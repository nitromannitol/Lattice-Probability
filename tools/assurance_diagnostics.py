#!/usr/bin/env python3
"""Fail-closed process and Lean/Lake diagnostic boundaries."""
import os
import re
import subprocess
import stat
from pathlib import Path
from dataclasses import dataclass

POLICY = "library-assurance-v1"
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
SEVERITY = re.compile(r"^(?:(?:[⚠ℹ✔]\s*|\[[^\]]+\]\s*)*)"
                      r"(?:(?:[^\n]+):\d+(?::\d+)?:\s*)?(?:warning|error):", re.I)
TERMINAL = re.compile(
    r"^(?:[✖×]\s*|(?:FAIL|FAILED|FAILURE)(?:\s|[(:.]|$)|"
    r"[^\n]*:\s*(?:FAIL|FAILED|FAILURE)(?:\s|[(:.]|$)|"
    r"(?:build|compilation|test(?:s)?|check(?:s)?)(?:\s+[^\n]*?)?\s+failed(?:[.!:]|$)|"
    r"Some required builds logged failures:|error(?:\s*:\s*|\s+)(?:build|Lean|Lake))", re.I)

class GateError(RuntimeError):
    pass

@dataclass(frozen=True)
class Result:
    command: tuple
    returncode: int
    stdout: str
    stderr: str


def diagnostic_lines(output):
    """Severity and terminal records, not arbitrary words in informational prose."""
    bad = []
    for raw in ANSI.sub("", output).splitlines():
        line = raw.strip()
        # Cached Lake output can prefix a severity with a path/job label.
        if SEVERITY.search(line) or TERMINAL.search(line):
            bad.append(line)
        elif re.match(r"^declaration uses ['`]sorry['`]", line, re.I):
            bad.append(line)
    return bad


def require_clean(result, *, warnings=True):
    if result.returncode != 0:
        raise GateError(f"child exit {result.returncode}: {list(result.command)}")
    bad = diagnostic_lines(result.stdout + "\n" + result.stderr)
    if not warnings:
        bad = [line for line in bad if not SEVERITY.match(line) or "error:" in line.lower()]
    if bad:
        raise GateError("diagnostics: " + " | ".join(bad[:10]))
    return result


def lock_identity(value, *, must_exist):
    """Validate the explicit runtime path; no hardcoded working-environment path."""
    if not isinstance(value, str) or not value or not Path(value).is_absolute() or ".." in Path(value).parts:
        raise GateError("expected lock path must be explicitly configured and absolute")
    path = Path(value)
    if path.is_symlink() or any(parent.is_symlink() for parent in path.parents):
        raise GateError("expected lock path cannot be a symlink")
    try:
        info = path.stat()
    except FileNotFoundError:
        if must_exist or not path.parent.is_dir():
            raise GateError("expected inherited lock file is absent")
        return {"path":str(path), "device":None, "inode":None}
    if not stat.S_ISREG(info.st_mode):
        raise GateError("expected lock path is not a regular file")
    return {"path":str(path), "device":info.st_dev, "inode":info.st_ino}


def process_identity(proc_root, pid):
    try:
        text = (proc_root / str(pid) / "stat").read_text()
    except OSError as error:
        raise GateError("cannot inspect live lock ancestry") from error
    end = text.rfind(")")
    if end < 0 or not text.startswith(str(pid) + " ("):
        raise GateError("malformed lock ancestry identity")
    fields = text[end + 1:].split()
    if len(fields) < 20 or fields[0] not in {"R", "S", "D", "T", "t", "I", "W", "K", "P"}:
        raise GateError("lock ancestor is absent or not live")
    try:
        parent, birth = int(fields[1]), int(fields[19])
    except ValueError as error:
        raise GateError("malformed lock ancestor lifetime") from error
    if parent < 0 or birth < 0:
        raise GateError("invalid lock ancestor lifetime")
    return {"pid":pid, "parent":parent, "birth":birth}


def kernel_lock_owner(proc_root, expected):
    try:
        text = (proc_root / "locks").read_text()
    except OSError as error:
        raise GateError("cannot read Linux kernel lock records") from error
    if text and not text.endswith("\n"):
        raise GateError("partial Linux kernel lock records")
    owners = []
    for line in text.splitlines():
        fields = line.split()
        waiting = len(fields) > 1 and fields[1] == "->"
        if waiting:
            fields = [fields[0], *fields[2:]]
        if len(fields) != 8 or not re.fullmatch(r"[0-9]+:",fields[0]):
            raise GateError("malformed Linux kernel lock record")
        identity = fields[5].split(":")
        if len(identity) != 3:
            raise GateError("malformed kernel lock device/inode")
        try:
            major, minor, inode = int(identity[0],16), int(identity[1],16), int(identity[2])
        except ValueError as error:
            raise GateError("malformed kernel lock device/inode") from error
        if waiting:
            continue  # A queued waiter owns no current exclusive lock.
        if (major,minor,inode) != (os.major(expected["device"]),os.minor(expected["device"]),expected["inode"]):
            continue
        if fields[1:4] != ["FLOCK","ADVISORY","WRITE"] or fields[6:] != ["0","EOF"]:
            raise GateError("expected file lacks a full exclusive kernel flock")
        try:
            owner = int(fields[4])
        except ValueError as error:
            raise GateError("malformed kernel lock owner") from error
        if owner <= 0:
            raise GateError("kernel lock has no attributable live owner")
        owners.append(owner)
    if len(owners) != 1:
        raise GateError("missing or duplicate expected exclusive kernel lock")
    return owners[0]


def verify_inherited_lock(value, *, proc_root=Path("/proc"), self_pid=None):
    """Require the exact configured inode's live ancestor/self kernel lock.

    Alternate proc roots/PIDs are pure-fixture parameters only; runtime calls
    always use Linux /proc and the actual current PID, never an environment flag.
    """
    expected = lock_identity(value, must_exist=True)
    owner = kernel_lock_owner(proc_root, expected)
    pid = os.getpid() if self_pid is None else self_pid
    ancestry, seen = [], set()
    for _ in range(512):
        if type(pid) is not int or pid <= 0 or pid in seen:
            raise GateError("kernel lock holder is not a live ancestor or self")
        seen.add(pid)
        row = process_identity(proc_root,pid)
        ancestry.append(row)
        if pid == owner:
            break
        pid = row["parent"]
    else:
        raise GateError("lock ancestry is unbounded")
    if kernel_lock_owner(proc_root,expected) != owner:
        raise GateError("kernel lock ownership changed during inspection")
    if any(process_identity(proc_root,row["pid"]) != row for row in ancestry):
        raise GateError("lock ancestor lifetime or parent changed")
    if lock_identity(value,must_exist=True) != expected:
        raise GateError("expected lock device/inode changed during inspection")
    return {**expected, "owner":owner, "ancestry":ancestry}


def success_summary(gate, count, detail):
    if not re.fullmatch(r"[a-z][a-z_]*",gate) or type(count) is not int or count <= 0 or not detail or "\n" in detail:
        raise GateError("success requires an exact positive inspected count")
    return f"{gate}: OK ({count} item(s) inspected)\nOK ({count} items; {detail})"


def run(command, root, *, timeout=7200, runner=subprocess.run, lock=False):
    argv = list(command)
    inherited = None
    if lock:
        outer = os.environ.get("LAKE_GATE_LOCK")
        direct = os.environ.get("LAKE_LOCK")
        if outer:
            inherited = verify_inherited_lock(outer)
            if direct and lock_identity(direct,must_exist=True) != {k:inherited[k] for k in ("path","device","inode")}:
                raise GateError("direct and inherited expected lock configurations disagree")
        elif direct:
            lock_identity(direct,must_exist=False)
            argv = ["/usr/bin/flock", direct, *argv]
        else:
            raise GateError("LAKE_LOCK or verified LAKE_GATE_LOCK is required for Lean/Lake processes")
    try:
        child = runner(argv, cwd=root, capture_output=True, text=True, timeout=timeout)
    except (OSError, subprocess.SubprocessError) as error:
        raise GateError(f"child could not finish: {error}") from error
    if inherited is not None and verify_inherited_lock(outer) != inherited:
        raise GateError("inherited kernel lock/lifetime changed during child execution")
    return Result(tuple(argv), child.returncode, child.stdout, child.stderr)
