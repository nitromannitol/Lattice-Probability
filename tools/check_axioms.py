#!/usr/bin/env python3
"""Axiom-closure gate for the library.

Every declaration the library exports is put through `#print axioms`.  A
declaration may stay in the library only if its closure is free of `sorryAx`
and of any axiom this library has not declared: the accepted set is Lean's own
`propext`, `Classical.choice` and `Quot.sound`, plus whatever the `External`
namespace states as an explicit hypothesis.

Usage: check_axioms.py
"""
import os, pathlib, re, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIB = ROOT / "LatticeProb"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|alias)\s+([A-Za-z_][A-Za-z_0-9.'!?]*)",
    re.M)


def strip_comments(text: str) -> str:
    """Blank out block comments, docstrings, line comments and string literals.

    Newlines are preserved so line-oriented scanning still lines up.  Without
    this, ordinary prose in a header comment that happens to begin a line with
    the word `theorem` is read as a declaration.
    """
    out = []
    i, n, depth, in_str = 0, len(text), 0, False
    while i < n:
        c = text[i]
        if depth == 0 and not in_str and text.startswith("/-", i):
            depth, i = 1, i + 2
            out.append("  ")
            continue
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if not in_str and text.startswith("--", i):
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if c == '"' and not in_str:
            in_str = True
            out.append(" ")
            i += 1
            continue
        if in_str:
            if c == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
                continue
            if c == '"':
                in_str = False
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


mods, names = [], []
for f in sorted(LIB.rglob("*.lean")):
    rel = f.relative_to(ROOT)
    mods.append(str(rel)[:-5].replace("/", "."))
    text = strip_comments(f.read_text(encoding="utf-8"))
    ns = None
    for line in text.splitlines():
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            ns = m.group(1)
        m = DECL.match(line)
        if m:
            nm = m.group(1)
            names.append(f"{ns}.{nm}" if ns and not nm.startswith(ns + ".") else nm)

names = sorted(set(names))
src = "".join(f"import {m}\n" for m in sorted(mods)) + \
      "".join(f"#print axioms {n}\n" for n in names)
(ROOT / "scratch").mkdir(exist_ok=True)
with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT / "scratch",
                                 delete=False) as fh:
    fh.write(src); tmp = fh.name
try:
    r = subprocess.run(["lake", "env", "lean", tmp], cwd=ROOT, capture_output=True,
                       text=True, timeout=3600,
                       env={**os.environ,
                            "PATH": os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]})
finally:
    os.unlink(tmp)

out = r.stdout
if "unknown" in out.lower() and "error" in out.lower():
    print(out[:4000]); sys.exit("check_axioms.py: the probe did not elaborate")

bad = []
for line in out.splitlines():
    line = line.strip()
    m = re.match(r"^'(.+?)' depends on axioms: \[(.*)\]$", line)
    if not m:
        continue
    used = {a.strip() for a in m.group(2).split(",") if a.strip()}
    extra = used - ALLOWED
    if extra:
        bad.append((m.group(1), sorted(extra)))

if bad:
    print("DECLARATIONS WITH AN UNACCEPTED AXIOM:")
    for n, e in bad:
        print(f"  {n}: {', '.join(e)}")
    sys.exit(1)
print(f"OK ({len(names)} declarations, axiom closure clean)")
