#!/usr/bin/env python3
"""Verify every declaration name mentioned in a prompt actually exists.

Writing a nonexistent lemma name into a prompt sends a whole fan-out chasing
it.  Names are elaborated by Lean before the prompt is allowed out.

Usage: check_names.py PROMPTFILE [extra-import, ...]
"""
import os, pathlib, re, subprocess, sys, tempfile
ROOT = pathlib.Path(os.environ.get("LEAN_ROOT") or pathlib.Path(__file__).resolve().parent.parent)
if len(sys.argv) < 2:
    print("OK (no prompt given, nothing to check)"); sys.exit(0)
prompt = pathlib.Path(sys.argv[1]).read_text()
imports = sys.argv[2:] or ["LatticeProb"]
names = sorted({m for m in re.findall(r"\bLatticeProb\.[A-Za-z_][A-Za-z_0-9.']*", prompt)}
               | {m for m in re.findall(
                   r"\b(?:Finset|Nat|Real|Sym2|Matrix|Function|MeasureTheory|"
                   r"ProbabilityTheory|Measure|Set|ENNReal)\.[A-Za-z_][A-Za-z_0-9.']*", prompt)})
if not names:
    print("OK (no declaration names to check)"); sys.exit(0)
src = "import Mathlib\n" + "".join(f"import {i}\n" for i in imports) + \
      "".join(f"#check @{n}\n" for n in names)
(ROOT / "scratch").mkdir(exist_ok=True)
with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT/"scratch", delete=False) as fh:
    fh.write(src); tmp = fh.name
try:
    r = subprocess.run(["lake", "env", "lean", tmp], cwd=ROOT, capture_output=True,
                       text=True, timeout=900,
                       env={**os.environ, "PATH": os.path.expanduser("~/.elan/bin")
                            + ":" + os.environ["PATH"]})
    bad = sorted(set(re.findall(r"[Uu]nknown (?:constant|identifier) `([^`]+)`", r.stdout)))
    if bad:
        print("PROMPT NAMES THAT DO NOT EXIST:"); [print("  " + b) for b in bad]
        sys.exit(1)
    print("OK (%d names checked, all exist)" % len(names))
finally:
    os.unlink(tmp)
