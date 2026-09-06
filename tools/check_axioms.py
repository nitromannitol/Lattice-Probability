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
    r"(?:theorem|lemma|def|abbrev|instance|structure)\s+([A-Za-z_][A-Za-z_0-9.'!?]*)",
    re.M)

mods, names = [], []
for f in sorted(LIB.rglob("*.lean")):
    rel = f.relative_to(ROOT)
    mods.append(str(rel)[:-5].replace("/", "."))
    text = f.read_text(encoding="utf-8")
    ns = None
    for line in text.splitlines():
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            ns = m.group(1)
        m = DECL.match(line)
        if m and not line.lstrip().startswith("--"):
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
