#!/usr/bin/env python3
"""Build gate: the library must build with no errors and no warnings."""
import os, pathlib, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
r = subprocess.run(["flock", "/home/nitro/.lake-global.lock", "lake", "build"],
                   cwd=ROOT, capture_output=True, text=True, timeout=7200,
                   env={**os.environ,
                        "PATH": os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]})
out = r.stdout + r.stderr
bad = [l for l in out.splitlines()
       if "warning:" in l or "error:" in l or "sorry" in l]
if r.returncode != 0 or bad:
    print(out[-8000:]); sys.exit(1)
print("OK (build clean, no warnings)")
