#!/usr/bin/env python3
"""Build every production module, requiring actual exit zero and clean diagnostics."""
import argparse
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_axioms import source_inventory
from assurance_diagnostics import GateError, require_clean, run, success_summary

ROOT = Path(__file__).resolve().parent.parent

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--include-comparator",action="store_true")
    args=parser.parse_args()
    try:
        modules = [row["module"] for row in source_inventory(ROOT,include_comparator=args.include_comparator)]
        result = run(["lake","build",*modules],ROOT,lock=True)
        print(result.stdout,end="")
        print(result.stderr,end="",file=sys.stderr)
        require_clean(result)
    except (GateError,OSError,ValueError) as error:
        print(f"check_warnings: FAIL: {error}",file=sys.stderr);return 1
    print(success_summary("check_warnings",len(modules),"all production modules built; no warning/error diagnostics"));return 0

if __name__ == "__main__":
    sys.exit(main())
