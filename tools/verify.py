#!/usr/bin/env python3
"""Required library gates. Preflight has no kernel/comparator success claim."""
import argparse
from pathlib import Path
import sys
import tempfile
sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_axioms import audit, input_identity
from check_comparators import compare, configuration
from assurance_diagnostics import GateError, require_clean, run
from check_public_hygiene import check

ROOT=Path(__file__).resolve().parent.parent


def verify(root, evidence, *, preflight_only=False, comparator=None, execute=run):
    before=input_identity(root,include_comparator=comparator is not None)
    tests=sorted((root/"tools/tests").glob("test_*.py"))
    if not tests: raise GateError("missing required meaningful tests")
    require_clean(execute([sys.executable,"-m","unittest","discover","-s","tools/tests","-v"],root,timeout=180))
    check(root)
    configuration(root)
    if input_identity(root,include_comparator=comparator is not None)!=before: raise GateError("required-gate input drift")
    if preflight_only:
        print("OK (administration preflight only; no Lean/kernel/comparator verdict)");return
    require_clean(execute([sys.executable,"tools/check_warnings.py"]+(["--include-comparator"] if comparator is not None else []),root))
    audit(root,evidence/"axioms",execute=execute,include_comparator=comparator is not None)
    if comparator is not None: compare(root,comparator,evidence/"comparator",execute=execute)
    if input_identity(root,include_comparator=comparator is not None)!=before: raise GateError("required-gate input drift")
    print("OK (required production gates completed"+("; three comparator pairs" if comparator else "")+")")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preflight-only",action="store_true")
    parser.add_argument("--evidence-dir",type=Path)
    parser.add_argument("--comparator",type=Path,metavar="TOOL_ROOT")
    args=parser.parse_args()
    try:
        if args.preflight_only and args.comparator: raise GateError("comparator cannot be skipped by preflight-only")
        if args.evidence_dir: verify(ROOT,args.evidence_dir,preflight_only=args.preflight_only,comparator=args.comparator)
        else:
            with tempfile.TemporaryDirectory(prefix="latticeprob-verification-") as p: verify(ROOT,Path(p),preflight_only=args.preflight_only,comparator=args.comparator)
    except (GateError,OSError,ValueError) as error:
        print(f"verify: FAIL: {error}",file=sys.stderr);return 1
    return 0

if __name__=="__main__":sys.exit(main())
