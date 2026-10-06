#!/usr/bin/env python3
"""Two-pass, source-bound census and axiom closure of every production constant.

The generated inspection commands contain no mathematical declaration. Discovery
uses Lean's complete environment and exact defining-module provenance, including
private/generated constants; no source declaration regex selects the names.
Only subsets of propext, Classical.choice, Quot.sound are accepted. Explicit
hypotheses are binders and do not enlarge that axiom allowance.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))

from assurance_diagnostics import ANSI, GateError, POLICY, require_clean, run, success_summary

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
COMPARATOR_PAIRS = {
    'Kingman': 'LatticeProbAudit.kingman',
    'GFF': 'LatticeProbAudit.gff',
    'BinomialLocalCLT': 'LatticeProbAudit.binomial_local_clt',
    'BerryEsseen': 'LatticeProbAudit.berry_esseen_one_dim',
    'NormalComparison': 'LatticeProbAudit.normal_comparison',
}
CHALLENGE_SHA256 = {
    'Kingman': 'd1c5b13575bb018d604ad21b12879222da731e9367e7090565378ab2d185c5b0',
    'GFF': 'a779f0aebe647da8d4eb6d9da91cb2f48bf38d5f42a4d51b68f26ea7c942a890',
    'BinomialLocalCLT': '8250b241e51e507de7490a22fb3c53c73694be30535443dbf8a00f6abbce3a07',
    'BerryEsseen': '2fb6bbf3a699b545beeb612ce48a428e52177ff4b98d266c619b012dd6efafd3',
    'NormalComparison': 'dd9e99bce68d37a86155b2512cf7ab3104433556621fabef70d87c13678bef2e',
}
KINDS = {"definition", "theorem", "axiom", "opaque", "quotient", "inductive", "constructor", "recursor"}
CONFIG = ("lean-toolchain", "lakefile.lean", "lake-manifest.json")


def digest(value):
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, sort_keys=True,
                                    separators=(",", ":")).encode()).hexdigest()


def regular_hash(root, relative):
    if Path(relative).is_absolute() or ".." in Path(relative).parts:
        raise GateError("configured path escapes checkout")
    p = root / relative
    if not p.is_file() or p.is_symlink() or any(parent.is_symlink() for parent in p.parents if parent != root.parent):
        raise GateError(f"missing/nonregular configured file: {relative}")
    return hashlib.sha256(p.read_bytes()).hexdigest()


def strict_json(text):
    def unique(pairs):
        value={}
        for key,item in pairs:
            if key in value: raise GateError("duplicate JSON field: "+key)
            value[key]=item
        return value
    return json.loads(text,object_pairs_hook=unique)


def comparator_baselines(root):
    """Bind the complete intentional challenge sources and exact solution configurations."""
    rows=[]
    for pair,name in COMPARATOR_PAIRS.items():
        path=f"LatticeProbAudit/{pair}/comparator.json"
        value=strict_json((root/path).read_text())
        required={"challenge_module","solution_module","theorem_names","definition_names",
                  "permitted_axioms","enable_nanoda"}
        if not isinstance(value,dict) or set(value)!=required:
            raise GateError("malformed comparator configuration")
        modules={"challenge_module":f"LatticeProbAudit.{pair}.Challenge",
                 "solution_module":f"LatticeProbAudit.{pair}.Solution"}
        if any(value[k]!=v for k,v in modules.items()) or value["theorem_names"] != [name] or value["definition_names"] != [] or value["enable_nanoda"] is not True:
            raise GateError("empty/duplicate/swapped comparator selection or module")
        axioms=value["permitted_axioms"]
        if not isinstance(axioms,list) or len(axioms)!=len(ALLOWED) or set(axioms)!=ALLOWED:
            raise GateError("changed comparator axiom policy")
        sources={m.replace(".","/")+".lean":regular_hash(root,m.replace(".","/")+".lean")
                 for m in modules.values()}
        challenge=modules["challenge_module"].replace(".","/")+".lean"
        if sources[challenge]!=CHALLENGE_SHA256[pair]:
            raise GateError("modified exact comparator Challenge baseline: "+pair)
        rows.append({"pair":pair,"configuration":path,"sha256":regular_hash(root,path),
                     "sources":sources,"selection":[name],"modules":modules})
    return rows


def tracked_paths(root, runner=subprocess.run):
    r = run(["git", "ls-files", "-z"], root, runner=runner)
    require_clean(r)
    paths = r.stdout.split("\0")
    if paths[-1] != "" or not paths[:-1] or len(paths[:-1]) != len(set(paths[:-1])):
        raise GateError("empty/malformed/duplicate tracked-file inventory")
    return paths[:-1]


def source_inventory(root, paths=None, *, include_comparator=False):
    paths = tracked_paths(root) if paths is None else paths
    if len(paths) != len(set(paths)):
        raise GateError("duplicate source path")
    selected = sorted(p for p in paths if p == "LatticeProb.lean" or
                      (p.startswith("LatticeProb/") and p.endswith(".lean")))
    if "LatticeProb.lean" not in selected or len(selected) < 2:
        raise GateError("missing production root or empty production modules")
    # Untracked production input could otherwise be built without being bound.
    actual = {"LatticeProb.lean"} | {p.relative_to(root).as_posix()
                for p in (root / "LatticeProb").rglob("*.lean")}
    if actual != set(selected):
        raise GateError("tracked/physical production module inventory differs")
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:/[A-Za-z_][A-Za-z_0-9]*)*\.lean",p) for p in selected):
        raise GateError("unsupported production module path; require an explicit safe module encoding")
    if include_comparator:
        comparator_baselines(root)  # Only exact complete configured baselines are separate.
        challenges={f"LatticeProbAudit/{p}/Challenge.lean" for p in COMPARATOR_PAIRS}
        audit_paths={p for p in paths if p.startswith("LatticeProbAudit/") and p.endswith(".lean")}
        physical={p.relative_to(root).as_posix() for p in (root/"LatticeProbAudit").rglob("*.lean")}
        if audit_paths != physical or not challenges <= audit_paths:
            raise GateError("missing/untracked comparator surface")
        audit_selected=sorted(audit_paths-challenges)
        if not audit_selected or not all(f"LatticeProbAudit/{p}/Solution.lean" in audit_selected for p in COMPARATOR_PAIRS):
            raise GateError("missing configured comparator Solution scope")
        selected += audit_selected
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:/[A-Za-z_][A-Za-z_0-9]*)*\.lean",p) for p in selected):
        raise GateError("unsupported comparator module path")
    rows = [{"path":p, "module":p[:-5].replace("/", "."),
             "sha256":regular_hash(root, p)} for p in selected]
    if len({r["module"] for r in rows}) != len(rows):
        raise GateError("duplicate defining module")
    return rows


def input_identity(root, paths=None, *, include_comparator=False):
    source = source_inventory(root, paths,include_comparator=include_comparator)
    configured=list(CONFIG)+[f"LatticeProbAudit/{p}/comparator.json" for p in COMPARATOR_PAIRS]
    configurations = {p: regular_hash(root, p) for p in configured}
    manifest = strict_json((root / "lake-manifest.json").read_text())
    packages = manifest.get("packages")
    if not isinstance(packages, list) or not packages:
        raise GateError("empty configured dependencies")
    revisions = []
    for p in packages:
        if not isinstance(p, dict) or not isinstance(p.get("name"), str) or not re.fullmatch(r"[0-9a-f]{40}", p.get("rev", "")):
            raise GateError("dependency must have an exact resolved revision")
        revisions.append({"name":p["name"], "rev":p["rev"], "url":p.get("url")})
    if len({p["name"] for p in revisions}) != len(revisions):
        raise GateError("duplicate dependency identity")
    tools = sorted(p.relative_to(root).as_posix() for p in (root / "tools").rglob("*.py"))
    required = {"tools/check_axioms.py", "tools/assurance_diagnostics.py", "tools/check_warnings.py",
                "tools/check_public_hygiene.py", "tools/check_comparators.py", "tools/verify.py"}
    if not required <= set(tools) or not any(p.startswith("tools/tests/test_") for p in tools):
        raise GateError("missing configured checker or meaningful tests")
    head = require_clean(run(["git", "rev-parse", "HEAD"], root)).stdout.strip()
    if not re.fullmatch(r"[0-9a-f]{40}", head):
        raise GateError("invalid checkout identity")
    return {"policy":POLICY, "base_commit":head, "sources":source,
            "comparator_baselines":comparator_baselines(root),
            "configurations":configurations, "dependencies":sorted(revisions,key=lambda p:p["name"]),
            "assurance_files":{p:regular_hash(root,p) for p in tools +
             ["README.md", "formalization.yaml", ".github/workflows/build.yml", ".github/workflows/comparator.yml"]}}


def inspection_program(sources, phase, identity):
    if phase not in {"census", "closure"} or not sources:
        raise GateError("invalid inspection phase/selection")
    modules = [r["module"] for r in sources]
    if len(modules) != len(set(modules)) or "LatticeProb" not in modules:
        raise GateError("invalid module selection")
    # JSON string literals are also Lean string literals for the module paths here.
    quoted = ", ".join(json.dumps(m, ensure_ascii=False) for m in modules)
    # A non-module inspector loads the full private import environment in Lean
    # 4.32, including legacy and module-system sources. It retains every kernel
    # declaration; `import all` is forbidden without a `module` header.
    imports = "import Lean\n" + "".join(f"import {m}\n" for m in modules)
    body = r'''open Lean Elab Command
run_cmd liftCoreM do
  let env ← getEnv
  let selected : List String := [MODULES]
  for m in selected do
    IO.println ("LIB-MODULE " ++ (Json.str m).compress)
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | throwError "invalid module index"
    if !selected.contains m.toString then continue
    let kind := match ci with
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let row := Json.mkObj [("name", Json.str n.toString), ("module", Json.str m.toString),
      ("kind", Json.str kind), ("exported", Json.bool ((env.setExporting true).find? n).isSome)]
    IO.println ("LIB-CENSUS " ++ row.compress)
CLOSURE
    count := count + 1
  if count == 0 then throwError "empty production constant census"
  IO.println ("LIB-END " ++ (Json.mkObj [("phase", Json.str "PHASE"),
    ("identity", Json.str "IDENTITY"), ("count", toJson count),
    ("module_count", toJson selected.length)]).compress)
'''
    closure = '''    let axioms ← collectAxioms n
    IO.println ("LIB-AXIOMS " ++ (Json.mkObj [("name", Json.str n.toString),
      ("axioms", toJson (axioms.map (·.toString)))]).compress)'''
    return imports + body.replace("MODULES", quoted).replace("CLOSURE", closure if phase == "closure" else "").replace("PHASE", phase).replace("IDENTITY", identity)


def parse_inspection(result, sources, phase, identity):
    require_clean(result)
    modules, declarations, axioms, endings = [], [], [], []
    combined=ANSI.sub("",result.stdout)+"\n"+ANSI.sub("",result.stderr)
    if parse_print_axioms(combined): raise GateError("mixed/unattributed textual and structured axiom reports")
    for line in combined.splitlines():
        if not line.startswith("LIB-"):
            continue
        try:
            tag, payload = line.split(" ", 1)
            value = strict_json(payload)
        except (ValueError, json.JSONDecodeError) as error:
            raise GateError("malformed inspection row") from error
        if tag == "LIB-MODULE": modules.append(value)
        elif tag == "LIB-CENSUS": declarations.append(value)
        elif tag == "LIB-AXIOMS": axioms.append(value)
        elif tag == "LIB-END": endings.append(value)
        else: raise GateError("unexpected inspection record")
    expected_modules = [r["module"] for r in sources]
    if not all(isinstance(m,str) for m in modules) or len(modules) != len(expected_modules) or set(modules) != set(expected_modules):
        raise GateError("missing/duplicate/unexpected imported module report")
    if len(endings) != 1 or not isinstance(endings[0],dict) or type(endings[0].get("count")) is not int or type(endings[0].get("module_count")) is not int or endings[0] != {"phase":phase,"identity":identity,
             "count":len(declarations),"module_count":len(expected_modules)}:
        raise GateError("missing/duplicate/stale/truncated inspection terminator")
    if not declarations:
        raise GateError("empty declaration census")
    by_module = {r["module"]:r for r in sources}
    names = []
    bound = []
    for row in declarations:
        if not isinstance(row, dict) or set(row) != {"name","module","kind","exported"}:
            raise GateError("malformed census declaration")
        if not isinstance(row["name"], str) or not row["name"] or any(c in row["name"] for c in "\r\n\0") or not isinstance(row["module"],str) or row["module"] not in by_module or not isinstance(row["kind"],str) or row["kind"] not in KINDS or type(row["exported"]) is not bool:
            raise GateError("invalid declaration name/kind/module/visibility")
        names.append(row["name"])
        src = by_module[row["module"]]
        bound.append({**row,"path":src["path"],"source_sha256":src["sha256"]})
    if len(names) != len(set(names)):
        raise GateError("duplicate declaration identity")
    if phase == "census" and axioms:
        raise GateError("unexpected closure rows in census")
    if phase == "closure":
        accept_axiom_rows(names, axioms)
    return sorted(bound,key=lambda r:r["name"]), axioms


def accept_axiom_rows(expected, rows):
    if not expected or not all(isinstance(n,str) and n for n in expected) or len(expected) != len(set(expected)):
        raise GateError("empty/duplicate expected declaration selection")
    reported = []
    for row in rows:
        if not isinstance(row,dict) or set(row) != {"name","axioms"} or not isinstance(row["name"],str) or not isinstance(row["axioms"],list) or not all(isinstance(a,str) and a for a in row["axioms"]):
            raise GateError("malformed axiom report")
        reported.append(row["name"])
        if len(row["axioms"]) != len(set(row["axioms"])) or set(row["axioms"]) - ALLOWED:
            raise GateError(f"unaccepted/duplicate axioms: {row['name']}: {row['axioms']}")
    if len(reported) != len(expected) or set(reported) != set(expected) or len(reported) != len(set(reported)):
        raise GateError("missing/duplicate/unexpected axiom report names")
    return rows


def parse_print_axioms(output):
    """Strict optional textual #print-axioms adapter; duplicates remain visible."""
    pattern = re.compile(r"^'(.+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))\s*$",re.M)
    rows = []
    spans = []
    for m in pattern.finditer(output):
        values = [] if m.group(3) else [a.strip() for a in m.group(2).split(",")]
        if values == [""]: values = []
        rows.append({"name":m.group(1),"axioms":values});spans.append(m.span())
    remainder = output
    for start,end in reversed(spans): remainder = remainder[:start] + remainder[end:]
    if re.search(r"depends on axioms|does not depend on any axioms",remainder):
        raise GateError("malformed/unattributable textual axiom row")
    return rows


def accept_print_axioms(result,expected):
    require_clean(result)
    combined=ANSI.sub("",result.stdout)+"\n"+ANSI.sub("",result.stderr)
    return accept_axiom_rows(expected,parse_print_axioms(combined))


def audit(root, evidence, *, execute=run, prepare_only=False, include_comparator=False):
    evidence = evidence.resolve()
    if evidence == root.resolve() or root.resolve() in evidence.parents:
        raise GateError("inspection evidence must be outside the repository")
    evidence.mkdir(parents=True, exist_ok=True)
    before = input_identity(root,include_comparator=include_comparator)
    identity = digest(before)
    (evidence / "input-before.json").write_text(json.dumps(before,indent=2,ensure_ascii=False)+"\n")
    results = []
    for phase in ("census","closure"):
        program = evidence / f"{phase}.lean"
        program.write_text(inspection_program(before["sources"],phase,identity))
        if prepare_only: continue
        result = execute(["lake","env","lean",str(program)],root,timeout=7200,lock=True)
        (evidence/f"{phase}.stdout").write_text(result.stdout)
        (evidence/f"{phase}.stderr").write_text(result.stderr)
        (evidence/f"{phase}.process.json").write_text(json.dumps({"command":result.command,"exit":result.returncode},indent=2)+"\n")
        if input_identity(root,include_comparator=include_comparator) != before: raise GateError("source/config/checker drift during probe")
        results.append(parse_inspection(result,before["sources"],phase,identity))
    if input_identity(root,include_comparator=include_comparator) != before: raise GateError("source/config/checker drift")
    if prepare_only:
        print("PREPARED ONLY: no Lean census or axiom verdict")
        return None
    if results[0][0] != results[1][0]: raise GateError("environment census changed between passes")
    names = [r["name"] for r in results[0][0]]
    (evidence/"expected-names.txt").write_text("\n".join(names)+"\n")
    record={"policy":POLICY,"input_identity":identity,"sources":before["sources"],
            "declarations":results[0][0],"expected_names":names,"expected_names_sha256":digest(names),
            "axioms":results[1][1],"coverage":"all kernel-environment constants in every selected defining module",
            "before_after_identity_equal":True,"actual_probe_exits":[0,0],"verdict":"OK"}
    (evidence/"public-census.json").write_text(json.dumps(record,indent=2,ensure_ascii=False)+"\n")
    print(success_summary("check_axioms",len(names),"uniquely bound declarations; exact axiom closure"))
    return record


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-dir",type=Path)
    parser.add_argument("--prepare-only",action="store_true")
    parser.add_argument("--include-comparator",action="store_true")
    args=parser.parse_args()
    try:
        if args.evidence_dir:
            audit(ROOT,args.evidence_dir,prepare_only=args.prepare_only,include_comparator=args.include_comparator)
        else:
            with tempfile.TemporaryDirectory(prefix="latticeprob-axioms-") as path:
                audit(ROOT,Path(path),prepare_only=args.prepare_only,include_comparator=args.include_comparator)
    except (GateError,OSError,ValueError) as error:
        print(f"check_axioms: FAIL: {error}",file=sys.stderr);return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
