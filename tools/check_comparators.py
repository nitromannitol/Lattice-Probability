#!/usr/bin/env python3
"""Exact three-pair comparator configuration, tool identity and process gate."""
import argparse
import json
import os
from pathlib import Path
import re
import sys
import tempfile
sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_axioms import ALLOWED, digest, regular_hash, strict_json
from assurance_diagnostics import ANSI, GateError, Result, require_clean, run, success_summary

ROOT = Path(__file__).resolve().parent.parent
PAIRS = {"Kingman":"LatticeProbAudit.kingman", "GFF":"LatticeProbAudit.gff",
         "BinomialLocalCLT":"LatticeProbAudit.binomial_local_clt"}
REVISIONS = {"comparator":"575674928e239f5bc452aab72d1dd7b0f1326494",
             "lean4export":"4e7915201d3f9f04470d9eae002fa695f7cdc589",
             "nanoda_lib":"6ae1f0cd962f081f6c423454c5da729d841236a7",
             "landrun-src":"811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"}
BINARIES={"comparator":"comparator/.lake/build/bin/comparator",
          "lean4export":"lean4export/.lake/build/bin/lean4export",
          "nanoda_lib":"nanoda_lib/target/release/nanoda_bin", "landrun-src":"bin/landrun"}


def configuration(root):
    actual=sorted(p.parent.name for p in (root/"LatticeProbAudit").rglob("comparator.json"))
    if actual != sorted(PAIRS): raise GateError("missing/duplicate/unexpected comparator pair")
    rows=[]
    for pair,name in PAIRS.items():
        path=f"LatticeProbAudit/{pair}/comparator.json"
        value=strict_json((root/path).read_text())
        required={"challenge_module","solution_module","theorem_names","definition_names","permitted_axioms","enable_nanoda"}
        if not isinstance(value,dict) or set(value)!=required: raise GateError("malformed comparator configuration")
        expected_modules={"challenge_module":f"LatticeProbAudit.{pair}.Challenge", "solution_module":f"LatticeProbAudit.{pair}.Solution"}
        if any(value[k]!=v for k,v in expected_modules.items()) or value["theorem_names"] != [name] or value["definition_names"] != [] or value["enable_nanoda"] is not True:
            raise GateError("empty/duplicate/swapped comparator selection or module")
        axioms=value["permitted_axioms"]
        if not isinstance(axioms,list) or len(axioms)!=len(ALLOWED) or set(axioms)!=ALLOWED: raise GateError("changed comparator axiom policy")
        sources={m.replace(".","/")+".lean":regular_hash(root,m.replace(".","/")+".lean") for m in expected_modules.values()}
        rows.append({"pair":pair,"configuration":path,"sha256":regular_hash(root,path),"sources":sources,"selection":[name],"modules":expected_modules})
    return rows


def tool_identity(root, toolroot, execute=run):
    record={}
    for name,rev in REVISIONS.items():
        checkout=toolroot/name
        observed=require_clean(execute(["git","rev-parse","HEAD"],checkout)).stdout.strip()
        if observed!=rev: raise GateError(f"tool checkout identity mismatch: {name}")
        dirty=require_clean(execute(["git","status","--porcelain","--untracked-files=no"],checkout)).stdout
        if dirty.strip(): raise GateError(f"modified verification tool: {name}")
        binary=toolroot/BINARIES[name]
        if not binary.is_file() or binary.is_symlink() or not os.access(binary,os.X_OK): raise GateError(f"missing/nonexecutable comparator tool: {name}")
        record[name]={"revision":rev,"binary_sha256":regular_hash(toolroot,BINARIES[name])}
    if (toolroot/"lean4export/lean-toolchain").read_bytes()!=(root/"lean-toolchain").read_bytes(): raise GateError("lean4export toolchain differs from library")
    for command,version in [(["go","env","GOVERSION"],"go1.24.0"),(["rustc","--version"],"rustc 1.85.0")]:
        output=require_clean(execute(command,root)).stdout.strip()
        if (command[0]=="go" and output!=version) or (command[0]=="rustc" and not output.startswith(version+" ")): raise GateError("tool build environment mismatch")
    record["build_environment"]={"go":"go1.24.0","rust":"rustc 1.85.0",
        "project_toolchain_sha256":regular_hash(root,"lean-toolchain"),
        "policy":"library-assurance-v1", "platform":sys.platform,
        "architecture":__import__("platform").machine()}
    return record


def verify_tools(root,toolroot,execute=run):
    actual=tool_identity(root,toolroot,execute)
    stamp=toolroot/"build-provenance.json"
    if not stamp.is_file() or stamp.is_symlink(): raise GateError("missing exact successful tool-build provenance")
    expected=strict_json(stamp.read_text())
    if expected != actual: raise GateError("cached tool binary/source/environment/provenance mismatch")
    return actual


def accept_comparator(result, challenge_path):
    # Only the deliberately holed exact Challenge file may emit this exact warning.
    path=re.escape(challenge_path)
    permitted=re.compile(rf"^(?:{path}:\d+:\d+: warning:|warning: {path}:\d+:\d+:) declaration uses ['`]sorry['`]\s*$")
    stdout="\n".join(line for line in ANSI.sub("",result.stdout).splitlines() if not permitted.fullmatch(line))
    stderr="\n".join(line for line in ANSI.sub("",result.stderr).splitlines() if not permitted.fullmatch(line))
    require_clean(Result(result.command,result.returncode,stdout,stderr))
    if (ANSI.sub("",result.stdout)+"\n"+ANSI.sub("",result.stderr)).splitlines().count("Your solution is okay!")!=1:
        raise GateError("missing/duplicate comparator success verdict")


def compare(root, toolroot, evidence, execute=run):
    before=configuration(root)
    tools=verify_tools(root,toolroot,execute)
    evidence=evidence.resolve()
    if root.resolve()==evidence or root.resolve() in evidence.parents: raise GateError("comparator evidence must be external")
    evidence.mkdir(parents=True,exist_ok=True)
    results=[]
    os.environ.update({"COMPARATOR_LANDRUN":str(toolroot/BINARIES["landrun-src"]),"COMPARATOR_LEAN4EXPORT":str(toolroot/BINARIES["lean4export"]),"COMPARATOR_NANODA":str(toolroot/BINARIES["nanoda_lib"])})
    for row in before:
        build=execute(["lake","build",row["modules"]["solution_module"]],root,lock=True)
        require_clean(build)
        result=execute(["lake","env",str(toolroot/BINARIES["comparator"]),row["configuration"]],root,lock=True)
        (evidence/f"{row['pair']}.stdout").write_text(result.stdout)
        (evidence/f"{row['pair']}.stderr").write_text(result.stderr)
        process={"pair":row["pair"],"command":result.command,"exit":result.returncode,"selection":row["selection"]}
        (evidence/f"{row['pair']}.process.json").write_text(json.dumps(process,indent=2)+"\n")
        accept_comparator(result,row["modules"]["challenge_module"].replace(".","/")+".lean")
        if configuration(root)!=before or verify_tools(root,toolroot,execute)!=tools: raise GateError("comparator source/tool drift")
        results.append(process)
    if len(results)!=len(PAIRS): raise GateError("unexecuted required comparator pair")
    (evidence/"comparator-results.json").write_text(json.dumps({"configurations":before,"tools":tools,"results":results},indent=2)+"\n")
    print(success_summary("check_comparators",len(results),"exact comparator pairs; actual exits zero"))


def configured_tool_root(explicit, environ=None):
    if explicit is not None:
        return explicit
    value = (os.environ if environ is None else environ).get("COMPARATOR_TOOL_ROOT")
    if not value or not Path(value).is_absolute() or ".." in Path(value).parts:
        raise GateError("--tool-root or an explicit absolute COMPARATOR_TOOL_ROOT is required")
    return Path(value)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config-only",action="store_true")
    parser.add_argument("--tools-only",action="store_true")
    parser.add_argument("--record-tool-build",action="store_true")
    parser.add_argument("--tool-root",type=Path)
    parser.add_argument("--evidence-dir",type=Path)
    args=parser.parse_args()
    try:
        if args.config_only:
            rows=configuration(ROOT);print(f"OK (configuration only, {len(rows)} pairs, digest {digest(rows)}; no comparator verdict)")
        else:
            args.tool_root = configured_tool_root(args.tool_root)
            if args.record_tool_build:
                identity=tool_identity(ROOT,args.tool_root)
                (args.tool_root/"build-provenance.json").write_text(json.dumps(identity,indent=2)+"\n")
                print("RECORDED (tool build identity; no comparator verdict)")
            elif args.tools_only: verify_tools(ROOT,args.tool_root);print("OK (tool identity only; no comparator verdict)")
            elif args.evidence_dir: compare(ROOT,args.tool_root,args.evidence_dir)
            else:
                with tempfile.TemporaryDirectory(prefix="latticeprob-comparator-") as p: compare(ROOT,args.tool_root,Path(p))
    except (GateError,OSError,ValueError) as error:
        print(f"check_comparators: FAIL: {error}",file=sys.stderr);return 1
    return 0

if __name__=="__main__": sys.exit(main())
