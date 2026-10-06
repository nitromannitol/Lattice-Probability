#!/usr/bin/env python3
"""Tracked public-surface operational-attribution and workflow configuration gate.

Licensed source/publisher credit is retained. Every tracked regular file is
checked; checker signatures and test negatives are assembled at runtime.
This gate does not interpret or prove mathematical statements.
"""
from pathlib import Path
import re
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_axioms import regular_hash, tracked_paths
from assurance_diagnostics import GateError, success_summary

ROOT=Path(__file__).resolve().parent.parent
OPERATIONAL_NAMES=r"\b(?:f"+r"leet|Cl"+r"aude|Deep"+r"Seek|GL"+r"M|Open"+r"AI|So"+r"nnet|Op"+r"us|co"+r"dex)\b"
ATTRIBUTION=re.compile(r"Co-"+r"Authored-"+r"By:|AI (?:coding )?agents?|\b(?:models?|framework|hardware|prompting_notes):|"
                       r"~"+r"/(?:f"+r"leet|work|lean)/[^\s]+|/"+r"home/[^/\s]+/|(?:^|\n)automation:\s*|"+OPERATIONAL_NAMES,re.I)
ACTIONS={"actions/checkout":"3d3c42e5aac5ba805825da76410c181273ba90b1", "leanprover/lean-action":"38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9", "actions/cache/restore":"0057852bfaa89a56745cba8c7296529d2fc39830", "actions/cache/save":"0057852bfaa89a56745cba8c7296529d2fc39830", "actions/setup-go":"40f1582b2485089dde7abd97c1529aa768e1baff", "actions/upload-artifact":"043fb46d1a93c77aae656e7c1c64a875d1fc6a0a"}


def prose_findings(text):
    return [m.group(0) for m in ATTRIBUTION.finditer(text)]


def workflow_findings(text, comparator=False):
    issues=[]
    used=re.findall(r"^\s*uses:\s*([^\s#]+)",text,re.M)
    if not used: issues.append("no immutable workflow actions")
    for value in used:
        action,sep,revision=value.partition("@")
        if not sep or action not in ACTIONS or revision!=ACTIONS[action]: issues.append("unapproved/mutable action: "+value)
    # The checked workflows use simple scalar run fields. Reject missing actual
    # gate invocations even if a comment mentions the command.
    for mandatory,pattern in (("contents: read",r"^\s*contents: read\s*$"),
                              ("persist-credentials: false",r"^\s*persist-credentials: false\s*$"),
                              ("required preflight",r"^\s*run: python3 tools/verify.py --preflight-only\s*$"),
                              ("required production gate",r"^\s*run: python3 tools/verify.py (?![^\n]*--preflight-only)[^\n]*--evidence-dir [^\n]+$")):
        if not re.search(pattern,text,re.M): issues.append("missing configured workflow requirement: "+mandatory)
    for forbidden in ("restore-keys:","curl ","cargo +stable","toolchain install stable","continue-on-error: true"):
        if forbidden in text: issues.append("unsafe workflow configuration: "+forbidden)
    if comparator:
        for mandatory in ("--tools-only","--tool-root","--evidence-dir","--comparator", "go-version: '1.24.0'", "1.85.0"):
            if mandatory not in text: issues.append("missing comparator/tool verification: "+mandatory)
        if re.search(r"name: Verify[^\n]*\n\s*if:",text): issues.append("tool identity verification cannot be cache-miss-only")
    for line in text.splitlines():
        if re.match(r"^\s*key:",line):
            required=("runner.os","runner.arch","hashFiles", "lean-toolchain", "lake-manifest.json", "tools/**/*.py", ".github/workflows/")
            if "comparator-tools-v1-" not in line:
                required += ("lakefile.lean", "LatticeProb.lean", "LatticeProb/**/*.lean", "LatticeProbAudit/**/*.lean", "comparator.json", "README.md", "formalization.yaml")
            else:
                required += ("comparator.json", "COMPARATOR_REV", "LEAN4EXPORT_REV", "NANODA_REV", "LANDRUN_REV", "go1.24.0-rust1.85.0")
            if not all(part in line for part in required): issues.append("cache key lacks complete source/environment binding")
    for block in re.split(r"(?m)^\s*- name: ",text):
        if re.search(r"^\s*uses: actions/cache/save@",block,re.M) and not re.search(r"^\s*if: success\(\)",block,re.M):
            issues.append("artifact cache save lacks success condition")
    return issues


def check(root):
    findings=[]
    paths=tracked_paths(root)
    # New owned assurance files must be checked before they become tracked.
    paths=sorted(set(paths)|{"tools/verify.py","tools/check_public_hygiene.py","tools/check_comparators.py","tools/assurance_diagnostics.py"})
    for rel in paths:
        regular_hash(root,rel)
        p=root/rel
        try: text=p.read_text()
        except UnicodeDecodeError: continue
        for token in prose_findings(text): findings.append({"path":rel,"finding":token})
    for name in ("build","comparator"):
        rel=f".github/workflows/{name}.yml"
        for issue in workflow_findings((root/rel).read_text(),name=="comparator"):
            findings.append({"path":rel,"finding":issue})
    if findings: raise GateError("public surface: "+repr(findings))
    return paths


def main():
    try: paths=check(ROOT)
    except (GateError,OSError,ValueError) as error:
        print(f"check_public_hygiene: FAIL: {error}",file=sys.stderr);return 1
    print(success_summary("check_public_hygiene",len(paths),"tracked/configured surfaces; hygiene only"));return 0

if __name__=="__main__":sys.exit(main())
