"""Mutation controls for the actual checker functions; all Lean children mocked."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import check_axioms as ax
import check_comparators as cmp
import assurance_diagnostics as diag
import check_public_hygiene as hygiene
import verify


def result(stdout="",rc=0,stderr=""):
    return diag.Result(("mock-child",),rc,stdout,stderr)

SOURCES=[{"path":"LatticeProb.lean","module":"LatticeProb","sha256":"a"*64},
         {"path":"LatticeProb/Fixture.lean","module":"LatticeProb.Fixture","sha256":"b"*64}]
NAMES=["Outer.«quoted name»", "ᾱ.lemma'", "_private.LatticeProb.Fixture.0.hidden", "Generated.mk", "Generated.rec", "Generated.instType"]
DECLS=[{"name":n,"module":"LatticeProb.Fixture","kind":k,"exported":not n.startswith("_private")} for n,k in zip(NAMES,["theorem","opaque","theorem","constructor","recursor","definition"])]


def inspection(phase="census",declarations=None,axioms=None,modules=None,identity="identity"):
    ds=copy.deepcopy(DECLS if declarations is None else declarations)
    ms=[s["module"] for s in SOURCES] if modules is None else modules
    lines=["LIB-MODULE "+json.dumps(m) for m in ms]
    for row in ds:
        lines.append("LIB-CENSUS "+json.dumps(row,ensure_ascii=False))
        if phase=="closure":
            values=[] if axioms is None else axioms
            lines.append("LIB-AXIOMS "+json.dumps({"name":row["name"],"axioms":values},ensure_ascii=False))
    lines.append("LIB-END "+json.dumps({"phase":phase,"identity":identity,"count":len(ds),"module_count":len(ms)}))
    return "\n".join(lines)


class ReportTests(unittest.TestCase):
    def test_standard_subsets_and_genuine_empty(self):
        for allowed in [[],["propext"],["Classical.choice"],["Quot.sound"],sorted(ax.ALLOWED)]:
            with self.subTest(axioms=allowed):
                self.assertEqual(ax.accept_axiom_rows([NAMES[0]],[{"name":NAMES[0],"axioms":allowed}])[0]["axioms"],allowed)

    def test_all_four_old_false_acceptances_rejected(self):
        good="'A.f' depends on axioms: [propext]\n'B.g' does not depend on any axioms\n"
        cases=[("nonzero",good,42),("missing",good.splitlines()[0]+"\n",0),("empty","",0),("duplicate",good+good.splitlines()[0]+"\n",0)]
        for name,out,rc in cases:
            with self.subTest(case=name),self.assertRaises(diag.GateError):
                diag.require_clean(result(out,rc));ax.accept_axiom_rows(["A.f","B.g"],ax.parse_print_axioms(out))

    def test_report_mutations(self):
        rows=[{"name":"A.f","axioms":[]}]
        cases=[([],rows),(["A.f","A.f"],rows),(["A.f"],[]),(["A.f"],rows*2),(["A.f"],[{"name":"B.f","axioms":[]}]),
               (["A.f"],[{}]),(["A.f"],[{"name":"A.f","axioms":"propext"}]),(["A.f"],[{"name":"A.f","axioms":["propext","propext"]}])]
        for expected,reported in cases:
            with self.subTest(expected=expected,rows=reported),self.assertRaises(diag.GateError):ax.accept_axiom_rows(expected,reported)

    def test_custom_qualified_placeholder_axioms_rejected(self):
        for bad in ["sorryAx","Custom.ax","Namespace.sorryAx","Lean.ofReduceBool","Native.trust", ""]:
            with self.subTest(axiom=bad),self.assertRaises(diag.GateError):ax.accept_axiom_rows(["A.f"],[{"name":"A.f","axioms":[bad]}])

    def test_wrapped_quoted_unicode_text_rows(self):
        output="'ᾱ.«quoted name».f\'' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n'Empty' does not depend on any axioms\n"
        rows=ax.parse_print_axioms(output)
        self.assertEqual(rows[0]["name"],"ᾱ.«quoted name».f'")
        ax.accept_axiom_rows([rows[0]["name"],"Empty"],rows)

    def test_malformed_text_and_mixed_duplicates(self):
        for text in ["'A.f' depends on axioms: [propext", "A.f depends on axioms: []", "'A.f' depends on axioms: [propext,,]", "'A.f' depends on axioms: []\n'A.f' does not depend on any axioms"]:
            with self.subTest(text=text),self.assertRaises(diag.GateError):ax.accept_axiom_rows(["A.f"],ax.parse_print_axioms(text))

    def test_complete_environment_provenance_and_zero_module(self):
        census,_=ax.parse_inspection(result(inspection()),SOURCES,"census","identity")
        closed,rows=ax.parse_inspection(result(inspection("closure")),SOURCES,"closure","identity")
        self.assertEqual(census,closed);self.assertEqual(len(rows),len(NAMES))
        self.assertEqual({r["name"] for r in census},set(NAMES));self.assertTrue(all(r["source_sha256"]=="b"*64 for r in census))

    def test_census_metadata_mutations(self):
        for key,value in [("name",""),("name","A\nB"),("module","Other.Module"),("kind","unsupported"),("exported","true")]:
            ds=copy.deepcopy(DECLS);ds[0][key]=value
            with self.subTest(key=key,value=value),self.assertRaises(diag.GateError):ax.parse_inspection(result(inspection(declarations=ds)),SOURCES,"census","identity")
        for ds in [[],DECLS+[DECLS[0]]]:
            with self.subTest(declarations=ds),self.assertRaises(diag.GateError):ax.parse_inspection(result(inspection(declarations=ds)),SOURCES,"census","identity")

    def test_missing_duplicate_stale_or_malformed_census(self):
        original=inspection()
        cases=[original.rsplit("\n",1)[0],original+"\n"+original.splitlines()[-1],original.replace('"identity"','"stale"'),original+"\nLIB-UNKNOWN {}",original+"\nLIB-CENSUS broken",inspection(modules=["LatticeProb"]),inspection(modules=["LatticeProb","LatticeProb"])]
        for text in cases:
            with self.subTest(text=text),self.assertRaises(diag.GateError):ax.parse_inspection(result(text),SOURCES,"census","identity")

    def test_failed_census_process_and_error_stderr(self):
        for rc,stderr in [(42,""),(-9,""),(0,"file.lean:7:2: error: failed elaboration")]:
            with self.subTest(rc=rc,stderr=stderr),self.assertRaises(diag.GateError):ax.parse_inspection(result(inspection(),rc,stderr),SOURCES,"census","identity")

    def test_complete_expected_binding_probe_generation(self):
        p=ax.inspection_program(SOURCES,"closure","a"*64)
        self.assertTrue(p.startswith("import Lean\n"))
        self.assertNotRegex(p, r"(?m)^module\s*$|^import all ")
        for module in SOURCES:self.assertIn("import "+module["module"]+"\n",p)
        self.assertIn("env.constants.toList",p);self.assertIn("env.getModuleIdxFor? n",p);self.assertIn("collectAxioms n",p)
        self.assertNotIn("n.isInternal",p);self.assertNotIn("isPrivateName",p)
        self.assertNotRegex(p,r"(?m)^\s*(?:theorem|example|def|axiom)\b")
        for source,phase in [([],"census"),(SOURCES+SOURCES,"closure"),(SOURCES,"unknown")]:
            with self.subTest(phase=phase),self.assertRaises(diag.GateError):ax.inspection_program(source,phase,"id")


class ProcessTests(unittest.TestCase):
    def test_actual_nonzero_and_signal_child_exits(self):
        for command,rc in [([sys.executable,"-c","print('complete standard rows');raise SystemExit(42)"],42),([sys.executable,"-c","import os,signal;os.kill(os.getpid(),signal.SIGTERM)"],-15)]:
            with self.subTest(command=command):
                r=diag.run(command,Path.cwd());self.assertEqual(r.returncode,rc)
                with self.assertRaises(diag.GateError):diag.require_clean(r)

    def test_timeout_missing_child_and_lock(self):
        for error in [FileNotFoundError("missing"),subprocess.TimeoutExpired("child",1),OSError("exec")]:
            def runner(*args,**kwargs):raise error
            with self.subTest(error=type(error).__name__),self.assertRaises(diag.GateError):diag.run(["mock"],Path.cwd(),runner=runner)
        with patch.dict(os.environ,{},clear=True),self.assertRaises(diag.GateError):diag.run(["lake","build"],Path.cwd(),lock=True)

    def test_exact_actual_mocked_command_exit_and_stdout_stderr(self):
        called=[]
        def runner(command,**kwargs):called.append((command,kwargs));return subprocess.CompletedProcess(command,-9,"complete","failure")
        with tempfile.TemporaryDirectory() as d,patch.dict(os.environ,{"LAKE_LOCK":str(Path(d)/"fixture-lock")},clear=True):
            r=diag.run(["lake","env","lean","external.lean"],Path.cwd(),lock=True,runner=runner,timeout=17)
            expected_lock=str(Path(d)/"fixture-lock")
        self.assertEqual(called[0][0],["/usr/bin/flock",expected_lock,"lake","env","lean","external.lean"]);self.assertEqual(called[0][1]["timeout"],17)
        self.assertEqual(r.returncode,-9);self.assertEqual(r.stderr,"failure")
        with self.assertRaises(diag.GateError):diag.require_clean(r)

    def test_informational_cached_ring_and_prose_are_valid(self):
        for text in ["info: File.lean:598:4: Try this:\nThe `ring` tactic failed to close the goal. Use `ring_nf`.\nBuild completed successfully (9 jobs).", "info: a proof may discuss sorry in prose", "info: 'error' is a quoted word", "info: mathematical error: bound", "info: warning: is a quoted diagnostic label", "Your solution is okay!\n"]:
            with self.subTest(text=text):diag.require_clean(result(text))

    def test_precise_severity_and_terminal_mutations(self):
        cases=["warning: declaration uses 'sorry'", "File.lean:3:2: warning: declaration uses 'sorry'", "info: cached:\nFile.lean:3:2: error: elaboration failed", "\x1b[31merror:\x1b[0m failure", "✖ [2/3] Building X", "FAILED", "gate: FAIL", "Build failed.", "Some required builds logged failures:\nX", "error: Lean exited with code 1", "Your solution is okay!\npair: FAILED", "Build completed successfully\nerror: Lake build failed", "File.lean:2:3:warning: missing space", "FAILED (failures=1)"]
        for text in cases:
            with self.subTest(text=text),self.assertRaises(diag.GateError):diag.require_clean(result(text))


class InventoryTests(unittest.TestCase):
    def fixture(self,root):
        (root/"LatticeProb").mkdir();(root/"LatticeProb.lean").write_text("-- root fixture\n");(root/"LatticeProb/Fixture.lean").write_text("-- selected fixture\n")
        return ["LatticeProb.lean","LatticeProb/Fixture.lean"]

    def test_stable_all_module_inventory_without_source_regex(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);paths=self.fixture(root)
            first=ax.source_inventory(root,paths);self.assertEqual(len(first),2)
            (root/paths[1]).write_text("-- changed bytes\n")
            self.assertNotEqual(first,ax.source_inventory(root,paths))

    def test_missing_empty_duplicate_untracked_symlink_rejected(self):
        for variant in ["root","empty","duplicate","untracked","symlink","unsupported"]:
            with self.subTest(variant=variant),tempfile.TemporaryDirectory() as d:
                root=Path(d);paths=self.fixture(root)
                if variant=="root":(root/paths[0]).unlink()
                if variant=="empty":paths=[]
                if variant=="duplicate":paths+=paths
                if variant=="untracked":(root/"LatticeProb/New.lean").write_text("-- extra fixture")
                if variant=="symlink":(root/paths[1]).unlink();(root/paths[1]).symlink_to(root/paths[0])
                if variant=="unsupported":(root/paths[1]).rename(root/"LatticeProb/Bad Name.lean");paths[1]="LatticeProb/Bad Name.lean"
                with self.assertRaises(diag.GateError):ax.source_inventory(root,paths)

    def test_tracked_inventory_actual_exit_and_multiplicity(self):
        for rc,out in [(42,"a\0"),(0,""),(0,"a"),(0,"a\0a\0")]:
            def runner(command,**kw):return subprocess.CompletedProcess(command,rc,out,"")
            with self.subTest(rc=rc,out=out),self.assertRaises(diag.GateError):ax.tracked_paths(Path.cwd(),runner)

    def test_audit_two_pass_actual_binding_and_drift(self):
        identity={"sources":SOURCES,"policy":"fixture"}
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)/"repo";root.mkdir();evidence=Path(d)/"external";calls=[]
            def execute(command,cwd,**kw):
                calls.append((command,cwd,kw));phase=Path(command[-1]).stem
                return result(inspection(phase,identity=ax.digest(identity)))
            with patch.object(ax,"input_identity",return_value=identity):record=ax.audit(root,evidence,execute=execute)
            self.assertEqual(record["expected_names"],sorted(NAMES));self.assertEqual(len(calls),2)
            self.assertTrue(all(c[0][:3]==["lake","env","lean"] and c[2]["lock"] for c in calls))
            self.assertEqual(json.loads((evidence/"public-census.json").read_text())["actual_probe_exits"],[0,0])
            with patch.object(ax,"input_identity",side_effect=[identity,{"sources":[]}]),self.assertRaises(diag.GateError):ax.audit(root,Path(d)/"drift",execute=execute)
            with patch.object(ax,"input_identity",return_value=identity),self.assertRaises(diag.GateError):ax.audit(root,root/"forbidden",execute=execute)


class ConfigurationTests(unittest.TestCase):
    def fixture(self,root):
        for pair,name in cmp.PAIRS.items():
            p=root/"LatticeProbAudit"/pair;p.mkdir(parents=True)
            original=Path(__file__).resolve().parents[2]/"LatticeProbAudit"/pair/"Challenge.lean"
            (p/"Challenge.lean").write_bytes(original.read_bytes())
            (p/"Solution.lean").write_text("-- source hash fixture\n")
            config={"challenge_module":f"LatticeProbAudit.{pair}.Challenge","solution_module":f"LatticeProbAudit.{pair}.Solution","theorem_names":[name],"definition_names":[],"permitted_axioms":sorted(ax.ALLOWED),"enable_nanoda":True}
            (p/"comparator.json").write_text(json.dumps(config))

    def test_exact_pairs_and_exact_config_hashes(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);self.fixture(root);rows=cmp.configuration(root)
            self.assertEqual({r["pair"] for r in rows},set(cmp.PAIRS));self.assertTrue(all(len(r["sources"])==2 for r in rows))

    def test_missing_empty_duplicate_swapped_pair_or_tool_mutations(self):
        for change in ["missing","empty","duplicate","swapped","extra","source","custom","nanoda","definition"]:
            with self.subTest(change=change),tempfile.TemporaryDirectory() as d:
                root=Path(d);self.fixture(root);p=root/"LatticeProbAudit/Kingman/comparator.json";v=json.loads(p.read_text())
                if change=="missing":p.unlink()
                elif change=="source":(p.parent/"Solution.lean").unlink()
                elif change=="extra":(p.parent/"Extra").mkdir();(p.parent/"Extra/comparator.json").write_text(p.read_text())
                else:
                    if change=="empty":v["theorem_names"]=[]
                    if change=="duplicate":v["theorem_names"]*=2
                    if change=="swapped":v["solution_module"]="LatticeProbAudit.GFF.Solution"
                    if change=="custom":v["permitted_axioms"]+=["Custom.ax"]
                    if change=="nanoda":v["enable_nanoda"]=False
                    if change=="definition":v["definition_names"]=["Unexpected"]
                    p.write_text(json.dumps(v))
                with self.assertRaises((diag.GateError,OSError)):cmp.configuration(root)

    def test_comparator_success_and_scoped_challenge_warning(self):
        path="LatticeProbAudit/Kingman/Challenge.lean"
        cmp.accept_comparator(result("Your solution is okay!"),path)
        cmp.accept_comparator(result(path+":10:2: warning: declaration uses 'sorry'\nYour solution is okay!"),path)
        for out,rc in [("Your solution is okay!",42),("Your solution is okay!",-9),("",0),("Your solution is okay!\nYour solution is okay!",0),("Your solution is okay!\nFAILED",0),("LatticeProbAudit/Kingman/Solution.lean:10:2: warning: declaration uses 'sorry'\nYour solution is okay!",0),(path+":10:2: warning: arbitrary warning\nYour solution is okay!",0),("Other/Challenge.lean:10:2: warning: declaration uses 'sorry'\nYour solution is okay!",0)]:
            with self.subTest(out=out,rc=rc),self.assertRaises(diag.GateError):cmp.accept_comparator(result(out,rc),path)

    def test_comparator_executes_all_pairs_or_fails_exact_child(self):
        for fail in [None,"GFF"]:
            with self.subTest(fail=fail),tempfile.TemporaryDirectory() as d:
                root=Path(d)/"repo";root.mkdir();self.fixture(root);calls=[]
                def execute(command,cwd,**kwargs):
                    calls.append(command)
                    pair=Path(command[-1]).parent.name if command[-1].endswith("json") else ""
                    return result("Your solution is okay!" if pair else "Build completed successfully",42 if pair==fail else 0)
                with patch.object(cmp,"verify_tools",return_value={"stable":True}):
                    if fail:
                        with self.assertRaises(diag.GateError):cmp.compare(root,Path(d)/"tools",Path(d)/"evidence",execute)
                    else:
                        cmp.compare(root,Path(d)/"tools",Path(d)/"evidence",execute)
                        self.assertEqual(len(calls),2*len(cmp.PAIRS));self.assertEqual(len([c for c in calls if c[-1].endswith("json")]),len(cmp.PAIRS))

    def test_bad_tool_identity_on_cache_hit_never_skips(self):
        calls=[]
        def execute(command,cwd,**kwargs):calls.append(command);return result("0"*40+"\n")
        with self.assertRaises(diag.GateError):cmp.verify_tools(Path.cwd(),Path("fixture-tools"),execute)
        self.assertEqual(calls[0],["git","rev-parse","HEAD"])

    def test_hygiene_source_credit_and_attribution(self):
        self.assertEqual(hygiene.prose_findings("Adapted from Anthropic, PBC software; see NOTICE."),[])
        for text in ["mo"+"dels: example", "hard"+"ware: workstation", "AI "+"coding "+"agents", "Co-"+"Authored-"+"By: example", "auto"+"mation:\n  methods: []"]:
            with self.subTest(text=text):self.assertTrue(hygiene.prose_findings(text))

    def test_actual_workflows_and_mutable_pin_missing_gate_bad_cache(self):
        root=Path(__file__).resolve().parents[2]
        for name in ("build","comparator"):
            text=(root/f".github/workflows/{name}.yml").read_text()
            self.assertEqual(hygiene.workflow_findings(text,name=="comparator"),[])
            for old,new in [("@3d3c42e5aac5ba805825da76410c181273ba90b1","@v5"),("python3 tools/verify.py","python3 missing.py"),("persist-credentials: false","persist-credentials: true"),("library-v1-${{ runner.os }}","library-v1-unknown"),("run: python3 tools/verify.py","continue-on-error: true\n        run: python3 tools/verify.py")]:
                altered=text.replace(old,new)
                if altered!=text:
                    with self.subTest(name=name,mutation=old):self.assertTrue(hygiene.workflow_findings(altered,name=="comparator"))
            self.assertNotIn("restore-keys:",text)
            for block in text.split("- name: "):
                if "actions/cache/save@" in block:self.assertIn("if: success()",block)

    def test_missing_required_test_rejected_before_any_child(self):
        with tempfile.TemporaryDirectory() as d,patch.object(verify,"input_identity",return_value={}):
            calls=[]
            with self.assertRaises(diag.GateError):verify.verify(Path(d),Path(d)/"external",execute=lambda *a,**kw:calls.append(a))
            self.assertEqual(calls,[])


class AdditionalBoundaryTests(unittest.TestCase):
    def test_ansi_and_both_stream_census_duplicate_conflict(self):
        out=inspection("closure")
        good=result("\x1b[32m"+out+"\x1b[0m")
        ax.parse_inspection(good,SOURCES,"closure","identity")
        ax.parse_inspection(result("",stderr=out),SOURCES,"closure","identity")
        duplicate="LIB-AXIOMS "+json.dumps({"name":NAMES[0],"axioms":[]})
        custom="LIB-AXIOMS "+json.dumps({"name":NAMES[0],"axioms":["Qualified.sorryAx"]})
        textual=f"'{NAMES[0]}' does not depend on any axioms"
        for extra in [duplicate,custom,textual,"\x1b[31mFile.lean:1:1: error: bad\x1b[0m","LIB-END {}"]:
            with self.subTest(extra=extra),self.assertRaises(diag.GateError):ax.parse_inspection(result(out,stderr=extra),SOURCES,"closure","identity")

    def test_duplicate_json_fields_and_nontyped_records(self):
        base=inspection()
        for change in [base.replace('"name":', '"name":"swapped","name":',1),base.replace('"count": 6','"count": true'),base.replace('"module_count": 2','"module_count": true'),base.replace('"kind": "theorem"','"kind": []',1),base.replace('LIB-MODULE "LatticeProb"','LIB-MODULE null',1)]:
            with self.subTest(change=change),self.assertRaises(diag.GateError):ax.parse_inspection(result(change),SOURCES,"census","identity")

    def test_complete_comparator_solution_and_bridge_scope(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);paths=InventoryTests().fixture(root);ConfigurationTests().fixture(root)
            bridge=root/"LatticeProbAudit/Support/Bridge.lean";bridge.parent.mkdir();bridge.write_text("-- fixture bridge\n")
            basic=root/"LatticeProbAudit/GFF/SolutionBasic.lean";basic.write_text("-- fixture basic\n")
            paths+=[p.relative_to(root).as_posix() for p in (root/"LatticeProbAudit").rglob("*.lean")]
            rows=ax.source_inventory(root,paths,include_comparator=True)
            selected={r["path"] for r in rows}
            self.assertIn(bridge.relative_to(root).as_posix(),selected);self.assertIn(basic.relative_to(root).as_posix(),selected)
            self.assertEqual(len(rows),len(cmp.PAIRS)+4);self.assertFalse(any(p.endswith("/Challenge.lean") for p in selected))
            basic.unlink()
            with self.assertRaises(diag.GateError):ax.source_inventory(root,paths,include_comparator=True)

    def test_hygiene_reads_every_tracked_surface_without_allowlist(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);paths=["Unowned/Source.lean","NOTICE","tools/check_names.py"]
            for rel in paths+["tools/verify.py","tools/check_public_hygiene.py","tools/check_comparators.py","tools/assurance_diagnostics.py"]:
                p=root/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text("Licensed source credit: Anthropic, PBC.\n")
            for name in ["build","comparator"]:
                target=root/f".github/workflows/{name}.yml";target.parent.mkdir(parents=True,exist_ok=True)
                target.write_text((Path(__file__).resolve().parents[2]/target.relative_to(root)).read_text())
            with patch.object(hygiene,"tracked_paths",return_value=paths):hygiene.check(root)
            for rel in paths:
                (root/rel).write_text("mo"+"dels: fixture attribution\n")
                with patch.object(hygiene,"tracked_paths",return_value=paths),self.assertRaises(diag.GateError):hygiene.check(root)
                (root/rel).write_text("Licensed software credit.\n")

    def test_comparator_ansi_both_stream_and_solution_warning_boundary(self):
        path="LatticeProbAudit/GFF/Challenge.lean"
        cmp.accept_comparator(result("",stderr="\x1b[32mYour solution is okay!\x1b[0m"),path)
        for stderr in ["\x1b[31merror: actual failure\x1b[0m", "Your solution is okay!", "LatticeProbAudit/GFF/Solution.lean:1:2: warning: declaration uses 'sorry'"]:
            with self.subTest(stderr=stderr),self.assertRaises(diag.GateError):cmp.accept_comparator(result("Your solution is okay!",stderr=stderr),path)

    def test_cached_binary_provenance_missing_stale_and_valid(self):
        identity={"comparator":{"revision":cmp.REVISIONS["comparator"],"binary_sha256":"a"*64},"build_environment":{"architecture":"fixture"}}
        with tempfile.TemporaryDirectory() as d:
            toolroot=Path(d)
            with patch.object(cmp,"tool_identity",return_value=identity),self.assertRaises(diag.GateError):cmp.verify_tools(Path.cwd(),toolroot)
            stamp=toolroot/"build-provenance.json";stamp.write_text(json.dumps(identity))
            with patch.object(cmp,"tool_identity",return_value=identity):self.assertEqual(cmp.verify_tools(Path.cwd(),toolroot),identity)
            for key in ["binary","revision","architecture"]:
                mutated=copy.deepcopy(identity)
                if key=="binary":mutated["comparator"]["binary_sha256"]="b"*64
                elif key=="revision":mutated["comparator"]["revision"]="0"*40
                else:mutated["build_environment"]["architecture"]="other"
                with self.subTest(key=key),patch.object(cmp,"tool_identity",return_value=mutated),self.assertRaises(diag.GateError):cmp.verify_tools(Path.cwd(),toolroot)

    def test_comment_only_gate_and_unsafe_cache_save_are_rejected(self):
        root=Path(__file__).resolve().parents[2]
        for name in ["build","comparator"]:
            text=(root/f".github/workflows/{name}.yml").read_text()
            mutations=[text.replace('run: python3 tools/verify.py','note: python3 tools/verify.py'),text.replace('if: success()','if: always()'),text.replace("'LatticeProb/**/*.lean', ",""),text.replace('contents: read','# contents: read')]
            for altered in mutations:
                with self.subTest(name=name,altered=altered):self.assertTrue(hygiene.workflow_findings(altered,name=="comparator"))

    def test_census_incomplete_second_pass_and_module_swap_are_rejected(self):
        identity={"sources":SOURCES,"policy":"fixture"}
        for mutation in ["name","module","missing","nonzero"]:
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as d:
                root=Path(d)/"repo";root.mkdir()
                def execute(command,cwd,**kw):
                    phase=Path(command[-1]).stem
                    ds=copy.deepcopy(DECLS);rc=0
                    if phase=="closure":
                        if mutation=="name":ds[0]["name"]="Other.f"
                        elif mutation=="module":ds[0]["module"]="LatticeProb"
                        elif mutation=="missing":ds=ds[:-1]
                        elif mutation=="nonzero":rc=42
                    return result(inspection(phase,declarations=ds,identity=ax.digest(identity)),rc)
                with patch.object(ax,"input_identity",return_value=identity),self.assertRaises(diag.GateError):ax.audit(root,Path(d)/"external",execute=execute)

    def test_production_build_and_hygiene_cannot_be_missing_or_skipped(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/"tools/tests").mkdir(parents=True);(root/"tools/tests/test_required.py").write_text("-- mocked test identity")
            for failure in ["tests","build"]:
                calls=[]
                def execute(command,cwd,**kwargs):
                    calls.append(command)
                    test=command[1:3]==["-m","unittest"]
                    return result("",42 if ((failure=="tests" and test) or (failure=="build" and not test)) else 0)
                with self.subTest(failure=failure),patch.object(verify,"input_identity",return_value={}),patch.object(verify,"check",return_value=[]),patch.object(verify,"configuration",return_value=[]),patch.object(verify,"audit") as audited,self.assertRaises(diag.GateError):
                    verify.verify(root,root.parent/"external",execute=execute)
                audited.assert_not_called();self.assertTrue(calls)
            with patch.object(verify,"input_identity",return_value={}),patch.object(verify,"check",side_effect=diag.GateError("unowned hygiene defect")),patch.object(verify,"configuration",return_value=[]),patch.object(verify,"audit") as audited,self.assertRaises(diag.GateError):
                verify.verify(root,root.parent/"external",execute=lambda *a,**k:result(""))
            audited.assert_not_called()

class CrossStreamTextControls(unittest.TestCase):
    def test_standard_and_zero_text_rows_across_streams(self):
        good="'A.f' depends on axioms: [propext]"
        ax.accept_print_axioms(result("\x1b[32m"+good+"\x1b[0m",stderr="'B.g' does not depend on any axioms"),["A.f","B.g"])
        for duplicate in [good,"'A.f' does not depend on any axioms","'A.f' depends on axioms: [Qualified.ax]","'B.g' depends on axioms: [Qualified.sorryAx]"]:
            with self.subTest(duplicate=duplicate),self.assertRaises(diag.GateError):ax.accept_print_axioms(result(good,stderr=duplicate),["A.f"])
        for rc,stderr in [(42,""),(-15,""),(0,"\x1b[31mwarning: bad\x1b[0m")]:
            with self.subTest(rc=rc,stderr=stderr),self.assertRaises(diag.GateError):ax.accept_print_axioms(result(good,rc,stderr),["A.f"])

class CurrentAdministrationControls(unittest.TestCase):
    def test_operational_names_rejected_and_licensed_human_credit_preserved(self):
        for token in ["f"+"leet", "Cl"+"aude", "Deep"+"Seek", "GL"+"M", "Open"+"AI", "So"+"nnet", "Op"+"us", "co"+"dex"]:
            with self.subTest(token=token):
                self.assertTrue(hygiene.prose_findings("The proof was written by " + token + "."))
        self.assertEqual(hygiene.prose_findings("Copyright Ahmed Bou-Rabee. Licensed source: Anthropic, PBC; see NOTICE."), [])

    def test_tracked_mathematical_comment_cannot_escape_operational_matcher(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);paths=["LatticeProb/Walk/Fixture.lean", "NOTICE"]
            configured=["tools/verify.py","tools/check_public_hygiene.py","tools/check_comparators.py","tools/assurance_diagnostics.py"]
            for rel in paths+configured:
                p=root/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text("Licensed source credit.\n")
            for name in ["build","comparator"]:
                dst=root/f".github/workflows/{name}.yml";dst.parent.mkdir(parents=True,exist_ok=True)
                dst.write_text((Path(__file__).resolve().parents[2]/dst.relative_to(root)).read_text())
            with patch.object(hygiene,"tracked_paths",return_value=paths):hygiene.check(root)
            (root/paths[0]).write_text("/- The proof was written by the proof " + "f"+"leet" + ". -/\n")
            with patch.object(hygiene,"tracked_paths",return_value=paths),self.assertRaises(diag.GateError):hygiene.check(root)

    def test_real_system_lock_command_even_when_path_contains_wrapper(self):
        seen=[]
        def runner(argv,**kw):seen.append(argv);return subprocess.CompletedProcess(argv,0,"Build completed successfully","")
        with tempfile.TemporaryDirectory() as d,patch.dict(os.environ,{"LAKE_LOCK":str(Path(d)/"fixture-exclusive.lock"), "PATH":"/tmp/fixture-wrapper"},clear=True):
            r=diag.run(["lake","build"],Path.cwd(),lock=True,runner=runner)
            expected_lock=str(Path(d)/"fixture-exclusive.lock")
        self.assertEqual(seen, [["/usr/bin/flock",expected_lock,"lake","build"]]);diag.require_clean(r)

    def test_warning_named_cache_artifact_is_informational_but_diagnostics_fail(self):
        text="✔ [12/16] Built Cache.Warning:c.o (112ms)\nBuild completed successfully (16 jobs)."
        diag.require_clean(result(text))
        for stream in ["warning: real warning", "Cache.lean:7:1: error: actual compiler error", "FAILED"]:
            with self.subTest(stream=stream),self.assertRaises(diag.GateError):diag.require_clean(result(text,stderr=stream))

class NativeAdapterControls(unittest.TestCase):
    def lock_fixture(self, directory, owner=100):
        base=Path(directory);lock=base/"expected-lock";lock.write_text("");proc=base/"proc";proc.mkdir()
        info=lock.stat();identity=f"{os.major(info.st_dev):x}:{os.minor(info.st_dev):x}:{info.st_ino}"
        line=f"1: FLOCK ADVISORY WRITE {owner} {identity} 0 EOF\n";(proc/"locks").write_text(line)
        for pid,parent,birth in [(200,150,3000),(150,100,2000),(100,1,1000)]:
            p=proc/str(pid);p.mkdir();fields=["R",str(parent)]+["0"]*17+[str(birth)]
            (p/"stat").write_text(f"{pid} (fixture process) "+" ".join(fields)+"\n")
        return lock,proc,line

    def test_kernel_expected_inode_and_live_ancestor_or_self(self):
        for owner in [100,200]:
            with self.subTest(owner=owner),tempfile.TemporaryDirectory() as d:
                lock,proc,line=self.lock_fixture(d,owner);r=diag.verify_inherited_lock(str(lock),proc_root=proc,self_pid=200)
                self.assertEqual(r["inode"],lock.stat().st_ino);self.assertEqual(r["owner"],owner)
                self.assertEqual(r["ancestry"][0]["pid"],200);self.assertEqual(r["ancestry"][-1]["pid"],owner)
                (proc/"locks").write_text(line+line.replace("1:","2:").replace("FLOCK","-> FLOCK").replace(str(owner)+" ","999 ",1))
                self.assertEqual(diag.verify_inherited_lock(str(lock),proc_root=proc,self_pid=200)["owner"],owner)

    def test_kernel_absent_unrelated_partial_shared_duplicate_and_wrong_inode_rejected(self):
        for mutation in ["absent","unrelated","partial","read","posix","range","duplicate","wrong-inode","wrong-device","waiter-only","malformed"]:
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as d:
                lock,proc,line=self.lock_fixture(d)
                if mutation=="absent":text=""
                elif mutation=="unrelated":text=line.replace("WRITE 100 ","WRITE 999 ")
                elif mutation=="partial":text=line.rstrip("\n")
                elif mutation=="read":text=line.replace("WRITE","READ")
                elif mutation=="posix":text=line.replace("FLOCK","POSIX")
                elif mutation=="range":text=line.replace("0 EOF","0 7")
                elif mutation=="duplicate":text=line+line.replace("1:","2:")
                elif mutation=="wrong-inode":text=line.replace(str(lock.stat().st_ino),str(lock.stat().st_ino+1))
                elif mutation=="wrong-device":text=line.replace(f"{os.major(lock.stat().st_dev):x}:{os.minor(lock.stat().st_dev):x}:","ffff:ffff:")
                elif mutation=="waiter-only":text=line.replace("FLOCK","-> FLOCK")
                else:text=line+"2: FLOCK partial\n"
                (proc/"locks").write_text(text)
                with self.assertRaises(diag.GateError):diag.verify_inherited_lock(str(lock),proc_root=proc,self_pid=200)

    def test_live_ancestry_identity_cannot_be_missing_malformed_dead_or_cyclic(self):
        for mutation in ["missing","malformed","zombie","unknown-state","cycle"]:
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as d:
                lock,proc,line=self.lock_fixture(d);p=proc/"150/stat"
                if mutation=="missing":p.unlink()
                elif mutation=="malformed":p.write_text("150 (fixture) R nonsense\n")
                elif mutation=="zombie":p.write_text(p.read_text().replace(") R ",") Z "))
                elif mutation=="unknown-state":p.write_text(p.read_text().replace(") R ",") ? "))
                else:p.write_text(p.read_text().replace(") R 100 ",") R 200 "))
                with self.assertRaises(diag.GateError):diag.verify_inherited_lock(str(lock),proc_root=proc,self_pid=200)

    def test_inherited_configuration_requires_exact_absolute_regular_physical_path(self):
        with tempfile.TemporaryDirectory() as d:
            lock,proc,line=self.lock_fixture(d);alias=Path(d)/"alias";alias.symlink_to(lock)
            for value in ["", "relative-lock", str(Path(d)/"absent"), str(alias), str(Path(d))]:
                with self.subTest(value=value),self.assertRaises(diag.GateError):diag.verify_inherited_lock(value,proc_root=proc,self_pid=200)

    def test_inherited_ancestry_or_expected_identity_change_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            lock,proc,line=self.lock_fixture(d);original=diag.process_identity;calls=[]
            def changing(proc_root,pid):
                row=original(proc_root,pid);calls.append(pid)
                if calls.count(pid)>1:row={**row,"birth":row["birth"]+1}
                return row
            with patch.object(diag,"process_identity",side_effect=changing),self.assertRaises(diag.GateError):diag.verify_inherited_lock(str(lock),proc_root=proc,self_pid=200)
            original_id=diag.lock_identity(str(lock),must_exist=True)
            with patch.object(diag,"lock_identity",side_effect=[original_id,{**original_id,"inode":original_id["inode"]+1}]),self.assertRaises(diag.GateError):diag.verify_inherited_lock(str(lock),proc_root=proc,self_pid=200)

    def test_inherited_run_no_reacquisition_and_exact_exit_status(self):
        binding={"path":"/tmp/expected-runtime-lock","device":7,"inode":9,"owner":100,"ancestry":[{"pid":200,"parent":100,"birth":5}]}
        for rc in [0,42,-15]:
            with self.subTest(rc=rc):
                seen=[]
                def runner(argv,**kw):seen.append(argv);return subprocess.CompletedProcess(argv,rc,"complete rows","")
                with patch.dict(os.environ,{"LAKE_GATE_LOCK":binding["path"]},clear=True),patch.object(diag,"verify_inherited_lock",return_value=binding) as checked:
                    r=diag.run(["lake","env","lean","external.lean"],Path.cwd(),lock=True,runner=runner)
                self.assertEqual(seen,[["lake","env","lean","external.lean"]]);self.assertEqual(checked.call_count,2);self.assertEqual(r.returncode,rc)
                if rc:
                    with self.assertRaises(diag.GateError):diag.require_clean(r)

    def test_inherited_runtime_missing_mismatch_and_post_child_drift_never_skip(self):
        seen=[];binding={"path":"/tmp/expected-runtime-lock","device":7,"inode":9,"owner":100,"ancestry":[]}
        with patch.dict(os.environ,{"LAKE_GATE_LOCK":"/tmp/expected-runtime-lock"},clear=True),patch.object(diag,"verify_inherited_lock",side_effect=diag.GateError("no kernel lock")),self.assertRaises(diag.GateError):
            diag.run(["lake","build"],Path.cwd(),lock=True,runner=lambda *a,**kw:seen.append(a))
        self.assertEqual(seen,[])
        with patch.dict(os.environ,{"LAKE_GATE_LOCK":binding["path"],"LAKE_LOCK":"/tmp/different-runtime-lock"},clear=True),patch.object(diag,"verify_inherited_lock",return_value=binding),patch.object(diag,"lock_identity",return_value={"path":"different","device":7,"inode":10}),self.assertRaises(diag.GateError):
            diag.run(["lake","build"],Path.cwd(),lock=True,runner=lambda *a,**kw:seen.append(a))
        self.assertEqual(seen,[])
        def runner(argv,**kw):seen.append(argv);return subprocess.CompletedProcess(argv,0,"Build completed successfully","")
        with patch.dict(os.environ,{"LAKE_GATE_LOCK":binding["path"]},clear=True),patch.object(diag,"verify_inherited_lock",side_effect=[binding,{**binding,"owner":999}]),self.assertRaises(diag.GateError):diag.run(["lake","build"],Path.cwd(),lock=True,runner=runner)
        self.assertEqual(seen,[["lake","build"]])

    def test_comparator_explicit_env_root_missing_and_actual_failure_boundary(self):
        root=Path("/tmp/explicit-tool-root")
        self.assertEqual(cmp.configured_tool_root(root,{"COMPARATOR_TOOL_ROOT":"/tmp/other"}),root)
        self.assertEqual(cmp.configured_tool_root(None,{"COMPARATOR_TOOL_ROOT":str(root)}),root)
        for env in [{},{"COMPARATOR_TOOL_ROOT":""},{"COMPARATOR_TOOL_ROOT":"relative"}]:
            with self.subTest(env=env),self.assertRaises(diag.GateError):cmp.configured_tool_root(None,env)
        seen=[]
        with patch.object(sys,"argv",["check_comparators.py"]),patch.dict(os.environ,{"COMPARATOR_TOOL_ROOT":str(root)},clear=True),patch.object(cmp,"compare",side_effect=lambda actual_root,toolroot,evidence:seen.append(toolroot)):
            self.assertEqual(cmp.main(),0)
        self.assertEqual(seen,[root])
        import contextlib,io
        captured=io.StringIO()
        with contextlib.redirect_stderr(captured),patch.object(sys,"argv",["check_comparators.py","--tools-only"]),patch.dict(os.environ,{"COMPARATOR_TOOL_ROOT":str(root)},clear=True),patch.object(cmp,"verify_tools",side_effect=diag.GateError("wrong actual tool identity")):
            self.assertEqual(cmp.main(),1)
        self.assertIn("check_comparators: FAIL",captured.getvalue())
        captured=io.StringIO()
        with contextlib.redirect_stderr(captured),patch.object(sys,"argv",["check_comparators.py"]),patch.dict(os.environ,{},clear=True),patch.object(cmp,"compare") as compare:
            self.assertEqual(cmp.main(),1);compare.assert_not_called()
        self.assertIn("COMPARATOR_TOOL_ROOT is required",captured.getvalue())

    def test_native_success_counts_are_positive_exact_and_status_sensitive(self):
        for gate,count in [("check_axioms",34),("check_warnings",620),("check_public_hygiene",650),("check_comparators",3)]:
            text=diag.success_summary(gate,count,"actual inspected selection")
            self.assertIn(f"{gate}: OK ({count} item(s) inspected)",text)
            self.assertEqual(__import__("re").findall(r"([0-9]+)\s+(?:nodes|statements|declarations|names|anchors|items)(?=\W|$)",text),[str(count)])
            diag.require_clean(result(text))
            with self.assertRaises(diag.GateError):diag.require_clean(result(text,rc=42))
        for count in [0,-1,True,"34"]:
            with self.subTest(count=count),self.assertRaises(diag.GateError):diag.success_summary("check_axioms",count,"selection")
        root=Path(__file__).resolve().parents[1]
        self.assertFalse((root/"check_diagnostics.py").exists());self.assertTrue((root/"assurance_diagnostics.py").is_file())

    def test_stock_helper_runpath_startup_resolves_exact_local_modules(self):
        tools = Path(__file__).resolve().parents[1]
        code = ("import pathlib,runpy,sys; "
                "target=pathlib.Path(sys.argv[1]).resolve(); "
                "values=runpy.run_path(str(target),run_name='__gate_startup_inspection__'); "
                "assert callable(values['main']); "
                "assert pathlib.Path(sys.modules['assurance_diagnostics'].__file__).resolve().parent "
                "== target.parent; "
                "print('local startup imports resolved')")
        for name in ["check_axioms.py", "check_comparators.py", "check_public_hygiene.py",
                     "check_warnings.py", "verify.py"]:
            with self.subTest(entrypoint=name), tempfile.TemporaryDirectory() as cwd:
                child = subprocess.run([sys.executable, "-I", "-B", "-c", code, str(tools/name)],
                                       cwd=cwd, capture_output=True, text=True, timeout=30)
                self.assertEqual(child.returncode, 0, child.stdout + child.stderr)
                self.assertEqual(child.stdout, "local startup imports resolved\n")
                self.assertEqual(child.stderr, "")

class ExactFivePairControls(unittest.TestCase):
    def test_both_new_pairs_require_exact_full_baseline_configuration(self):
        for pair in ("BerryEsseen","NormalComparison"):
            for mutation in ("missing-config","missing-solution","wrong-theorem",
                             "extra-premise-name","duplicate-name","custom-axiom",
                             "disabled-nanoda","changed-challenge"):
                with self.subTest(pair=pair,mutation=mutation),tempfile.TemporaryDirectory() as d:
                    root=Path(d);paths=InventoryTests().fixture(root)
                    ConfigurationTests().fixture(root);p=root/"LatticeProbAudit"/pair
                    value=json.loads((p/"comparator.json").read_text())
                    if mutation=="missing-config":(p/"comparator.json").unlink()
                    elif mutation=="missing-solution":(p/"Solution.lean").unlink()
                    elif mutation=="changed-challenge":
                        with (p/"Challenge.lean").open("a") as f:f.write("\n-- changed baseline\n")
                    else:
                        if mutation=="wrong-theorem":value["theorem_names"]=["Other.theorem"]
                        elif mutation=="extra-premise-name":value["theorem_names"]+=["Conditional.result"]
                        elif mutation=="duplicate-name":value["theorem_names"]*=2
                        elif mutation=="custom-axiom":value["permitted_axioms"]+=["sorryAx"]
                        else:value["enable_nanoda"]=False
                        (p/"comparator.json").write_text(json.dumps(value))
                    paths+=[q.relative_to(root).as_posix() for q in (root/"LatticeProbAudit").rglob("*.lean")]
                    with self.assertRaises((diag.GateError,OSError)):
                        ax.source_inventory(root,paths,include_comparator=True)

    def test_no_other_tracked_audit_module_is_a_baseline(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);paths=InventoryTests().fixture(root);ConfigurationTests().fixture(root)
            extra=root/"LatticeProbAudit/Other/Challenge.lean";extra.parent.mkdir()
            extra.write_text("-- a tracked input outside the exact baselines\n")
            paths+=[q.relative_to(root).as_posix() for q in (root/"LatticeProbAudit").rglob("*.lean")]
            selected={r["path"] for r in ax.source_inventory(root,paths,include_comparator=True)}
            excluded={f"LatticeProbAudit/{p}/Challenge.lean" for p in cmp.PAIRS}
            self.assertEqual(selected,set(paths)-excluded)
            self.assertIn(extra.relative_to(root).as_posix(),selected)
            for pair in cmp.PAIRS:self.assertIn(f"LatticeProbAudit/{pair}/Solution.lean",selected)

    def test_every_baseline_hash_drift_is_rejected(self):
        for pair in cmp.PAIRS:
            with self.subTest(pair=pair),tempfile.TemporaryDirectory() as d:
                root=Path(d);ConfigurationTests().fixture(root)
                p=root/"LatticeProbAudit"/pair/"Challenge.lean"
                p.write_bytes(p.read_bytes()+b"\n-- extra unapproved source bytes\n")
                with self.assertRaises(diag.GateError):cmp.configuration(root)


if __name__=="__main__":unittest.main()
