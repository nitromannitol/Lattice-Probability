"""Independent source/registry mutations at the exact cited-input boundary."""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_axioms as ax
import check_external_inputs as external
import verify
from assurance_diagnostics import GateError, Result

ROOT = Path(__file__).resolve().parents[2]


class ExternalInputTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.value = json.loads((ROOT / external.REGISTRY).read_text())
        row = self.value["inputs"][0]
        meaning = row["meaning"]
        paths = ({external.REGISTRY, meaning["source"], row["conditional_consumer"]["source"]}
                 | set(meaning["carrier_dependencies"]) | set(meaning["configuration"]))
        for relative in paths:
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, target)

    def save(self):
        (self.root / external.REGISTRY).write_text(json.dumps(self.value, ensure_ascii=False))

    def meaning(self):
        return self.value["inputs"][0]["meaning"]

    def change_source(self, path, old, new):
        target = self.root / path
        text = target.read_text()
        self.assertIn(old, text)
        target.write_text(text.replace(old, new, 1))

    def test_baseline_exact_public_input_and_nonvacuous_consumer(self):
        identity = external.check(self.root)
        self.assertEqual(identity["inputs"][0]["status"],
                         "FROZEN_ASSUMPTION_UNPROVED")
        self.assertEqual(self.meaning()["source_sha256"],
                         "b322761a1262fe643edef2f28247605145e3d3b0a590c9f16fa0a66bb45498a9")
        consumer = self.value["inputs"][0]["conditional_consumer"]
        self.assertIn("(hclassical : SupercriticalBondUniqueness)", consumer["type"])
        self.assertIn("∃ p : unitInterval, criticalProbability d < (p : ℝ)", consumer["type"])
        self.assertNotIn("False", consumer["type"])

    def test_definition_body_drift(self):
        self.change_source(self.meaning()["source"], "= 1)", "= 0)")
        with self.assertRaisesRegex(GateError, "input source drift"):
            external.check(self.root)

    def test_self_rehashed_input_body_cannot_authorize_an_assumption(self):
        meaning = self.meaning()
        self.change_source(meaning["source"], "= 1)", "= 0)")
        meaning["command"] = meaning["command"].replace("= 1)", "= 0)")
        meaning["body"] = meaning["body"].replace("= 1)", "= 0)")
        meaning["source_sha256"] = hashlib.sha256(
            (self.root / meaning["source"]).read_bytes()).hexdigest()
        self.save()
        with self.assertRaisesRegex(GateError, "meaning/citation/status"):
            external.check(self.root)

    def test_carrier_binder_drift(self):
        path = "LatticeProb/Prob/Percolation/LatticeBondModel.lean"
        self.change_source(path, "Configuration (d : ℕ) := Bond d → Bool",
                           "Configuration (d : ℕ) := Vertex d → Bool")
        with self.assertRaisesRegex(GateError, "carrier-body drift"):
            external.check(self.root)

    def test_self_rehashed_carrier_cannot_change_approved_meaning(self):
        path = "LatticeProb/Prob/Percolation/LatticeBondProbability.lean"
        self.change_source(path, "bernoulliMeasure true false p", "bernoulliMeasure false true p")
        self.meaning()["carrier_dependencies"][path] = hashlib.sha256(
            (self.root / path).read_bytes()).hexdigest()
        self.save()
        with self.assertRaisesRegex(GateError, "meaning/citation/status"):
            external.check(self.root)

    def test_wrong_package_pin(self):
        self.change_source("lake-manifest.json", self.meaning()["mathlib_revision"], "0" * 40)
        with self.assertRaisesRegex(GateError, "package/toolchain pin drift"):
            external.check(self.root)

    def test_wrong_toolchain(self):
        self.change_source("lean-toolchain", "v4.32.0", "v4.31.0")
        with self.assertRaisesRegex(GateError, "package/toolchain pin drift"):
            external.check(self.root)

    def test_extra_paper_owned_assertion_cannot_be_registered(self):
        extra = copy.deepcopy(self.value["inputs"][0])
        extra["meaning"]["name"] = "Rigidity.Main.liouville"
        self.value["inputs"].append(extra)
        self.save()
        with self.assertRaisesRegex(GateError, "exact input allowlist"):
            external.check(self.root)

    def test_paper_owned_replacement_cannot_be_registered(self):
        self.meaning()["name"] = "Rigidity.Main.liouville"
        self.save()
        with self.assertRaisesRegex(GateError, "unregistered"):
            external.check(self.root)

    def test_counterfeit_proved_status(self):
        self.meaning()["status"] = "PROVED"
        self.save()
        with self.assertRaisesRegex(GateError, "meaning/citation/status"):
            external.check(self.root)

    def test_missing_cited_locator(self):
        self.meaning()["bibliography"]["locators"].pop()
        self.save()
        with self.assertRaisesRegex(GateError, "meaning/citation/status"):
            external.check(self.root)

    def test_changed_exact_consumer_type(self):
        consumer = self.value["inputs"][0]["conditional_consumer"]
        self.change_source(consumer["source"], "(hd : 2 ≤ d)", "(hd : 3 ≤ d)")
        with self.assertRaisesRegex(GateError, "conditional consumer source drift"):
            external.check(self.root)

    def test_consumer_metadata_is_separate_from_meaning(self):
        self.value["inputs"][0]["conditional_consumer"]["type"] += " → False"
        self.save()
        with self.assertRaisesRegex(GateError, "conditional consumer identity"):
            external.check(self.root)

    def test_missing_duplicate_and_unknown_registry_fields(self):
        original = (self.root / external.REGISTRY).read_text()
        for text in (original.replace('"schema":', '"unknown":', 1),
                     original.replace('"schema":', '"schema": "duplicate", "schema":', 1),
                     '{"schema": "latticeprob-external-inputs-v1", "inputs": []}'):
            with self.subTest(text=text[:50]):
                (self.root / external.REGISTRY).write_text(text)
                with self.assertRaises(GateError):
                    external.check(self.root)
        (self.root / external.REGISTRY).unlink()
        with self.assertRaises(GateError):
            external.check(self.root)

    def test_symlinked_carrier_rejected(self):
        path = self.root / "LatticeProb/Prob/Percolation/LatticeBondModel.lean"
        original = path.with_suffix(".copy")
        path.rename(original)
        path.symlink_to(original)
        with self.assertRaisesRegex(GateError, "nonregular"):
            external.check(self.root)

    def test_standard_identity_requires_guard_before_inventory(self):
        self.meaning()["status"] = "PROVED"
        self.save()
        with patch.object(ax, "source_inventory") as inventory:
            with self.assertRaisesRegex(GateError, "meaning/citation/status"):
                ax.input_identity(self.root)
            inventory.assert_not_called()

    def test_preflight_rejects_invalid_input_before_child_tests(self):
        self.meaning()["bibliography"]["locators"] = []
        self.save()
        execute = unittest.mock.Mock()
        with self.assertRaisesRegex(GateError, "meaning/citation/status"):
            verify.verify(self.root, self.root / "evidence", preflight_only=True, execute=execute)
        execute.assert_not_called()

    def test_preflight_after_identity_rejects_registry_drift(self):
        tests = self.root / "tools/tests"
        tests.mkdir(parents=True)
        (tests / "test_fixture.py").write_text("# simulated child suite\n")
        before = external.check(self.root)
        def child(command, cwd, **kwargs):
            self.meaning()["status"] = "PROVED"
            self.save()
            return Result(tuple(command), 0, "", "")
        # Use the real external identity on both sides of the existing preflight check.
        with patch.object(verify, "input_identity", side_effect=lambda *a, **k: external.check(a[0])), \
                patch.object(verify, "check"), patch.object(verify, "configuration"):
            with self.assertRaisesRegex(GateError, "meaning/citation/status"):
                verify.verify(self.root, self.root / "evidence", preflight_only=True, execute=child)
        self.assertEqual(before["inputs"][0]["meaning_identity"],
                         external.EXACT_ALLOWLIST[self.meaning()["name"]][0])


if __name__ == "__main__":
    unittest.main()
