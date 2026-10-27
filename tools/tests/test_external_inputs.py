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
        paths = {external.REGISTRY}
        for row in self.value["inputs"]:
            meaning = row["meaning"]
            paths |= ({meaning["source"], row["conditional_consumer"]["source"]}
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
        self.assertEqual(len(identity["inputs"]), 4)
        self.assertEqual(identity["inputs"][1]["status"],
                         "FROZEN_ASSUMPTION_UNPROVED")
        second = self.value["inputs"][1]
        self.assertEqual(second["meaning"]["source_sha256"],
                         "9f446f7cb8a6e5d880554906e4506458a0e0e3f2f4a19d84ab76a6f277d01aeb")
        actual = second["conditional_consumer"]["type"]
        self.assertIn("(hclassical : SupercriticalBondUniqueness)", actual)
        self.assertIn("(hcorrector : SupercriticalBondCorrectorInput)", actual)
        self.assertIn("∃ p : unitInterval", actual)
        self.assertIn("∃ x y : uniqueInfiniteComponent h, u x ≠ u y", actual)

    def test_green_and_order_zero_consumers_keep_their_cited_inputs_explicit(self):
        green, order_zero = self.value["inputs"][2:]
        self.assertEqual(green["meaning"]["name"],
                         "LatticeProb.External.SupercriticalBondGreenColumnExistence")
        self.assertEqual(order_zero["meaning"]["name"],
                         "LatticeProb.External.ArmstrongDarioOrderZero")
        for row in (green, order_zero):
            self.assertEqual(row["meaning"]["status"], "FROZEN_ASSUMPTION_UNPROVED")
        self.assertIn("(hg : SupercriticalBondGreenColumnExistence)",
                      green["conditional_consumer"]["type"])
        self.assertIn("(hu : SupercriticalBondUniqueness)",
                      green["conditional_consumer"]["type"])
        self.assertIn("(input : LatticeProb.External.ArmstrongDarioOrderZero)",
                      order_zero["conditional_consumer"]["type"])
        self.assertIn("∃ c : ℝ, ∀ r : ℝ", order_zero["conditional_consumer"]["type"])

    def test_new_input_status_body_and_citation_changes_are_rejected(self):
        for index in (2, 3):
            original = copy.deepcopy(self.value["inputs"][index])
            changes = (
                lambda m: m.update(status="PROVED"),
                lambda m: m.update(command="def Unreviewed : Prop := True", body="True"),
                lambda m: m["bibliography"][0].update(title="Unreviewed citation"),
            )
            for change in changes:
                with self.subTest(index=index, change=change):
                    self.value["inputs"][index] = copy.deepcopy(original)
                    change(self.value["inputs"][index]["meaning"])
                    self.save()
                    with self.assertRaisesRegex(GateError, "meaning/citation/status"):
                        external.check(self.root)
            self.value["inputs"][index] = original
            self.save()

    def test_new_input_self_rehash_cannot_authorize_quantifier_weakening(self):
        changes = ((2, "∃! g", "∃ g"), (3, "∀ r : ℝ", "∃ r : ℝ"))
        for index, old, new in changes:
            with self.subTest(index=index):
                original = copy.deepcopy(self.value["inputs"][index])
                meaning = self.value["inputs"][index]["meaning"]
                path = meaning["source"]
                original_source = (self.root / path).read_bytes()
                self.change_source(path, old, new)
                changed = hashlib.sha256((self.root / path).read_bytes()).hexdigest()
                meaning["source_sha256"] = changed
                meaning["carrier_dependencies"][path] = changed
                meaning["command"] = meaning["command"].replace(old, new, 1)
                meaning["body"] = meaning["body"].replace(old, new, 1)
                self.save()
                with self.assertRaisesRegex(GateError, "meaning/citation/status"):
                    external.check(self.root)
                (self.root / path).write_bytes(original_source)
                self.value["inputs"][index] = original
                self.save()

    def test_corrector_body_and_full_iff_source_drift(self):
        meaning = self.value["inputs"][1]["meaning"]
        characterization = meaning["semantic_unit"]["full_characterization"]
        cases = ((meaning["source"], "∃! u", "∃ u"),
                 (characterization["source"], "IsCorrectedPlane C q u ↔",
                  "IsCorrectedPlane C q u →"))
        for path, old, new in cases:
            with self.subTest(path=path):
                original = (self.root / path).read_bytes()
                self.change_source(path, old, new)
                with self.assertRaisesRegex(GateError, "carrier-body drift"):
                    external.check(self.root)
                (self.root / path).write_bytes(original)

    def test_corrector_self_rehash_cannot_change_semantic_unit(self):
        meaning = self.value["inputs"][1]["meaning"]
        full = meaning["semantic_unit"]["full_characterization"]
        path = full["source"]
        self.change_source(path, "IsCorrectedPlane C q u ↔", "IsCorrectedPlane C q u →")
        changed = hashlib.sha256((self.root / path).read_bytes()).hexdigest()
        meaning["carrier_dependencies"][path] = changed
        full["source_sha256"] = changed
        full["command"] = full["command"].replace(" C q u ↔", " C q u →")
        full["type"] = full["type"].replace(" C q u ↔", " C q u →")
        self.save()
        with self.assertRaisesRegex(GateError, "meaning/citation/status"):
            external.check(self.root)

    def test_corrector_locator_type_and_status_are_fixed(self):
        original = copy.deepcopy(self.value["inputs"][1]["meaning"])
        mutations = (
            lambda m: m["bibliography"][1]["locators"].pop(),
            lambda m: m["semantic_unit"]["full_characterization"].update(type="True"),
            lambda m: m.update(status="PROVED"),
            lambda m: m.update(status="REVIEWED_ASSUMPTION_PENDING_FREEZE"),
        )
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                meaning = copy.deepcopy(original)
                mutate(meaning)
                self.value["inputs"][1]["meaning"] = meaning
                self.save()
                with self.assertRaisesRegex(GateError, "meaning/citation/status"):
                    external.check(self.root)

    def test_actual_corrector_consumer_source_and_type_drift(self):
        consumer = self.value["inputs"][1]["conditional_consumer"]
        self.change_source(consumer["source"],
                           "(hcorrector : SupercriticalBondCorrectorInput)",
                           "(hcorrector : True)")
        with self.assertRaisesRegex(GateError, "conditional consumer source drift"):
            external.check(self.root)
        consumer["type"] = consumer["type"].replace(
            "(hcorrector : SupercriticalBondCorrectorInput)", "(hcorrector : True)")
        consumer["command"] = consumer["command"].replace(
            "(hcorrector : SupercriticalBondCorrectorInput)", "(hcorrector : True)")
        consumer["source_sha256"] = hashlib.sha256(
            (self.root / consumer["source"]).read_bytes()).hexdigest()
        self.save()
        with self.assertRaisesRegex(GateError, "conditional consumer identity"):
            external.check(self.root)

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
