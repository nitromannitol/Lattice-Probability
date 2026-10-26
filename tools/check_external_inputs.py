#!/usr/bin/env python3
"""Exact cited-input registry guard; never a mathematical proof or freeze approval.

The code allowlist binds the whole reviewed meaning record, including bibliography,
locators, unproved status, literal command/body, carrier closure and package pins.
Editing JSON or rehashing a changed source cannot authorize another assumption.
Changes to the separately bound conditional consumer require their own review;
they do not change the literature proposition. No axiom policy is enlarged here.
"""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from assurance_diagnostics import GateError
from check_axioms import digest, regular_hash, strict_json

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = "metadata/external-inputs.json"
SCHEMA = "latticeprob-external-inputs-v1"
# A change to this exact allowlist requires separate review of the complete input.
# This freezes the reviewed formulation, never an authority to assert the proposition.
EXACT_ALLOWLIST = {
    "LatticeProb.External.SupercriticalBondUniqueness": (
        "86bea5ed061e21fc8636e65209581569709a1bb7e0315bf4fd8c57245ba324aa",
        "c627ff813699e1aab7a0b453e98e50b7e7d92f9c5a876fbdd550dfbf764f2bc9",
    ),
    "LatticeProb.External.SupercriticalBondCorrectorInput": (
        "6a555fffa16192ad6684309400918b4daf4b7a718d0db7e56e52aac732962111",
        "7d7e1ed2ef9cf1c1fbb48ec6c8b4508cd8506ad9215671c849b76bc4afd96916",
    ),
}


def check(root):
    """Return source-bound identity, rejecting every nonallowlisted registry change."""
    registry_hash = regular_hash(root, REGISTRY)
    value = strict_json((root / REGISTRY).read_text())
    if (not isinstance(value, dict) or set(value) != {"schema", "inputs"}
            or value["schema"] != SCHEMA or not isinstance(value["inputs"], list)):
        raise GateError("external inputs: malformed versioned registry")
    rows = value["inputs"]
    if len(rows) != len(EXACT_ALLOWLIST):
        raise GateError("external inputs: changed exact input allowlist")
    names = []
    identities = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"meaning", "conditional_consumer"}:
            raise GateError("external inputs: malformed input record")
        meaning, consumer = row["meaning"], row["conditional_consumer"]
        if not isinstance(meaning, dict) or not isinstance(consumer, dict):
            raise GateError("external inputs: malformed meaning/consumer")
        name = meaning.get("name")
        if not isinstance(name, str) or name not in EXACT_ALLOWLIST or name in names:
            raise GateError("external inputs: unregistered/duplicate input")
        names.append(name)
        expected_meaning, expected_consumer = EXACT_ALLOWLIST[name]
        if digest(meaning) != expected_meaning:
            raise GateError("external inputs: changed exact meaning/citation/status allowlist")
        if digest(consumer) != expected_consumer:
            raise GateError("external inputs: changed exact conditional consumer identity")
        # The exact record digest above fixes all keys, paths, hashes and literal text.
        for path, expected in meaning["carrier_dependencies"].items():
            if regular_hash(root, path) != expected:
                raise GateError("external inputs: carrier-body drift: " + path)
        for path, expected in meaning["configuration"].items():
            if regular_hash(root, path) != expected:
                raise GateError("external inputs: package/toolchain pin drift: " + path)
        for record, role in ((meaning, "input"), (consumer, "conditional consumer")):
            if regular_hash(root, record["source"]) != record["source_sha256"]:
                raise GateError("external inputs: exact " + role + " source drift")
            if record["command"] not in (root / record["source"]).read_text():
                raise GateError("external inputs: missing exact " + role + " command")
        # The second reviewed meaning includes the existing proved full iff, even
        # though the input definition does not import the growth theorem directly.
        for record in meaning.get("semantic_unit", {}).values():
            if not isinstance(record, dict):
                continue
            if regular_hash(root, record["source"]) != record["source_sha256"]:
                raise GateError("external inputs: semantic-unit source drift")
            if record["command"] not in (root / record["source"]).read_text():
                raise GateError("external inputs: missing exact semantic-unit command")
        identities.append({"name": name, "meaning_identity": expected_meaning,
                           "conditional_consumer_identity": expected_consumer,
                           "status": meaning["status"]})
    return {"schema": SCHEMA, "registry_sha256": registry_hash, "inputs": identities}


def main():
    try:
        identity = check(ROOT)
    except (GateError, OSError, ValueError) as error:
        print(f"check_external_inputs: FAIL: {error}", file=sys.stderr)
        return 1
    statuses = [row["status"] for row in identity["inputs"]]
    frozen = statuses.count("FROZEN_ASSUMPTION_UNPROVED")
    pending = statuses.count("REVIEWED_ASSUMPTION_PENDING_FREEZE")
    print(f"check_external_inputs: OK ({len(statuses)} cited assumptions: "
          f"{frozen} frozen unproved, {pending} reviewed pending freeze; metadata only)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
