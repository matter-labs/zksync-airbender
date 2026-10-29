#!/usr/bin/env python3
"""Focused provenance/freshness failure controls. No Cargo or Lean subprocesses."""

import copy
import json
from pathlib import Path
import shutil
import tempfile
import tomllib
import unittest

import check_native_evidence as evidence
import check_setup_artifacts as retained
import check_setup_freshness as freshness


class ProvenanceControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.scratch = Path(self.temporary.name)
        self.manifest = retained.read_json(retained.ARTIFACTS / "manifest.json")

    def mutated(self, family, change):
        original = retained.ARTIFACTS / (family + ".json")
        payload = retained.read_json(original)
        geometry = payload["trace_len"], len(payload["columns"])
        change(payload)
        self.assertEqual(geometry, (payload["trace_len"], len(payload["columns"])))
        output = self.scratch / original.name
        output.write_text(json.dumps(payload))
        with self.assertRaisesRegex(ValueError, "differs from retained complete JSON"):
            freshness.compare_artifact(output, original)

    def test_current_retained_guards(self):
        self.assertEqual(retained.check()[0], 16)
        self.assertEqual(evidence.check(), 8)

    def test_native_json_inputs_are_required_lake_dependencies(self):
        config = tomllib.loads((retained.REPO / "formal_verification/lean/lakefile.toml").read_text())
        inputs = {entry["path"]: entry["name"] for entry in config["input_file"]}
        library = next(entry for entry in config["lean_lib"] if entry["name"] == "Airbender")
        required = {
            f"../../cs/compiled_circuits/{stem}_layout_no_caches_gkr.json"
            for stem in retained.PRODUCTION_CIRCUITS.values()
        }
        required.update(f"artifacts/setup/{name}" for name in self.manifest["artifacts"])
        required.update(
            f"../../cs/compiled_circuits/{stem}_layout_gkr.json"
            for stem in ("keccak_column_parity", "keccak_theta_rho", "keccak_chi5")
        )
        for path in sorted(required):
            with self.subTest(path=path):
                self.assertIn(path, inputs)
                self.assertIn(inputs[path], library["needs"])

    def test_clean_checkout_lock_bootstrap_never_overwrites(self):
        pinned = self.scratch / retained.NATIVE_LOCK
        pinned.parent.mkdir(parents=True)
        shutil.copyfile(retained.REPO / retained.NATIVE_LOCK, pinned)
        self.assertFalse((self.scratch / "Cargo.lock").exists())
        self.assertTrue(retained.prepare_native_lock(self.scratch, self.manifest, prepare=True))
        destination = self.scratch / "Cargo.lock"
        self.assertEqual(destination.read_bytes(), pinned.read_bytes())
        self.assertFalse(retained.prepare_native_lock(self.scratch, self.manifest, prepare=True))
        altered = destination.read_bytes() + b"\n# different lock selection\n"
        destination.write_bytes(altered)
        with self.assertRaisesRegex(ValueError, "refusing to overwrite"):
            retained.prepare_native_lock(self.scratch, self.manifest, prepare=True)
        self.assertEqual(destination.read_bytes(), altered)

    def test_changed_source_without_reexport(self):
        # Real local Cargo/source closure, not a fabricated dependency-name list.
        for name in [*self.manifest["source_sha256"], "Cargo.lock", retained.NATIVE_LOCK]:
            destination = self.scratch / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(retained.REPO / name, destination)
        retained.check_sources(self.scratch, self.manifest)
        dependency = self.scratch / "riscv_transpiler/src/ir/simple_instruction_set.rs"
        dependency.write_text(dependency.read_text() + "\n// provenance negative control\n")
        with self.assertRaisesRegex(ValueError, "Setup source changed.*simple_instruction_set"):
            retained.check_sources(self.scratch, self.manifest)

    def test_manifest_omitting_real_unsigned_mul_source(self):
        manifest = copy.deepcopy(self.manifest)
        del manifest["source_sha256"]["circuit_defs/setups/src/unrolled_circuits/mul_div_unsigned_circuit/mod.rs"]
        with self.assertRaisesRegex(ValueError, "source inventory changed"):
            retained.check_sources(retained.REPO, manifest)

    def test_current_native_evidence_drift(self):
        manifest = retained.ARTIFACTS / "native-evidence.json"
        for name in evidence.SOURCES:
            path = self.scratch / name
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(retained.REPO / name, path)
        source = self.scratch / "prover/src/definitions/mod.rs"
        source.write_text(source.read_text() + "\n// evidence negative control\n")
        with self.assertRaisesRegex(ValueError, "Native evidence changed"):
            evidence.check(self.scratch, manifest)

    def test_same_geometry_physical_value(self):
        self.mutated("add-sub", lambda data: data["columns"][0]["blocks"][0]["values"].__setitem__(0, 1))

    def test_initialization_actual_relation_input(self):
        def change(data):
            pair = data["circuit"]["layers"][0]["gates"][1]["enforced_relation"]["InitsOrTeardownsInitialPair"]
            pair["timestamp_and_value"]["Teardown"]["lhs_value"][0] += 1
        self.mutated("inits-and-teardowns", change)

    def test_initialization_typed_coefficient_fixture(self):
        # Actual init uses specialized relations, with no serialized coefficient.
        # Exercise coefficient-only identity sensitivity using the native linear
        # constraint shape in an isolated copy of its otherwise unchanged JSON.
        data = retained.read_json(retained.ARTIFACTS / "inits-and-teardowns.json")
        data["circuit"]["degree_1_constraints"] = [{"constant_term": 0, "linear_terms": [[65536, 0]]}]
        expected = self.scratch / "expected.json"
        expected.write_text(json.dumps(data))
        data["circuit"]["degree_1_constraints"][0]["linear_terms"][0][0] += 1
        actual = self.scratch / "actual.json"
        actual.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "differs from retained complete JSON"):
            freshness.compare_artifact(actual, expected)

    def test_smoke_native_id(self):
        self.mutated("decoder-smoke", lambda data: data["tables"][0].__setitem__("id", 1))

    def test_smoke_native_offset(self):
        self.mutated("decoder-smoke", lambda data: data["tables"][1].__setitem__("offset", 2))

    def test_smoke_base_identity(self):
        identity = self.manifest["circuit_identities"]["decoder-smoke.json"]
        for name in (identity["base_path"], identity["constructor_path"]):
            destination = self.scratch / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(retained.REPO / name, destination)
        base = self.scratch / identity["base_path"]
        data = retained.read_json(base)
        data["trace_len"] += 1
        base.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "Smoke retained ADD/SUB base changed"):
            retained.check_smoke_identity(self.scratch, retained.ARTIFACTS, identity)

    def test_missing_fresh_artifact(self):
        for family in freshness.FAMILIES:
            if family != "inits-and-teardowns":
                (self.scratch / (family + ".json")).write_text("{}")
        with self.assertRaisesRegex(ValueError, "inventory differs.*inits-and-teardowns"):
            freshness.compare_directory(self.scratch)

    def test_complete_json_positive_and_typed_scalar(self):
        original = retained.ARTIFACTS / "add-sub.json"
        data = retained.read_json(original)
        path = self.scratch / "add-sub.json"
        path.write_text(json.dumps(data, sort_keys=True))
        freshness.compare_artifact(path, original)
        data["columns"][0]["blocks"][0]["values"][0] = False
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "differs from retained complete JSON"):
            freshness.compare_artifact(path, original)

    def test_exact_one_native_test_positive(self):
        name = retained.SMOKE_TEST
        text = f"running 1 test\ntest {name} ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 99 filtered out; finished in 0.1s\n"
        freshness.validate_test_output(text, name)

    def test_exact_one_test_with_nocapture_compiler_output(self):
        name = freshness.generator_test("add-sub")
        text = f"running 1 test\ntest {name} ... native compiler progress\nmore progress\nok\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 99 filtered out; finished in 0.1s\n"
        freshness.validate_test_output(text, name)

    def test_zero_selected_native_tests(self):
        text = "running 0 tests\ntest result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 99 filtered out; finished in 0.0s\n"
        with self.assertRaisesRegex(ValueError, "exactly one executed"):
            freshness.validate_test_output(text, retained.SMOKE_TEST)

    def test_ci_false_is_present(self):
        with self.assertRaisesRegex(ValueError, "CI=false still skips"):
            freshness.require_native_environment({"CI": "false"})
        freshness.require_native_environment({})

    def test_skipped_generator_cannot_pass_as_one_test(self):
        name = freshness.generator_test("add-sub")
        text = f"running 1 test\nskipping {name} in CI\ntest {name} ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 99 filtered out; finished in 0.0s\n"
        with self.assertRaisesRegex(ValueError, "skipped in CI"):
            freshness.validate_test_output(text, name)

    def test_native_dep_info_unpinned_include(self):
        include = self.scratch / "extra.inc"
        include.write_text("native include negative control\n")
        dep_info = self.scratch / "fixture.d"
        dep_info.write_text(f"fixture: {include}\n")
        with self.assertRaisesRegex(ValueError, "unpinned source/include"):
            retained.check_dep_info(self.scratch, self.manifest, [dep_info])


if __name__ == "__main__":
    unittest.main()
