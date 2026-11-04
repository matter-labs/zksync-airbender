#!/usr/bin/env python3
"""Failure controls for compiler translation provenance; kernel tests are separate."""
import json
from pathlib import Path
import shutil
import tempfile
import tomllib
import unittest
from unittest.mock import patch

import check_gkr_translations as checker
from check_compiler_export_bytes import compare
from export_gkr_translations import COMPILER_INPUTS, LEAN, ROOT, digest
import check_setup_freshness as setup_freshness


class CompilerProvenance(unittest.TestCase):
    def test_import_glob_required_for_reader_dependencies(self):
        lake = tomllib.loads((LEAN / "lakefile.toml").read_text())
        compiler = next(lib for lib in lake["lean_lib"] if lib["name"] == "GKRCompiler")
        compiler["globs"] = ["Airbender.Proofs.GKRCompiler"]
        with self.assertRaisesRegex(ValueError, "reader/library ownership changed"):
            checker.check_library_ownership(lake)

    def test_protocol_rows_keep_their_input_dependencies(self):
        lake = tomllib.loads((LEAN / "lakefile.toml").read_text())
        protocol = next(lib for lib in lake["lean_lib"] if lib["name"] == "GKRProtocol")
        protocol["globs"].remove("Airbender.Import.Compiler.Rows.+")
        with self.assertRaisesRegex(ValueError, "reader/library ownership changed"):
            checker.check_library_ownership(lake)

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name) / "compiler"
        shutil.copytree(LEAN / "artifacts/compiler", self.directory)
        # Payload mutation controls use an explicitly unqualified input fixture.
        # This does not update retained pins or claim a native re-export result.
        manifest = self.directory / "manifest.json"
        data = json.loads(manifest.read_text())
        data["compiler_inputs"] = {name: digest(ROOT / name) for name in COMPILER_INPUTS}
        manifest.write_text(json.dumps(data))
        original_check = checker.setup.check
        candidate = setup_freshness.requalification_manifest(ROOT)
        fixture = patch.object(checker.setup, 'check', side_effect=lambda repo: original_check(repo, manifest=candidate))
        fixture.start()
        self.addCleanup(fixture.stop)

    def mutate(self, suffix, change, repin=False, name="add-sub-cached"):
        path = self.directory / (name + suffix)
        data = json.loads(path.read_text())
        change(data)
        path.write_text(json.dumps(data))
        if repin:
            manifest = self.directory / "manifest.json"
            data = json.loads(manifest.read_text())
            key = {".json": "pair_sha256", "-source.json": "source_sha256",
                   "-certificate.json": "certificate_sha256"}[suffix]
            data["files"][name][key] = digest(path)
            manifest.write_text(json.dumps(data))

    def test_payload_with_explicit_current_input_fixture(self):
        self.assertEqual(checker.check(self.directory), 11)

    def test_stale_retained_inputs_are_still_rejected(self):
        original = json.loads((LEAN / "artifacts/compiler/manifest.json").read_text())
        current = {name: digest(ROOT / name) for name in COMPILER_INPUTS}
        if original['compiler_inputs'] == current:
            self.assertEqual(checker.check(LEAN / "artifacts/compiler"), 11)
        else:
            with self.assertRaises(ValueError):
                checker.check(LEAN / "artifacts/compiler")

    def test_requalification_promotes_only_input_receipts(self):
        destination = Path(self.temporary.name) / 'retained'
        shutil.copytree(LEAN / 'artifacts/compiler', destination)
        before = {path.name: path.read_bytes() for path in destination.iterdir() if path.is_file()}
        self.assertEqual(compare(destination, self.directory, requalify=True), 34)
        for name, data in before.items():
            if name != 'manifest.json':
                self.assertEqual((destination / name).read_bytes(), data)
        self.assertEqual((destination / 'manifest.json').read_bytes(), (self.directory / 'manifest.json').read_bytes())

    def test_requalification_rejects_changed_payload_before_promotion(self):
        destination = Path(self.temporary.name) / 'retained'
        shutil.copytree(LEAN / 'artifacts/compiler', destination)
        before = (destination / 'manifest.json').read_bytes()
        self.mutate('.json', lambda data: data['circuit'].__setitem__('scratch_space_size', 1), True)
        with self.assertRaisesRegex(ValueError, 'export differs'):
            compare(destination, self.directory, requalify=True)
        self.assertEqual((destination / 'manifest.json').read_bytes(), before)

    def test_requalification_rejects_changed_manifest_metadata(self):
        destination = Path(self.temporary.name) / 'retained'
        shutil.copytree(LEAN / 'artifacts/compiler', destination)
        before = (destination / 'manifest.json').read_bytes()
        path = self.directory / 'manifest.json'
        data = json.loads(path.read_text())
        data['scope'] = 'changed scope'
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'only producer input receipts'):
            compare(destination, self.directory, requalify=True)
        self.assertEqual((destination / 'manifest.json').read_bytes(), before)

    def test_changed_native_output_metadata(self):
        self.mutate(".json", lambda data: data["circuit"].__setitem__("scratch_space_size", 1))
        with self.assertRaisesRegex(ValueError, "Compiler artifact changed"):
            checker.check(self.directory)

    def test_rehashed_cached_native_output_is_compared_to_production(self):
        self.mutate(".json", lambda data: data["circuit"].__setitem__("scratch_space_size", 1),
                    True, name="add-sub-cached")
        with self.assertRaisesRegex(ValueError, "Complete compiler output differs.*add-sub-cached"):
            checker.check(self.directory)

    def test_rehashed_source_omission(self):
        self.mutate("-source.json", lambda data: data["semantic_inputs"]["range_checks"].pop(), True)
        with self.assertRaisesRegex(ValueError, "Source semantic input count changed"):
            checker.check(self.directory)

    def test_detached_source(self):
        self.mutate("-source.json", lambda data: data["source"].__setitem__("num_variables", 43), True)
        with self.assertRaisesRegex(ValueError, "Source sidecar is detached"):
            checker.check(self.directory)

    def test_missing_compilation(self):
        (self.directory / "keccak-cached-source.json").unlink()
        with self.assertRaisesRegex(ValueError, "artifact inventory differs"):
            checker.check(self.directory)

    def test_export_bytes_ignore_derived_directories_but_reject_file_changes(self):
        retained = LEAN / 'artifacts/compiler'
        # This byte-only control starts with the original exact manifest.
        shutil.copyfile(retained / 'manifest.json', self.directory / 'manifest.json')
        shutil.rmtree(self.directory / 'interpretation')
        shutil.rmtree(self.directory / 'lookup')
        self.assertEqual(compare(retained, self.directory), 34)
        path = self.directory / 'manifest.json'
        original = path.read_bytes()
        path.write_bytes(original + b'\n')
        with self.assertRaisesRegex(ValueError, 'export differs'):
            compare(retained, self.directory)
        path.unlink()
        with self.assertRaisesRegex(ValueError, 'inventories differ'):
            compare(retained, self.directory)
        path.write_bytes(original)
        (self.directory / 'extra.json').write_text('{}')
        with self.assertRaisesRegex(ValueError, 'inventories differ'):
            compare(retained, self.directory)

    def test_rehashed_certificate_corruption(self):
        self.mutate("-certificate.json", lambda data: data["selected"].pop(), True)
        with self.assertRaisesRegex(ValueError, "Arithmetic identity synthesis changed"):
            checker.check(self.directory)


if __name__ == "__main__":
    unittest.main()
