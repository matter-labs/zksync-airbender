import copy
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import native_qualification as native


class NativeQualification(unittest.TestCase):
    def setUp(self):
        self.current = {"sha256": "a" * 64}
        self.receipt = {"schema": 1, "fingerprint": self.current["sha256"],
                        "checks": list(native.CHECKS), "commit": "b" * 40,
                        "run_id": "123", "run_attempt": "1"}

    def test_exact_completed_native_inputs_can_be_reused_for_proof_edits(self):
        self.assertTrue(native.reusable(self.receipt, self.current, {})[0])

    def test_full_cold_and_requalification_always_require_fresh_native_work(self):
        for flag in native.FORCE_FLAGS:
            with self.subTest(flag=flag):
                self.assertFalse(native.reusable(self.receipt, self.current, {flag: "true"})[0])

    def test_incomplete_or_mismatched_receipts_never_authorize_reuse(self):
        for key in self.receipt:
            changed = copy.deepcopy(self.receipt)
            del changed[key]
            self.assertFalse(native.reusable(changed, self.current, {})[0], key)
        for key, value in (("fingerprint", "c" * 64), ("schema", 2),
                           ("checks", native.CHECKS[:-1]), ("run_id", "0"),
                           ("commit", "b" * 40 + "\ninjected=true")):
            changed = {**self.receipt, key: value}
            self.assertFalse(native.reusable(changed, self.current, {})[0], key)
        self.assertFalse(native.reusable(None, self.current, {})[0])

    def test_missing_corrupt_duplicate_or_nonobject_receipts_require_fresh_work(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "receipt.json"
            self.assertIsNone(native.load_receipt(path))
            for text in ("{", "null", "[]", '{"schema":1,"schema":1}'):
                path.write_text(text)
                self.assertIsNone(native.load_receipt(path))

    def test_real_producer_import_closure_includes_guard_and_provenance(self):
        paths = native.script_inputs(native.REPO)
        for name in ("check_setup_artifacts.py", "check_native_evidence.py",
                     "export_gkr_translations.py", "gkr_arithmetic_certificate.py",
                     "compilation_pool/guard.py", "compilation_pool/pool.py"):
            self.assertIn(native.SCRIPTS + name, paths)
        self.assertNotIn(native.SCRIPTS + "check_lean.py", paths)

    def test_record_and_decide_revalidate_inputs_before_emitting_reuse(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            inputs = directory / "inputs.json"
            receipt = directory / "receipt.json"
            outputs = directory / "outputs.txt"
            inputs.write_text(json.dumps(self.current))
            environment = {"GITHUB_SHA": self.receipt["commit"],
                           "GITHUB_RUN_ID": self.receipt["run_id"],
                           "GITHUB_RUN_ATTEMPT": self.receipt["run_attempt"]}
            arguments = ["native_qualification.py", "record", "--fingerprint", str(inputs),
                         "--receipt", str(receipt), "--outputs", str(outputs)]
            with (patch.dict(os.environ, environment, clear=True),
                  patch.object(native, "fingerprint", return_value=self.current),
                  patch("sys.argv", arguments), redirect_stdout(io.StringIO())):
                native.main()
                self.assertEqual(native.load_receipt(receipt), self.receipt)
                arguments[1] = "decide"
                native.main()
                self.assertIn("reuse=true\n", outputs.read_text())
                outputs.unlink()
                with patch.object(native, "fingerprint", return_value={"sha256": "c" * 64}):
                    for command in ("record", "decide"):
                        arguments[1] = command
                        with self.assertRaisesRegex(ValueError, "inputs changed"):
                            native.main()
                        self.assertFalse(outputs.exists())
                        self.assertEqual(native.load_receipt(receipt), self.receipt)

    def test_fingerprint_covers_native_inputs_but_not_proof_or_document_edits(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            source = "cs/src/native.rs"
            producer = native.SCRIPTS + "producer.py"
            manifest = native.PREFIX + "artifacts/setup/manifest.json"
            names = [source, producer, "Cargo.toml", "Cargo.lock", native.setup.NATIVE_LOCK,
                     "rust-toolchain.toml", ".github/workflows/ci.yml",
                     ".github/workflows/formal-verification.yml", native.PREFIX + "lakefile.toml",
                     native.PREFIX + "artifacts/compiler/manifest.json",
                     native.PREFIX + "artifacts/compiler/interpretation/window-semantics.json",
                     "cs/compiled_circuits/sample_layout_no_caches_gkr.json"]
            for name in names:
                path = repo / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("initial\n")
            (repo / manifest).write_text(json.dumps({"source_sha256": {source: "pinned"}}))
            with (patch.object(native.setup, "check") as setups,
                  patch.object(native.compiler, "check") as compiler,
                  patch.object(native.evidence, "check") as evidence,
                  patch.object(native.compiler, "COMPILER_INPUTS", {"Cargo.lock"}),
                  patch.object(native.evidence, "SOURCES", set()),
                  patch.object(native.windows, "SOURCES", set()),
                  patch.object(native, "script_inputs", return_value={producer}),
                  patch.object(native.subprocess, "check_output", return_value="pinned toolchain"),
                  patch.dict(os.environ, {}, clear=True)):
                original = native.fingerprint(repo)
                for name in ("README.md", native.PREFIX + "Tests/Foo.lean"):
                    path = repo / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("proof or prose edit\n")
                self.assertEqual(native.fingerprint(repo), original)
                for name in names + [manifest]:
                    path = repo / name
                    before = path.read_bytes()
                    # Whitespace changes even in valid manifests invalidate reuse.
                    path.write_bytes(before + b"\n")
                    changed = native.fingerprint(repo)
                    self.assertNotEqual(changed["sha256"], original["sha256"], name)
                    path.write_bytes(before)
                added = repo / "cs/compiled_circuits/new_layout_no_caches_gkr.json"
                added.write_text("new circuit")
                self.assertNotEqual(native.fingerprint(repo)["sha256"], original["sha256"])
                added.unlink()
                with patch.dict(os.environ, {"RUSTFLAGS": "-C opt-level=3"}):
                    self.assertNotEqual(native.fingerprint(repo)["sha256"], original["sha256"])
                with patch.object(native.subprocess, "check_output", return_value="new toolchain"):
                    self.assertNotEqual(native.fingerprint(repo)["sha256"], original["sha256"])
                for checker in (setups, compiler, evidence):
                    checker.side_effect = ValueError("stale retained source or artifact")
                    with self.assertRaisesRegex(ValueError, "stale retained"):
                        native.fingerprint(repo)
                    checker.side_effect = None


if __name__ == "__main__":
    unittest.main()
