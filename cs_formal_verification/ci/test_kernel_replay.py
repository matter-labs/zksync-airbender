#!/usr/bin/env python3
"""Check which replay failures are required and which are advisory."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


CI = Path(__file__).resolve().parent
WORKFLOW = CI.parents[1] / ".github/workflows/lean-formal-verification.yml"
MOCK = r'''
lake() {
  printf '%s\n' "$*" >> "$REPLAY_TRACE"
  case "$*" in
    check) return "${REQUIRED_RC:-0}" ;;
    'check --paranoid') return "${EXTERNAL_RC:-0}" ;;
    'env leanchecker CleanCore.Equivalence Checks.Axioms') return "${CLEAN_RC:-0}" ;;
    *) return 99 ;;
  esac
}
source "$1" "$2"
'''


class ReplayGateTests(unittest.TestCase):
    def replay(self, step="kernel-check", **overrides):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            trace = root / "trace"
            env = dict(os.environ, FV_DIR=directory, KERNEL_CHECKER="lake", REPLAY_TRACE=str(trace),
                       REQUIRED_RC="0", EXTERNAL_RC="0", CLEAN_RC="0")
            env.update(overrides)
            result = subprocess.run(
                ["bash", "-c", MOCK, "replay-test", str(CI / "lean-ci.sh"), step],
                env=env, capture_output=True, text=True,
            )
            return result.returncode, trace.read_text().splitlines() if trace.exists() else []

    def test_required_checks_exclude_external_checkers(self):
        code, calls = self.replay()
        self.assertEqual(code, 0)
        self.assertEqual(calls, ["check", "env leanchecker CleanCore.Equivalence Checks.Axioms"])

    def test_kernel_or_export_axiom_failure_fails_required_replay(self):
        code, calls = self.replay(REQUIRED_RC="17")
        self.assertEqual(code, 17)
        self.assertEqual(calls, ["check"])

    def test_clean_module_rejection_remains_required(self):
        code, _ = self.replay(CLEAN_RC="19")
        self.assertEqual(code, 19)

    def test_external_failure_is_reported_without_changing_required_result(self):
        code, calls = self.replay("kernel-external", EXTERNAL_RC="23")
        self.assertEqual(code, 23)
        self.assertEqual(calls, ["check --paranoid"])
        workflow = WORKFLOW.read_text()
        required = workflow.split("- name: Required Lean kernel replay and export axiom audit", 1)[1].split("- name:", 1)[0]
        external = workflow.split("- name: Bundled external checkers (advisory)", 1)[1].split("- name:", 1)[0]
        self.assertNotIn("continue-on-error: true", required)
        self.assertIn("continue-on-error: true", external)


if __name__ == "__main__":
    unittest.main()
