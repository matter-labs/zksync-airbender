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
    check)
      if [[ ${REQUIRED_RC:-0} == 0 ]]; then printf 'export\n' > "$KERNEL_EXPORT_PATH"; fi
      return "${REQUIRED_RC:-0}" ;;
    env\ leanchecker-paranoid\ --silent\ --from-export\ *) return "${PARANOID_RC:-0}" ;;
    'check --paranoid'|check\ --paranoid\ --from-export\ *) return "${EXTERNAL_RC:-0}" ;;
    'env leanchecker CleanCore.Equivalence Checks.Axioms') return "${CLEAN_RC:-0}" ;;
    *) return 99 ;;
  esac
}
source "$1" "$2"
'''


class ReplayGateTests(unittest.TestCase):
    def replay(self, step="kernel-check", export_exists=False, **overrides):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean").mkdir()
            if export_exists:
                (root / "lean/.lake").mkdir()
                export = root / 'complete-export'
                export.write_text("complete export\n")
                (root / "lean/.lake/kernel-export-path").write_text(str(export) + '\n')
            trace = root / "trace"
            env = dict(os.environ, FV_DIR=directory, KERNEL_CHECKER="lake", REPLAY_TRACE=str(trace),
                       RUNNER_TEMP=directory,
                       REQUIRED_RC="0", EXTERNAL_RC="0", CLEAN_RC="0", PARANOID_RC="0")
            env.update(overrides)
            result = subprocess.run(
                ["bash", "-c", MOCK, "replay-test", str(CI / "lean-ci.sh"), step],
                env=env, capture_output=True, text=True,
            )
            calls = trace.read_text().splitlines() if trace.exists() else []
            for index, call in enumerate(calls):
                if ' --from-export ' in call:
                    command, export_path = call.rsplit(' ', 1)
                    self.assertFalse(Path(export_path).is_relative_to(root / 'lean'))
                    calls[index] = command + ' <export>'
            return result.returncode, calls

    def test_required_checks_exclude_external_checkers(self):
        code, calls = self.replay()
        self.assertEqual(code, 0)
        self.assertEqual(calls, ["check", "env leanchecker-paranoid --silent --from-export <export>",
                                 "env leanchecker CleanCore.Equivalence Checks.Axioms"])

    def test_kernel_or_export_axiom_failure_fails_required_replay(self):
        code, calls = self.replay(REQUIRED_RC="17")
        self.assertEqual(code, 17)
        self.assertEqual(calls, ["check"])

    def test_clean_module_rejection_remains_required(self):
        code, _ = self.replay(CLEAN_RC="19")
        self.assertEqual(code, 19)

    def test_native_paranoid_rejection_remains_required(self):
        code, calls = self.replay(PARANOID_RC="21")
        self.assertEqual(code, 21)
        self.assertEqual(calls, ["check", "env leanchecker-paranoid --silent --from-export <export>"])

    def test_external_failure_is_reported_without_changing_required_result(self):
        code, calls = self.replay("kernel-external", EXTERNAL_RC="23")
        self.assertEqual(code, 23)
        self.assertEqual(calls, ["check --paranoid"])
        workflow = WORKFLOW.read_text()
        required = workflow.split("- name: Required Lean kernel replay and export axiom audit", 1)[1].split("- name:", 1)[0]
        external = workflow.split("- name: Bundled external checkers (advisory)", 1)[1].split("- name:", 1)[0]
        self.assertNotIn("continue-on-error: true", required)
        self.assertIn("continue-on-error: true", external)

    def test_advisory_checks_reuse_the_complete_required_export(self):
        code, calls = self.replay("kernel-external", export_exists=True, EXTERNAL_RC="23")
        self.assertEqual(code, 23)
        self.assertEqual(calls, ["check --paranoid --from-export <export>"])


class SandboxExportTests(unittest.TestCase):
    def wrapper(self, exporting=True, status=0):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "bwrap"
            binary.write_text('#!/usr/bin/env bash\nprintf "%s\\n" "$@" > "$SANDBOX_ARGS"\n'
                              'printf "complete export\\n"\nexit "$SANDBOX_RC"\n')
            binary.chmod(0o755)
            export = root / "complete.ndjson"
            arguments = root / "arguments"
            env = dict(os.environ, PATH=str(root) + os.pathsep + os.environ['PATH'],
                       SANDBOX_ARGS=str(arguments), SANDBOX_RC=str(status), KERNEL_EXPORT_PATH=str(export))
            flags = ["--clearenv"]
            if exporting:
                flags += ["--setenv", "LAKE_CHECK_EXPORT", "1"]
            result = subprocess.run([str(CI / "kernel-bwrap.sh"), *flags, "--", "lake", "check"],
                                    env=env, capture_output=True, text=True)
            return (result, export.read_text() if export.exists() else None,
                    export.with_suffix('.ndjson.part').exists(), arguments.read_text().splitlines(), flags)

    def test_complete_export_is_copied_without_changing_the_sandbox_arguments(self):
        result, exported, partial, arguments, flags = self.wrapper()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(exported, result.stdout)
        self.assertEqual(exported, "complete export\n")
        self.assertFalse(partial)
        compiled = str(CI.parents[1] / "cs/compiled_circuits")
        self.assertEqual(arguments, flags + ["--ro-bind", compiled, compiled, "--", "lake", "check"])

    def test_failed_export_is_not_published(self):
        result, exported, partial, _, _ = self.wrapper(status=17)
        self.assertEqual(result.returncode, 17)
        self.assertIsNone(exported)
        self.assertFalse(partial)

    def test_other_sandbox_commands_do_not_create_an_export(self):
        result, exported, partial, _, _ = self.wrapper(exporting=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIsNone(exported)
        self.assertFalse(partial)


if __name__ == "__main__":
    unittest.main()
