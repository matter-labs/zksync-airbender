#!/usr/bin/env python3
"""Check which replay failures are required and which are advisory."""
import os
import json
from pathlib import Path
import shlex
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
      if [[ ${REQUIRED_RC:-0} == 0 ]]; then
        env -i PATH="$PATH" "$COMPARATOR_BWRAP" --setenv LAKE_CHECK_EXPORT 1 -- lake check
      fi
      return "${REQUIRED_RC:-0}" ;;
    env\ leanchecker-paranoid\ --silent\ --from-export\ *) return "${PARANOID_RC:-0}" ;;
    'env lean --print-prefix') printf '/mock/toolchain\n' ;;
    env\ lean\ --run\ */external-checkers.lean\ *) return "${EXTERNAL_RC:-0}" ;;
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
            (root / "bin").mkdir()
            bwrap = root / "bin/bwrap"
            bwrap.write_text('#!/usr/bin/env bash\nprintf "export\\n"\n')
            bwrap.chmod(0o755)
            if export_exists:
                (root / "lean/.lake").mkdir()
                export = root / 'complete-export'
                export.write_text("complete export\n")
                (root / "lean/.lake/kernel-export-path").write_text(str(export) + '\n')
            trace = root / "trace"
            env = dict(os.environ, FV_DIR=directory, KERNEL_CHECKER="lake", REPLAY_TRACE=str(trace),
                       RUNNER_TEMP=directory,
                       PATH=str(root / "bin") + os.pathsep + os.environ["PATH"],
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
                elif '/external-checkers.lean ' in call:
                    command, export_path, sandbox, prefix = call.rsplit(' ', 3)
                    self.assertFalse(Path(export_path).is_relative_to(root / 'lean'))
                    calls[index] = f'{command} <export> {sandbox} {prefix}'
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
        code, calls = self.replay("kernel-external", export_exists=True, EXTERNAL_RC="23")
        self.assertEqual(code, 23)
        self.assertEqual(calls, ["env lean --print-prefix",
            f"env lean --run {CI / 'external-checkers.lean'} <export> {CI / 'kernel-bwrap.sh'} /mock/toolchain"])
        workflow = WORKFLOW.read_text()
        required = workflow.split("- name: Required Lean kernel replay and export axiom audit", 1)[1].split("- name:", 1)[0]
        external = workflow.split("- name: Bundled external checkers (advisory)", 1)[1].split("- name:", 1)[0]
        self.assertNotIn("continue-on-error: true", required)
        self.assertIn("continue-on-error: true", external)

    def test_advisory_checks_reuse_the_complete_required_export(self):
        code, calls = self.replay("kernel-external", export_exists=True, EXTERNAL_RC="23")
        self.assertEqual(code, 23)
        self.assertEqual(calls, ["env lean --print-prefix",
            f"env lean --run {CI / 'external-checkers.lean'} <export> {CI / 'kernel-bwrap.sh'} /mock/toolchain"])

    def test_missing_required_export_stops_the_advisory_replay(self):
        code, calls = self.replay("kernel-external")
        self.assertEqual(code, 2)
        self.assertEqual(calls, [])


class ExternalCheckerRunnerTests(unittest.TestCase):
    def replay(self, first_status=0, empty=False, missing=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prefix = root / 'toolchain'
            (prefix / 'bin').mkdir(parents=True)
            trace = root / 'trace'
            export = root / 'required-export.ndjson'
            if not missing:
                export.write_text('' if empty else 'retained export\n')
            for name in ('lean4lean', 'nanoda_bin', 'con-leche', 'con-ron'):
                checker = prefix / 'bin' / name
                arguments = shlex.quote(str(root / (name + '.args')))
                # Shell stubs do not need setup-python's shared-library search path.
                # Capture the real arguments and config for the assertions below.
                checker.write_text(
                    '#!/bin/sh\nset -eu\n'
                    + "printf '%s\\n' " + shlex.quote(name) + ' >> ' + shlex.quote(str(trace)) + '\n'
                    + ': > ' + arguments + '\n'
                    + 'for argument in "$@"; do\n'
                    + "  printf '%s\\000' \"$argument\" >> " + arguments + '\n'
                    + 'done\n'
                    + ('/bin/cp "$1" ' + shlex.quote(str(root / 'nanoda-config.json')) + '\n'
                       if name == 'nanoda_bin' else '')
                    + 'exit ' + str(first_status if name == 'lean4lean' else 0) + '\n')
                checker.chmod(0o755)
            sandbox = root / 'sandbox'
            sandbox.write_text('#!/bin/sh\nwhile [ "$1" != "--" ]; do shift; done\nshift\nexec "$@"\n')
            sandbox.chmod(0o755)
            result = subprocess.run(
                ['lake', 'env', 'lean', '--run', str(CI / 'external-checkers.lean'),
                 str(export), str(sandbox), str(prefix)],
                cwd=CI.parent / 'lean', env=dict(os.environ, LEAN_NUM_THREADS='2'),
                capture_output=True, text=True,
            )
            names = trace.read_text().splitlines() if trace.exists() else []
            entries = [{
                'name': name,
                'arguments': [os.fsdecode(argument)
                              for argument in (root / (name + '.args')).read_bytes().split(b'\0')[:-1]],
                'config': json.loads((root / 'nanoda-config.json').read_text()) if name == 'nanoda_bin' else None,
            } for name in names]
            return result, entries, str(export)

    def test_only_four_external_checkers_read_the_same_export(self):
        result, entries, export = self.replay()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual([entry['name'] for entry in entries],
                         ['lean4lean', 'nanoda_bin', 'con-leche', 'con-ron'])
        self.assertEqual(entries[0]['arguments'], ['--import', export])
        self.assertEqual(entries[2]['arguments'], [export])
        self.assertEqual(entries[3]['arguments'], [export])
        self.assertEqual(entries[1]['config'], {
            'use_stdin': False, 'export_file_path': export,
            'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
            'unpermitted_axiom_hard_error': False, 'num_threads': 4,
            'nat_extension': True, 'string_extension': True,
        })

    def test_rejection_does_not_skip_the_other_checkers(self):
        result, entries, _ = self.replay(first_status=17)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(len(entries), 4)
        self.assertIn('lean4lean exited with 17', result.stderr)

    def test_missing_or_empty_export_runs_no_checker(self):
        for options in ({'missing': True}, {'empty': True}):
            with self.subTest(options=options):
                result, entries, _ = self.replay(**options)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertEqual(entries, [])


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
