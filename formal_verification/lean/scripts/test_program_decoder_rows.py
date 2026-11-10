import copy
import hashlib
import http.client
import io
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import textwrap
import unittest
from unittest.mock import call, patch
import urllib.error

from check_program_decoder_rows import SMALL_PROGRAMS, check_group_shapes, checked_rows, csr_word
import fetch_production_program
import check_program_decoder_rows as decoder


class GuardedDecoderCaseTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.guard = self.root / 'guard.sh'
        self.guard.write_text('''fv_native() {
  printf '%s\\n' "$1" >> "$FIXTURE_ROOT/guards"
  shift
  test ! -e "$FIXTURE_ROOT/active"
  touch "$FIXTURE_ROOT/active"
  trap 'rm -f "$FIXTURE_ROOT/active"' EXIT
  if [[ "${FIXTURE_GUARD_EXIT:-0}" != 0 ]]; then return "$FIXTURE_GUARD_EXIT"; fi
  if [[ "${FIXTURE_SKIP_WORKER:-0}" == 1 ]]; then return 0; fi
  "$@"
  if [[ "${FIXTURE_INVALID_RESULT:-0}" == 1 ]]; then
    printf '{"sha256":"invalid"}\\n' > "${@: -1}"
  fi
}
''')
        self.exporter = self.root / 'exporter'
        self.exporter.write_text('#!' + sys.executable + '\n' + '''
import json, os, pathlib, sys
assert 'CI' not in os.environ and 'RUST_MIN_STACK' not in os.environ
assert (pathlib.Path(os.environ['FIXTURE_ROOT']) / 'active').exists()
if os.environ.get('FIXTURE_EXPORT_EXIT'): sys.exit(23)
family, image, text, output = sys.argv[1:5]
mask = [True] * 7 + [False, True]
count = len(pathlib.Path(text).read_bytes()) // 4
circuit = {'decode_table_columns_mask': mask, 'tables_ids_in_generic_lookups': False,
           'offset_for_decoder_table': 0, 'total_tables_size': count}
if os.environ.get('FIXTURE_CONFIG_CHANGE'):
    circuit['marker'] = int('--reduced' in sys.argv)
if os.environ.get('FIXTURE_TEXT_CHANGE'):
    circuit['marker'] = pathlib.Path(text).stem
first = 8 if os.environ.get('FIXTURE_ROW_CHANGE') else 0
artifact = {'field_modulus': 2013265921, 'trace_len': count,
            'program': {'text_words': count}, 'circuit': circuit,
            'columns': [{'blocks': [{'kind': 'dense',
                                    'values': [first] + [2013265920] * (count - 1)}]}
                        for _ in range(sum(mask))]}
pathlib.Path(output).write_text(json.dumps(artifact))
''')
        self.oracle = self.root / 'oracle'
        self.oracle.write_text('#!' + sys.executable + '\n' + '''
import os, pathlib, sys
assert 'CI' not in os.environ and 'RUST_MIN_STACK' not in os.environ
assert (pathlib.Path(os.environ['FIXTURE_ROOT']) / 'active').exists()
pathlib.Path(sys.argv[4]).write_text('0,' + ','.join(['0'] * 8) + '\\n')
''')
        self.exporter.chmod(0o755)
        self.oracle.chmod(0o755)

    def run_parent(self, options, **environment):
        command = [sys.executable, decoder.__file__, '--exporter', str(self.exporter),
                   '--oracle', str(self.oracle), '--guard-shell', str(self.guard),
                   '--families', 'add-sub', *options]
        env = dict(os.environ, FIXTURE_ROOT=str(self.root), CI='true', RUST_MIN_STACK='1',
                   **environment)
        return subprocess.run(command, env=env, text=True, capture_output=True)

    def test_each_case_owns_one_serial_guard_and_full_reduced_hashes_are_compared(self):
        options = ['--small-program', 'one', '--configs', 'full,reduced']
        result = self.run_parent(options)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('PASS 4 exact decoder row comparisons and circuit-object checks', result.stdout)
        self.assertEqual((self.root / 'guards').read_text().splitlines(), [
            f'decoder-one-{cache}-{config}-add-sub'
            for cache in ('plain', 'cached') for config in ('full', 'reduced')])
        self.assertFalse((self.root / 'active').exists())
        result = self.run_parent(options, FIXTURE_CONFIG_CHANGE='1')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('full/reduced circuit differs', result.stderr)

    def test_worker_guard_export_and_row_failures_stop_the_parent(self):
        for environment, error in [({'FIXTURE_GUARD_EXIT': '125'}, '125'),
                                   ({'FIXTURE_EXPORT_EXIT': '1'}, 'native export failed'),
                                   ({'FIXTURE_ROW_CHANGE': '1'}, 'decoder row 0'),
                                   ({'FIXTURE_SKIP_WORKER': '1'}, 'FileNotFoundError'),
                                   ({'FIXTURE_INVALID_RESULT': '1'}, 'invalid worker circuit hash')]:
            with self.subTest(environment=environment):
                (self.root / 'guards').unlink(missing_ok=True)
                result = self.run_parent(['--small-program', 'one'], **environment)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(error, result.stderr)
                self.assertEqual(len((self.root / 'guards').read_text().splitlines()), 1)
                self.assertNotIn('PASS ', result.stdout)
                self.assertFalse((self.root / 'active').exists())

    def test_circuit_independence_from_public_text_is_still_enforced(self):
        options = ['--configs', 'full', '--cache-modes', 'plain']
        for name in ('one', 'two'):
            text = self.root / (name + '.text')
            text.write_bytes(struct.pack('<I', 0x13))
            text.with_suffix('.bin').write_bytes(text.read_bytes())
            options += ['--program', str(text)]
        result = self.run_parent(options, FIXTURE_TEXT_CHANGE='1')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('circuit depends on public text', result.stderr)

    def test_complete_126_case_inventory_is_unchanged(self):
        cases = []
        def record(guard, exporter, oracle, directory, text, image, config, family, cache):
            self.assertEqual(guard, self.guard.resolve())
            cases.append((text.stem, config, family, cache))
            return 'a' * 64
        arguments = ['decoder', '--exporter', str(self.exporter), '--oracle', str(self.oracle),
                     '--guard-shell', str(self.guard)]
        with patch.object(sys, 'argv', arguments), patch.object(decoder, 'run_guarded_case', record), \
                patch('sys.stdout', new_callable=io.StringIO):
            decoder.main()
        expected = {(name, config, family, cache)
                    for name in ('one', 'two', 'muldiv', 'blake-caller')
                    for config, families in [('full', decoder.POOLED_FAMILIES),
                                             ('reduced', decoder.REDUCED_FAMILIES),
                                             ('unified', ('unified',))]
                    for family in families for cache in ('plain', 'cached')}
        expected |= {('split-keccak', 'full', 'add-sub', cache) for cache in ('plain', 'cached')}
        self.assertEqual(set(cases), expected)
        self.assertEqual(len(cases), 90)
        cases.clear()
        with patch.object(sys, 'argv', arguments + ['--committed-verifiers']), \
                patch.object(decoder, 'run_guarded_case', record), \
                patch('sys.stdout', new_callable=io.StringIO):
            decoder.main()
        repository = Path(__file__).resolve().parents[3]
        expected = {(text.stem, config, family, cache)
                    for text in (repository / 'tools/gkr_verifier').glob('fsv_*.text')
                    for config, families in [('reduced', decoder.REDUCED_FAMILIES)
                                             if text.name.startswith('fsv_unrolled_')
                                             else ('unified', ('unified',))]
                    for family in families for cache in ('plain', 'cached')}
        self.assertEqual(set(cases), expected)
        self.assertEqual(len(cases), 22)
        cases.clear()
        text = self.root / 'multiblock_batch.text'
        text.write_bytes(struct.pack('<I', 0x13))
        text.with_suffix('.bin').write_bytes(text.read_bytes())
        with patch.object(sys, 'argv', arguments + ['--program', str(text), '--configs', 'full,unified']), \
                patch.object(decoder, 'run_guarded_case', record), \
                patch('sys.stdout', new_callable=io.StringIO):
            decoder.main()
        self.assertEqual(set(cases), {
            (text.stem, config, family, cache)
            for config, families in [('full', decoder.POOLED_FAMILIES), ('unified', ('unified',))]
            for family in families for cache in ('plain', 'cached')})
        self.assertEqual(len(cases), 14)

    def test_workflow_uses_guarded_parent_without_wrapping_the_parent_in_a_guard(self):
        workflow = (Path(__file__).resolve().parents[3] /
                    '.github/workflows/formal-verification.yml').read_text()
        block = workflow.split('- name: Public program decoder row differential\n', 1)[1].split(
            '      - name:', 1)[0]
        calls = [line.strip() for line in block.splitlines()
                 if 'scripts/check_program_decoder_rows.py' in line]
        self.assertEqual(len(calls), 3)
        for line in calls:
            self.assertTrue(line.startswith('python3 scripts/check_program_decoder_rows.py --guard-shell '))
        self.assertIn('fv_stage decoder-differential 4500 ', block)
        self.assertIn('timeout-minutes: 75', block)


class ProductionProgramFetchTest(unittest.TestCase):
    payload = b'pinned production text'

    def asset(self):
        return {'name': 'multiblock_batch.text', 'size': len(self.payload),
                'sha256': hashlib.sha256(self.payload).hexdigest(),
                'url': 'https://example.invalid/pinned.text'}

    def fetch(self, root, responses):
        with patch.object(fetch_production_program.urllib.request, 'urlopen',
                          side_effect=responses) as request, \
                patch.object(fetch_production_program.time, 'sleep') as sleep, \
                patch('sys.stdout', new_callable=io.StringIO), \
                patch('sys.stderr', new_callable=io.StringIO):
            result = fetch_production_program.fetch(root, {'assets': [self.asset()]})
        return result, request, sleep

    def test_gateway_failure_and_partial_stream_retry_from_empty_temporary_files(self):
        class InterruptedStream(io.BytesIO):
            def read(self, size=-1):
                if self.tell():
                    raise http.client.IncompleteRead(b'partial')
                return super().read(3)

        gateway = urllib.error.HTTPError(self.asset()['url'], 504, 'Gateway Time-out', {}, None)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            result, request, sleep = self.fetch(
                root, [gateway, InterruptedStream(self.payload), io.BytesIO(self.payload)])
            self.assertEqual(result.read_bytes(), self.payload)
            self.assertEqual(list(root.iterdir()), [result])
            self.assertEqual(request.call_args_list,
                             [call(self.asset()['url'], timeout=60)] * 3)
            self.assertEqual(sleep.call_args_list, [call(1), call(2)])

    def test_transient_errors_exhaust_three_attempts_without_publishing(self):
        errors = [urllib.error.HTTPError(self.asset()['url'], code, 'temporary', {}, None)
                  for code in (408, 429, 500, 502, 503, 504)]
        errors += [urllib.error.URLError('connection reset'), TimeoutError('timeout'),
                   ConnectionResetError('reset')]
        for error in errors:
            with self.subTest(error=error), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                with patch.object(fetch_production_program.urllib.request, 'urlopen',
                                  side_effect=error) as request, \
                        patch.object(fetch_production_program.time, 'sleep') as sleep, \
                        patch('sys.stderr', new_callable=io.StringIO):
                    with self.assertRaises(type(error)):
                        fetch_production_program.fetch(root, {'assets': [self.asset()]})
                self.assertEqual(request.call_count, 3)
                self.assertEqual(sleep.call_args_list, [call(1), call(2)])
                self.assertEqual(list(root.iterdir()), [])

    def test_permanent_http_and_invalid_bytes_fail_without_retry(self):
        specimens = [urllib.error.HTTPError(self.asset()['url'], 404, 'missing', {}, None),
                     b'x' * len(self.payload), self.payload[:-1], self.payload + b'x']
        for specimen in specimens:
            with self.subTest(specimen=specimen), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                response = io.BytesIO(specimen) if isinstance(specimen, bytes) else specimen
                with patch.object(fetch_production_program.urllib.request, 'urlopen',
                                  side_effect=[response]) as request, \
                        patch.object(fetch_production_program.time, 'sleep') as sleep:
                    with self.assertRaises((urllib.error.HTTPError, ValueError)):
                        fetch_production_program.fetch(root, {'assets': [self.asset()]})
                self.assertEqual(request.call_count, 1)
                sleep.assert_not_called()
                self.assertEqual(list(root.iterdir()), [])

    def test_retained_assets_are_validated_without_network_or_retry(self):
        for payload in (self.payload, b'x' * len(self.payload)):
            with self.subTest(payload=payload), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                path = root / self.asset()['name']
                path.write_bytes(payload)
                with patch.object(fetch_production_program.urllib.request, 'urlopen') as request, \
                        patch.object(fetch_production_program.time, 'sleep') as sleep, \
                        patch('sys.stdout', new_callable=io.StringIO):
                    if payload == self.payload:
                        self.assertEqual(fetch_production_program.fetch(
                            root, {'assets': [self.asset()]}), path)
                    else:
                        with self.assertRaisesRegex(ValueError, 'hash differs'):
                            fetch_production_program.fetch(root, {'assets': [self.asset()]})
                request.assert_not_called()
                sleep.assert_not_called()
                self.assertEqual(path.read_bytes(), payload)


class DecoderExporterPrerequisiteTest(unittest.TestCase):
    def run_prerequisite(self, *, existing=False, build_exit=0, omit_exporter=False):
        workflow = (Path(__file__).resolve().parents[3] /
                    '.github/workflows/formal-verification.yml').read_text()
        block = workflow.split('- name: Public program decoder row differential\n', 1)[1]
        prefix = '          exporter=' + block.split('          exporter=', 1)[1].split(
            '          python3 scripts/test_program_decoder_rows.py\n', 1)[0]
        script = 'set -euo pipefail\nsource "$FV_ROOT/guard.sh"\n' + textwrap.dedent(prefix)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tools = root / 'tools'
            tools.mkdir()
            cargo = tools / 'cargo'
            cargo.write_text('''#!/bin/bash
set -euo pipefail
test "${CI+x}" != x
test "${RUST_MIN_STACK+x}" != x
printf '%s\\n' "$@" > "$FV_ROOT/cargo-call"
if [[ "$FIXTURE_BUILD_EXIT" != 0 ]]; then exit "$FIXTURE_BUILD_EXIT"; fi
if [[ "$FIXTURE_OMIT_EXPORTER" == 1 ]]; then exit 0; fi
mkdir -p "$CARGO_TARGET_DIR/debug/examples"
printf '#!/bin/sh\\nexit 0\\n' > "$CARGO_TARGET_DIR/debug/examples/export_setup_json"
chmod +x "$CARGO_TARGET_DIR/debug/examples/export_setup_json"
''')
            cargo.chmod(0o755)
            (root / 'guard.sh').write_text('''fv_native() {
  printf '%s\\n' "$@" > "$FV_ROOT/native-call"
  shift
  "$@"
}
''')
            oracle = root / '.lake/build/bin/program_rows_oracle'
            oracle.parent.mkdir(parents=True)
            oracle.write_text('#!/bin/sh\nexit 0\n')
            oracle.chmod(0o755)
            target = root / 'cargo-target'
            exporter = target / 'debug/examples/export_setup_json'
            if existing:
                exporter.parent.mkdir(parents=True)
                exporter.write_text('#!/bin/sh\nexit 0\n')
                exporter.chmod(0o755)
            env = dict(os.environ, FV_ROOT=str(root), CARGO_TARGET_DIR=str(target),
                       PATH=str(tools) + os.pathsep + os.environ['PATH'],
                       CI='true', RUST_MIN_STACK='1',
                       FIXTURE_BUILD_EXIT=str(build_exit),
                       FIXTURE_OMIT_EXPORTER='1' if omit_exporter else '0')
            result = subprocess.run(['bash', '-c', script], cwd=root, env=env,
                                    text=True, capture_output=True)
            native = (root / 'native-call').read_text().splitlines()
            self.assertEqual(native[:6], ['decoder-exporter-build', 'env', '-u', 'CI',
                                          '-u', 'RUST_MIN_STACK'])
            self.assertEqual((root / 'cargo-call').read_text().splitlines(),
                             ['build', '--locked', '--jobs', '1', '-p', 'execution_prover',
                              '--example', 'export_setup_json'])
            return result, exporter.is_file() and os.access(exporter, os.X_OK)

    def test_missing_and_restored_exporters_are_built_through_the_native_guard(self):
        for existing in (False, True):
            with self.subTest(existing=existing):
                result, executable = self.run_prerequisite(existing=existing)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertTrue(executable)

    def test_failed_build_or_absent_output_cannot_enter_the_differential(self):
        result, executable = self.run_prerequisite(build_exit=23)
        self.assertEqual(result.returncode, 23)
        self.assertFalse(executable)
        result, executable = self.run_prerequisite(omit_exporter=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(executable)


class ProgramDecoderRowsTest(unittest.TestCase):
    def setUp(self):
        sentinel = 2013265920
        self.artifact = {
            "field_modulus": 2013265921,
            "trace_len": 4,
            "program": {"text_words": 4},
            "circuit": {
                "decode_table_columns_mask": [True, True] + [False] * 7,
                "tables_ids_in_generic_lookups": False,
                "offset_for_decoder_table": 0,
                "total_tables_size": 4,
            },
            "columns": [
                {"blocks": [{"kind": "dense", "values": [0, 4]},
                            {"kind": "affine", "length": 2, "first": sentinel, "step": 0}]},
                {"blocks": [{"kind": "dense", "values": [0, 0, sentinel, sentinel]}]},
            ],
        }
        self.active = {0: [0, 0], 1: [4, 0]}

    def test_exact_active_and_sentinel_rows(self):
        checked_rows(self.artifact, self.active, "control")

    def test_changed_active_value_rejected(self):
        changed = copy.deepcopy(self.artifact)
        changed["columns"][0]["blocks"][0]["values"][1] = 8
        with self.assertRaisesRegex(ValueError, "decoder row 1"):
            checked_rows(changed, self.active, "changed active")

    def test_changed_sentinel_rejected(self):
        changed = copy.deepcopy(self.artifact)
        changed["columns"][0]["blocks"][1]["first"] = 0
        with self.assertRaisesRegex(ValueError, "non-sentinel padding"):
            checked_rows(changed, self.active, "changed sentinel")

    def test_changed_mask_rejected(self):
        with self.assertRaisesRegex(ValueError, "differs from imported Lean mask"):
            checked_rows(self.artifact, self.active, "changed mask", [True] * 9)

    def test_blake_group_shape(self):
        valid = b"".join(struct.pack("<I", word) for word in SMALL_PROGRAMS["blake-caller"])
        check_group_shapes(valid, "reduced", "valid caller")
        with self.assertRaisesRegex(ValueError, "length 1"):
            check_group_shapes(struct.pack("<II", csr_word(0x7C7), 0x13),
                               "reduced", "broken caller")

    def test_split_group_shape(self):
        words = SMALL_PROGRAMS["split-keccak"]
        check_group_shapes(b"".join(struct.pack("<I", word) for word in words),
                           "full", "valid split")
        changed = words[:8] + (csr_word(0x7CD),) + words[9:]
        with self.assertRaisesRegex(ValueError, "invalid split Keccak"):
            check_group_shapes(b"".join(struct.pack("<I", word) for word in changed),
                               "full", "broken split")


if __name__ == "__main__":
    unittest.main()
