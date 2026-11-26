#!/usr/bin/env python3
"""Regressions for the compiled-circuit regeneration and setup-circuit comparisons."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import check_compiled_circuits as regeneration
import check_compiler_captures as captures
from check_circuit_json import imported_paths

SAMPLE = {"trace_len": 4, "layers": [{"gates": [[268435454, {"Setup": 0}]]}], "_marker": None}


class CompiledCircuitTests(unittest.TestCase):
    def test_every_imported_circuit_has_one_generator(self):
        names = [path.relative_to(regeneration.REPOSITORY).as_posix() for path in imported_paths()]
        self.assertEqual(set(regeneration.GENERATORS), set(names))
        self.assertEqual(len(regeneration.generator_tests(names)), len(names))

    def test_unmapped_circuit_fails(self):
        with self.assertRaisesRegex(ValueError, 'without a generator test'):
            regeneration.generator_tests(['absent/generated/layout.json'])

    def test_serializer_whitespace_is_not_a_difference(self):
        committed = json.dumps(SAMPLE, indent=2).encode()
        regeneration.compare_circuit('sample', json.dumps(SAMPLE).encode(), committed)

    def test_changed_value_fails(self):
        committed = json.dumps(SAMPLE, indent=2).encode()
        changed = json.loads(json.dumps(SAMPLE))
        changed["layers"][0]["gates"][0][0] = 1
        with self.assertRaisesRegex(ValueError, 'differs from the committed file'):
            regeneration.compare_circuit('sample', json.dumps(changed).encode(), committed)

    def test_changed_field_order_fails(self):
        committed = json.dumps(SAMPLE, indent=2).encode()
        reordered = json.dumps(dict(reversed(list(SAMPLE.items())))).encode()
        with self.assertRaisesRegex(ValueError, 'differs from the committed file'):
            regeneration.compare_circuit('sample', reordered, committed)

    def test_skipped_or_missing_tests_fail(self):
        regeneration.check_test_output('test result: ok. 2 passed; 0 failed', 2)
        for output in ['test result: ok. 1 passed; 0 failed',
                       'skipping cs::gkr_circuits in CI\ntest result: ok. 2 passed; 0 failed']:
            with self.subTest(output=output), self.assertRaisesRegex(ValueError, 'did not all run'):
                regeneration.check_test_output(output, 2)

    def test_setup_with_a_different_circuit_fails(self):
        setup = captures.ROOT / 'artifacts/setup/inits-and-teardowns.json'
        data = json.loads(setup.read_bytes())
        data['circuit']['trace_len'] += 1
        with tempfile.TemporaryDirectory() as directory:
            changed = Path(directory) / setup.name
            changed.write_text(json.dumps(data))
            with mock.patch.object(captures, 'setup_paths', return_value=[changed]), \
                    self.assertRaisesRegex(ValueError, 'different circuit'):
                captures.check_setup_circuits()

    def test_setup_without_a_family_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            unknown = Path(directory) / 'unknown.json'
            unknown.write_text('{}')
            with mock.patch.object(captures, 'setup_paths', return_value=[unknown]), \
                    self.assertRaisesRegex(ValueError, 'without a production circuit family'):
                captures.check_setup_circuits()


if __name__ == '__main__':
    unittest.main()
