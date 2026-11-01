"""Keep complete native wiring keys and reject malformed capture data."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import gkr_packed_wiring as wiring


class WiringCaptureTests(unittest.TestCase):
    def payload(self):
        return {'producers': [8, 38], 'placements': [2, 8], 'provenance': {'fixture': 'exact'}}

    def load(self, value):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'artifacts/compiler/numeric-wiring/fixture.json'
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps(value))
            with patch.object(wiring, 'ROOT', root), patch.object(wiring, 'provenance', return_value={'fixture': 'exact'}):
                return wiring.load('fixture')

    def test_both_modes_cover_all_native_families(self):
        self.assertEqual(len(wiring.CAPTURES), 22)
        for case in wiring.CASES:
            self.assertIn(case + 'Cached', wiring.CAPTURES)
            self.assertIn(case + 'Uncached', wiring.CAPTURES)

    def test_duplicate_keys_are_retained(self):
        value = self.payload()
        value['producers'] = [8, 8, 38]
        self.assertEqual(self.load(value)['producers'], [8, 8, 38])
        data = wiring.modules('Fixture', value)['Airbender/Proofs/GKRCompiler/WiringCheckNative/FixtureData.lean']
        producer_line = next(line for line in data.splitlines() if line.startswith('def producers'))
        self.assertEqual(producer_line.count(' 8 '), 2)

    def test_invalid_keys_are_rejected(self):
        for key in [-1, True, '8', None]:
            value = self.payload()
            value['producers'] = [key]
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.load(value)

    def test_changed_provenance_is_rejected(self):
        value = self.payload()
        value['provenance'] = {}
        with self.assertRaises(ValueError):
            self.load(value)

    def test_unknown_fields_are_rejected(self):
        value = self.payload()
        value['ignored'] = [1]
        with self.assertRaises(ValueError):
            self.load(value)

    def test_one_complete_result_uses_exact_native_bindings(self):
        modules = wiring.modules('Fixture', self.payload())
        self.assertEqual(len(modules), 3)
        certificate = modules['Airbender/Proofs/GKRCompiler/WiringCheckNative/Fixture.lean']
        bindings = modules['Airbender/Proofs/GKRCompiler/WiringCheckNative/FixtureBindings.lean']
        self.assertEqual(certificate.count('by decide +kernel'), 1)
        self.assertIn('WiringChecks.check_sound', certificate)
        self.assertIn('WiringChecks.KeySort.sort', bindings)
        self.assertIn('numeric_data_binding producers_binding', bindings)
        self.assertIn('numeric_data_binding placements_binding', bindings)
        self.assertNotIn('maxHeartbeats', ''.join(modules.values()))

    def test_native_corollaries_keep_the_original_finalizer(self):
        source = wiring.native_module('Fixture', 'fixture', self.payload())
        self.assertEqual(source.count('import_compiler_wiring'), 1)
        self.assertIn('phase "certified" start 0 count 0 using', source)
        self.assertIn('theorem wiring_valid : native.graph.Valid := native.sound', source)
        self.assertNotIn('WiringParts', source)
        self.assertNotIn('maxHeartbeats', source)


if __name__ == '__main__':
    unittest.main()
