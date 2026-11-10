"""Keep complete Clean captures and their exact source obligations."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import gkr_clean_ideal as ideal


class CleanIdealTests(unittest.TestCase):
    def payload(self):
        return {'expressions': [[2, [1, 0], [0, 6]]],
                'relations': [[[1, [0]], [0, []], [6, []]]],
                'witnesses': [[[[[1, []]], 0]]], 'inputs': [[0]],
                'scopeLimit': 1, 'provenance': {'fixture': 'exact'}}

    def load(self, value):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'artifacts/compiler/numeric-clean/fixture.json'
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps(value))
            with patch.object(ideal, 'ROOT', root), \
                    patch.object(ideal, 'provenance', return_value={'fixture': 'exact'}), \
                    patch.object(ideal, 'selectors', return_value={'witnesses': [[]]}):
                return ideal.load('Fixture', 'fixture')

    def test_all_cache_modes_remain_required(self):
        self.assertEqual(len(ideal.CAPTURES), 11)
        for case in ideal.CASES:
            self.assertIn(case + 'Cached', ideal.CAPTURES)
            self.assertNotIn(case + 'Uncached', ideal.CAPTURES)

    def test_no_terms_are_normalized_or_dropped(self):
        value = self.payload()
        self.assertEqual(self.load(value), value)
        self.assertIn('(0, [])', ideal.polynomial(value['relations'][0]))

    def test_expression_tree_stays_complete(self):
        self.assertEqual(ideal.code([3, [2, [1, 4], [0, 0]], [0, 6]]),
                         '(.mul (.add (.atom 4) (.constant 0)) (.constant 6))')
        for malformed in [[4], [0, 1, 2], [1, -1], [2, [0, 1]], [3, [0, 1], [0, 2], [0, 3]]]:
            with self.subTest(value=malformed), self.assertRaises(ValueError):
                ideal.code(malformed)

    def test_one_closed_result_has_no_shards_or_heartbeat_override(self):
        modules = ideal.modules('Fixture', self.payload())
        self.assertEqual(len(modules), 2)
        certificate = modules['Airbender/Proofs/GKRProtocol/CleanIdealNative/Fixture.lean']
        self.assertEqual(certificate.count('by decide +kernel'), 1)
        self.assertNotIn('maxHeartbeats', ''.join(modules.values()))
        self.assertNotIn('CleanArithmeticNative', ''.join(modules.values()))

    def test_changed_provenance_is_rejected(self):
        value = self.payload()
        value['provenance'] = {}
        with self.assertRaises(ValueError):
            self.load(value)

    def test_incomplete_families_are_rejected(self):
        for field in ['expressions', 'witnesses', 'inputs']:
            value = self.payload()
            value[field] = []
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.load(value)

    def test_extra_fields_are_rejected(self):
        value = self.payload()
        value['unbound'] = []
        with self.assertRaises(ValueError):
            self.load(value)

    def test_trace_preserves_complete_polynomial_inputs(self):
        value = self.payload()
        with patch.object(ideal, 'TRACE_CASES', {'Fixture'}):
            traced = ideal.prepare('Fixture', value)
            self.assertEqual(traced['normalized'], [[[6, []], [1, [0]]]])
            self.assertEqual(len(traced['normalizationTraces']), 2)
            self.assertEqual(traced['normalizationTraces'][1]['input'][0], 3)
            self.assertEqual(self.load(traced), traced)

    def test_changed_trace_state_is_rejected(self):
        with patch.object(ideal, 'TRACE_CASES', {'Fixture'}):
            value = ideal.prepare('Fixture', self.payload())
            value['normalizationTraces'][0]['trace'][0][1][1] += 1
            with self.assertRaises(ValueError):
                self.load(value)

    def test_false_ideal_stops_trace_generation(self):
        value = self.payload()
        value['relations'][0][2][0] = 5
        with patch.object(ideal, 'TRACE_CASES', {'Fixture'}), self.assertRaises(ValueError):
            ideal.prepare('Fixture', value)

    def test_balanced_sizes_cover_every_row(self):
        text = ideal.table(['a', 'b', 'c', 'd'], [16, 16, 16, 3])
        self.assertEqual(text, '(.branch 32 (.branch 16 (.leaf a) (.leaf b)) (.branch 16 (.leaf c) (.leaf d)))')


if __name__ == '__main__':
    unittest.main()
