"""Keep the remaining fixed captures within their complete native scopes."""
import unittest
from unittest.mock import patch
import gkr_packed_fixed_captures as generator


class PackedFixedCaptureTests(unittest.TestCase):
    def test_complete_fixed_scopes_exclude_program_rom(self):
        expected = {
            4: ([[128, 24320], [24448, 25472]], 197, [9, 47, 48]),
            6: ([[128, 24192]], 188, [9]),
            7: ([[128, 24576]], 191, [9]),
        }
        for column, (spans, count, ids) in expected.items():
            with self.subTest(column=column):
                _, actual, targets, checks = generator.capture_plan(column)
                self.assertEqual(actual, spans)
                self.assertEqual(len(checks), count)
                self.assertEqual([target[0] for target in targets], ids)
                self.assertEqual(sum(item[1] for item in checks), count * 128)

    def test_each_capture_has_one_closed_kernel_result(self):
        for column in generator.COLUMNS:
            with self.subTest(column=column):
                modules = dict(generator.modules(column))
                self.assertEqual(set(modules), {'Codes', 'Bindings', 'Certificate'})
                certificate = modules['Certificate']
                self.assertEqual(certificate.count('theorem ok :'), 1)
                self.assertIn('checkTreeWithChunks sourceTree targetTree lengthChecks', certificate)
                self.assertIn('decide +kernel', certificate)
                self.assertNotIn('maxHeartbeats', certificate)
                self.assertNotIn('column_blocks_part', certificate)

    def test_program_region_stops_generation(self):
        artifact, *rest = generator.plans(6)
        artifact['tables'][6]['id'] = 34
        with patch.object(generator, 'plans', return_value=(artifact, *rest)):
            with self.assertRaisesRegex(ValueError, 'unexpected region'):
                list(generator.modules(6))


if __name__ == '__main__':
    unittest.main()
