"""Retain generic, range and helper arguments in cached captures."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import gkr_packed_clean_arguments as generator
import gkr_clean_argument_instances as scalar
import gkr_clean_generic_arguments as generic


class CleanArgumentTests(unittest.TestCase):
    def test_all_three_predicate_families(self):
        self.assertEqual(generator.PILOT_CASES, ('WordMemoryCached',))
        self.assertEqual(len(set(generator.CASES)), 11)
        counts_by_stem = {
            'AddSub': (6, 8, 0), 'JumpBranch': (4, 8, 40), 'MulDiv': (8, 8, 72),
            'ShiftBinop': (2, 8, 50), 'WordMemory': (3, 8, 9), 'SubwordMemory': (5, 8, 18),
            'Unified': (13, 8, 50), 'Bigint': (32, 41, 183), 'BlakeG': (0, 21, 171),
            'BlakeRound': (0, 89, 1152), 'Keccak': (0, 30, 328),
        }
        for case in generator.CASES:
            descriptors = generator.descriptors(case)
            mode = 'cached' if case.endswith('Cached') else 'uncached'
            circuit_stem = case[:-len(mode.title())]
            counts = list(zip(['rangeChecked', 'timestampChecked', 'genericChecked'], counts_by_stem[circuit_stem]))
            self.assertEqual(len(descriptors), sum(counts_by_stem[circuit_stem]))
            for family, count in counts:
                self.assertEqual(sum(row[0].startswith(family) for row in descriptors), count)
            generated = dict(generator.modules(case))
            stem = 'Airbender.Proofs.GKRProtocol.CleanArgumentChecks.' + case
            self.assertEqual(len(generated), 5)
            self.assertNotIn('NumericCleanArgumentChecks', generated[stem + '.Inputs'])
            self.assertIn('phase 0', generated[stem + '.Inputs'])
            typed = generated[stem + '.Typed']
            self.assertIn('.placement', typed)
            self.assertIn('.bank', typed)
            self.assertIn('LookupSourceNative.', typed)
            self.assertIn('MemoryNative.', typed)
            certificate = generated[stem + '.Certificate']
            self.assertIn('check_sound originalEntries data source_binding checked', certificate)
            self.assertIn('ofNative_check', certificate)
            for fact, _, predicate in descriptors:
                self.assertIn(f'theorem {fact} : {predicate} = true', certificate)
            self.assertEqual(certificate.count('theorem checked :'), 1)
            if len(descriptors) >= 32:
                windows = (len(descriptors) + 7) // 8
                self.assertEqual(certificate.count(' := by rfl\n'), windows)
                self.assertEqual(certificate.count('NumericCleanArgumentChecks.checked_window originalChecked'), windows)
                self.assertNotIn('originalEntries.get', certificate)
                first = (len(descriptors) - 1) // 8 * 8
                self.assertIn(f'(originalEntries.drop {first}).take {len(descriptors) - first}', certificate)
            self.assertNotIn('maxHeartbeats', ''.join(generated.values()))
            family = generator.capture_name(case).removesuffix('-' + mode)
            _, scalar_source = scalar.module(family, circuit_stem, mode)
            self.assertIn('phase 1 using_checks', scalar_source)
            targets = list(generic.modules(generator.capture_name(case), case))
            self.assertEqual(len(targets), 1 if counts_by_stem[circuit_stem][2] else 0)
            if targets:
                self.assertIn('part_size 8 phase 1 using_checks', targets[0][1])

    def test_legacy_paths_stay_available(self):
        with patch.object(generator, 'CASES', ()):
            _, scalar_source = scalar.module('word-memory', 'WordMemory', 'cached')
            targets = list(generic.modules('word-memory-cached', 'WordMemoryCached'))
        self.assertNotIn('using_checks', scalar_source)
        self.assertTrue(any('CleanGenericArgumentsParts' in module for module, _ in targets))

    def test_untracked_source_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Airbender/Proofs/GKRProtocol/CleanArgumentChecks/WordMemoryCached/Inputs.lean'
            path.parent.mkdir(parents=True)
            path.write_text('unrelated source\n')
            with patch('gkr_packed_rotate_boundary.LEAN', root), contextlib.redirect_stdout(io.StringIO()):
                with patch('sys.argv', ['gkr_packed_clean_arguments.py', '--case', 'WordMemoryCached', '--write']):
                    with self.assertRaisesRegex(ValueError, 'untracked capture source'):
                        generator.main()
            self.assertEqual(path.read_text(), 'unrelated source\n')


if __name__ == '__main__':
    unittest.main()
