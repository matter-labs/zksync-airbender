"""Retain generic, range and helper arguments in both native cache modes."""
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
        self.assertEqual(generator.PILOT_CASES, ('WordMemoryCached', 'WordMemoryUncached'))
        for case in generator.CASES:
            descriptors = generator.descriptors(case)
            dense = case.startswith('BlakeRound')
            counts = [('rangeChecked', 0), ('timestampChecked', 89), ('genericChecked', 1152)] if dense else [
                ('rangeChecked', 3), ('timestampChecked', 8), ('genericChecked', 9)]
            self.assertEqual(len(descriptors), 1241 if dense else 20)
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
            if dense:
                self.assertEqual(certificate.count(' := by rfl\n'), 156)
                self.assertEqual(certificate.count('NumericCleanArgumentChecks.checked_window originalChecked'), 156)
                self.assertNotIn('originalEntries.get', certificate)
                self.assertIn('(originalEntries.drop 1240).take 1', certificate)
            self.assertNotIn('maxHeartbeats', ''.join(generated.values()))
            _, scalar_source = scalar.module('blake-round' if dense else 'word-memory',
                'BlakeRound' if dense else 'WordMemory', 'cached' if case.endswith('Cached') else 'uncached')
            self.assertIn('phase 1 using_checks', scalar_source)
            targets = list(generic.modules(generator.capture_name(case), case))
            self.assertEqual(len(targets), 1)
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
