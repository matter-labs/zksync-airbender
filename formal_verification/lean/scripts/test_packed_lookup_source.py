"""Keep both lookup-source modes, original references and complete coverage."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import gkr_packed_lookup_source as generator


class LookupSourceTests(unittest.TestCase):
    def test_complete_original_checks(self):
        expected = {
            'AddSubCached': (38, 15, 18),
            'AddSubUncached': (38, 15, 18),
            'BlakeRoundCached': (1437, 1152, 283),
            'BlakeRoundUncached': (1437, 1152, 283),
        }
        self.assertEqual(set(generator.CASES), set(expected))
        for case in generator.CASES:
            count, fields, operands = expected[case]
            rows = generator.descriptors(case)
            self.assertEqual(len(rows), count)
            self.assertEqual(sum(isinstance(row[2], tuple) for row in rows), fields)
            generated = dict(generator.modules(case))
            stem = 'Airbender.Proofs.GKRProtocol.LookupSourceChecks.' + case
            self.assertEqual(len(generated), 5)
            inputs = generated[stem + '.Inputs']
            if operands > 128:
                for first in range(0, operands, 32):
                    self.assertIn(f'phase 4 start {first} stop {min(first + 32, operands)}', inputs)
                self.assertEqual(inputs.count('import_source_lookups native'), (operands + 31) // 32)
            else:
                self.assertIn(f'phase 4 start 0 stop {operands}', inputs)
            self.assertNotIn('NumericLookupSourceChecks', inputs)
            typed = generated[stem + '.Typed']
            self.assertIn('LookupSourceNative.' + case + '.native.field', typed)
            self.assertIn('LookupNative.' + case + '.native.sourcePlacement', typed)
            self.assertIn('baseCheck', typed)
            self.assertIn('.Perm (List.range', typed)
            certificate = generated[stem + '.Certificate']
            self.assertEqual(certificate.count('theorem checked :'), 1)
            self.assertIn('check_sound originalEntries data source_binding checked', certificate)
            for name, _, predicate in rows:
                self.assertIn('theorem ' + name + ' :', certificate)
                if isinstance(predicate, tuple):
                    self.assertIn('theorem ' + predicate[2] + ' : ' + predicate[0], certificate)
                    self.assertIn('theorem ' + predicate[3] + ' : ' + predicate[1], certificate)
            self.assertNotIn('originalEntries.get', certificate)
            first = (count - 1) // 8 * 8
            self.assertIn(f'(originalEntries.drop {first}).take {count - first}', certificate)
            if operands > 128:
                self.assertEqual(inputs.count('set_option maxHeartbeats 2000000 in'), 1)
                self.assertNotIn('maxHeartbeats', ''.join(source for name, source in generated.items()
                    if name != stem + '.Inputs'))
            else:
                self.assertNotIn('maxHeartbeats', ''.join(generated.values()))
            self.assertIn(f'phase 5 start 0 stop {operands} using_checks', generator.native_wrapper(case))
            with self.assertRaisesRegex(ValueError, 'require every operand'):
                generator.command(case, 5, 1, operands)

    def test_legacy_importer_and_full_witness_stay(self):
        source = (generator.LEAN / 'Airbender/Import/GKRProtocol/LookupSourceImport.lean').read_text()
        self.assertIn('only the complete source lookup phase accepts checker facts', source)
        self.assertIn('wholeChecks.isNone', source)
        for phase in [0, 1, 2, 3]:
            self.assertIn('phase ' + str(phase), generator.command('AddSubCached', phase))
            self.assertNotIn('using_checks', generator.command('AddSubCached', phase))
        proof = (generator.LEAN / 'Airbender/Proofs/GKRProtocol/NumericLookupSourceChecks.lean').read_text()
        self.assertIn('combination relations original.witness', proof)
        self.assertIn('bank.check recipe && agreement.check sourcePlacement bank.placement', proof)

    def test_untracked_capture_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Airbender/Proofs/GKRProtocol/LookupSourceChecks/AddSubCached/Inputs.lean'
            path.parent.mkdir(parents=True)
            path.write_text('unrelated source\n')
            with patch('gkr_packed_rotate_boundary.LEAN', root), contextlib.redirect_stdout(io.StringIO()):
                with patch('sys.argv', ['gkr_packed_lookup_source.py', '--case', 'AddSubCached', '--write']):
                    with self.assertRaisesRegex(ValueError, 'untracked capture source'):generator.main()
            self.assertEqual(path.read_text(), 'unrelated source\n')


if __name__ == '__main__':unittest.main()
