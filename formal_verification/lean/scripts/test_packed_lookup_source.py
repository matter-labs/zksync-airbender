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
        self.assertEqual(generator.CASES, ('AddSubCached', 'AddSubUncached'))
        for case in generator.CASES:
            rows = generator.descriptors(case)
            self.assertEqual(len(rows), 38)
            self.assertEqual(sum(isinstance(row[2], tuple) for row in rows), 15)
            generated = dict(generator.modules(case))
            stem = 'Airbender.Proofs.GKRProtocol.LookupSourceChecks.' + case
            self.assertEqual(len(generated), 5)
            inputs = generated[stem + '.Inputs']
            self.assertIn('phase 4 start 0 stop 18', inputs)
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
            self.assertIn('(originalEntries.drop 32).take 6', certificate)
            self.assertNotIn('maxHeartbeats', ''.join(generated.values()))
            self.assertIn('phase 5 start 0 stop 18 using_checks', generator.native_wrapper(case))

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
