"""Retain both exact erasure predicates, all fields and both cache modes."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import gkr_packed_history_erasure as generator
import gkr_history_erasure_instances as interface


class HistoryErasureTests(unittest.TestCase):
    def test_complete_source_and_exact_predicates(self):
        self.assertEqual(generator.CASES, ('AddSubCached', 'AddSubUncached'))
        for case in generator.CASES:
            generated = dict(generator.modules(case))
            stem = 'Airbender.Proofs.GKRProtocol.HistoryErasureChecks.' + case
            self.assertEqual(len(generated), 4)
            self.assertIn('phase 0', generated[stem + '.Inputs'])
            data = generated[stem + '.Data']
            for reference in ['.historyCells', '.originals', '.clock', '.protectedFields', '.helperPlacement.memory']:
                self.assertIn(reference, data)
            self.assertIn('source_binding : data = NumericHistoryErasureChecks.ofTyped ', generated[stem + '.Bindings'])
            self.assertIn('ofSource_eq', generated[stem + '.Bindings'])
            certificate = generated[stem + '.Certificate']
            self.assertIn('erasureCheck', certificate)
            self.assertIn('substitute (erasurePolynomials', certificate)
            self.assertIn('check_sound data', certificate)
            self.assertNotIn('erasureUntouched', certificate)
            self.assertEqual(certificate.count(':= by decide +kernel'), 1)
            name, _ = generator.dimensions(case)
            _, final = interface.module(name, case)
            self.assertIn('phase 1 using_check', final)
            self.assertNotIn('maxHeartbeats', final)
            self.assertNotIn('maxHeartbeats', ''.join(generated.values()))

    def test_legacy_wrapper_stays_available(self):
        with patch.object(generator, 'CASES', ()):
            _, final = interface.module('add-sub-cached', 'AddSubCached')
        self.assertNotIn('using_check', final)
        self.assertIn('import_history_erasure', final)

    def test_untracked_source_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Airbender/Proofs/GKRProtocol/HistoryErasureChecks/AddSubCached/Inputs.lean'
            path.parent.mkdir(parents=True)
            path.write_text('unrelated source\n')
            with patch('gkr_packed_rotate_boundary.LEAN', root), contextlib.redirect_stdout(io.StringIO()):
                with patch('sys.argv', ['gkr_packed_history_erasure.py', '--case', 'AddSubCached', '--write']):
                    with self.assertRaisesRegex(ValueError, 'untracked capture source'):
                        generator.main()
            self.assertEqual(path.read_text(), 'unrelated source\n')


if __name__ == '__main__':
    unittest.main()
