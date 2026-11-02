"""Retain every counter coordinate, polynomial and original semantic finalizer."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import gkr_packed_counter_frame as generator
import gkr_counter_frame_instances as interface


class CounterFrameTests(unittest.TestCase):
    def test_complete_capture_and_semantics(self):
        self.assertEqual(set(generator.CASES), {stem + mode for stem in generator.CIRCUIT_CASES
                                              for mode in ['Cached']})
        for case in generator.CASES:
            modules = dict(generator.modules(case))
            stem = 'Airbender.Proofs.GKRProtocol.CounterFrameChecks.' + case
            self.assertEqual(len(modules), 4)
            self.assertIn('phase 0', modules[stem + '.Inputs'])
            data = modules[stem + '.Data']
            for reference in ['.multiplicityColumns', '.slots', '.inputBank', '.artifact.source', '.fields', '.helperPlacement']:
                self.assertIn(reference, data)
            self.assertIn('source_binding : data = NumericCounterFrameChecks.ofTyped', modules[stem + '.Bindings'])
            self.assertIn('check_sound data', modules[stem + '.Certificate'])
            self.assertEqual(modules[stem + '.Certificate'].count(':= by decide +kernel'), 1)
            name, _, _, _ = generator.dimensions(case)
            _, final = interface.module(name, case)
            self.assertIn('phase 1 using_check', final)
            self.assertIn('theorem counter_graph_extends', final)
            self.assertIn('.source_preserved', final)
            self.assertNotIn('maxHeartbeats', final)
            self.assertNotIn('maxHeartbeats', ''.join(modules.values()))

    def test_legacy_wrapper_stays_available(self):
        with patch.object(generator, 'CASES', ()):
            _, final = interface.module('add-sub-cached', 'AddSubCached')
        self.assertNotIn('using_check', final)
        self.assertIn('import_counter_frame', final)

    def test_untracked_source_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Airbender/Proofs/GKRProtocol/CounterFrameChecks/AddSubCached/Inputs.lean'
            path.parent.mkdir(parents=True)
            path.write_text('unrelated source\n')
            with patch('gkr_packed_rotate_boundary.LEAN', root), contextlib.redirect_stdout(io.StringIO()):
                with patch('sys.argv', ['gkr_packed_counter_frame.py', '--case', 'AddSubCached', '--write']):
                    with self.assertRaisesRegex(ValueError, 'untracked capture source'):
                        generator.main()
            self.assertEqual(path.read_text(), 'unrelated source\n')


if __name__ == '__main__':
    unittest.main()
