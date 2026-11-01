"""Keep the fixed Subword captures complete and program proofs separate."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gkr_packed_subword_prefix as generator


class FixedSubwordTests(unittest.TestCase):
    def test_complete_fixed_scope_and_closed_results(self):
        for column,count in generator.COUNTS.items():
            _,chunks,chosen=generator.capture_plan(column)
            self.assertEqual(len(chosen),count)
            for index in chosen:self.assertTrue(all(kind<5 for kind,_,_ in chunks[index][-1]))
            modules=dict(generator.modules(column))
            capture=modules[f'Airbender.Proofs.GKRProtocol.SubwordFixedChecks.Column{column}']
            self.assertEqual(capture.count('theorem checked :'),1)
            self.assertEqual(capture.count('numeric_data_binding source'),count)
            self.assertEqual(capture.count('numeric_data_binding target'),count)
            self.assertEqual(capture.count('theorem chunkChecked'),count)
            self.assertEqual(capture.count('theorem chunkLength'),count)
            self.assertNotIn('maxHeartbeats',capture)

    def test_excluded_program_proofs_remain(self):
        modules=dict(generator.modules(1))
        part0=modules['Airbender.Proofs.GKRProtocol.SubwordPrefixParts.Column1.Part0']
        part1=modules['Airbender.Proofs.GKRProtocol.SubwordPrefixParts.Column1.Part1']
        self.assertNotIn('theorem chunkChecked',part0)
        self.assertNotIn('maxHeartbeats',part0)
        self.assertEqual(part0.count('column_blocks_part original'),8)
        for index in range(12,16):self.assertIn(f'theorem chunkChecked{index}',part1)
        for index in range(8,12):self.assertNotIn(f'theorem chunkChecked{index}',part1)
        self.assertEqual(part1.count('column_blocks_part original'),8)

    def test_untracked_capture_stops_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);path=root/'Airbender/Proofs/GKRProtocol/SubwordFixedChecks/Column0.lean'
            path.parent.mkdir(parents=True);path.write_text('unrelated untracked source\n')
            with patch('gkr_packed_rotate_boundary.LEAN',root),patch('sys.argv',['gkr_packed_subword_prefix.py','--write']),contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,'untracked capture source'):generator.main()
            self.assertEqual(path.read_text(),'unrelated untracked source\n')


if __name__=='__main__':unittest.main()
