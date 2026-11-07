"""Keep both complete fixed sample captures and exact native bindings."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import generate_aligned_samples as generator


class AlignedSampleTests(unittest.TestCase):
    def test_complete_fixed_scope(self):
        self.assertEqual([(c[0],c[1],c[2],c[3],c[4]) for c in generator.CAPTURES],
                         [('conditional','jump-branch',31,1,128),('position','shift-binop',9,0,8)])
        self.assertEqual([generator.block_count(c[1],c[2],c[3]) for c in generator.CAPTURES],[47,4])

    def test_one_closed_check_and_binding_per_capture(self):
        modules=dict(generator.modules());stem=generator.STEM
        self.assertEqual(modules[stem+'.Certificate'].count(':= by decide +kernel'),2)
        self.assertEqual(modules[stem+'.Bindings'].count('numeric_data_binding'),2)
        self.assertEqual(modules[stem+'.Data'].count(' := region '),2)
        for capture in generator.CAPTURES:
            self.assertIn(f'def {capture[0]} : Request',modules[stem+'.Data'])

    def test_untracked_data_stops_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);path=root/'Airbender/Proofs/Tables/AlignedSampleChecks/Data.lean'
            path.parent.mkdir(parents=True);path.write_text('unrelated untracked source\n')
            with patch('gkr_packed_rotate_boundary.LEAN',root),patch('sys.argv',['generate_aligned_samples.py','--write']),contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,'untracked capture source'):generator.main()
            self.assertEqual(path.read_text(),'unrelated untracked source\n')


if __name__=='__main__':unittest.main()
