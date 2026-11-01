"""Keep the complete seven-bit native XOR capture and public statement."""
import contextlib
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import generate_packed_xor7 as generator


class PackedXor7Tests(unittest.TestCase):
    def test_complete_native_capture(self):
        artifact=json.loads((generator.ROOT/'artifacts/setup/blake-g.json').read_text())
        blocks=generator.native_blocks(artifact)
        self.assertEqual(len(blocks),386)
        self.assertEqual(sum(map(generator.block_length,blocks)),16384)
        modules=dict(generator.modules())
        self.assertEqual(len(modules),3)
        self.assertEqual(modules[generator.BASE+'PackedCapture'].count('numeric_data_binding binding'),16)
        self.assertEqual(modules[generator.BASE+'PackedCertificate'].count('theorem checked :'),1)
        self.assertIn('theorem output7',modules[generator.BASE+'Certificate'])
        self.assertNotIn('maxHeartbeats',modules[generator.BASE+'Certificate'])

    def test_native_dimension_drift_stops(self):
        artifact=json.loads((generator.ROOT/'artifacts/setup/blake-g.json').read_text())
        next(table for table in artifact['tables'] if table['id']==19)['length']-=1
        with self.assertRaisesRegex(ValueError,'dimensions changed'):generator.native_blocks(artifact)

    def test_untracked_capture_stops_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);path=root/((generator.BASE+'PackedCapture').replace('.','/')+'.lean')
            path.parent.mkdir(parents=True);path.write_text('unrelated untracked source\n')
            with patch('gkr_packed_rotate_boundary.LEAN',root),patch('sys.argv',['generate_packed_xor7.py','--write']),contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,'untracked capture source'):generator.main()
            self.assertEqual(path.read_text(),'unrelated untracked source\n')


if __name__=='__main__':unittest.main()
