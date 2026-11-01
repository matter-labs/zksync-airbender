"""Keep every fixed Subword region and retain program-region proofs."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gkr_packed_subword_lengths as generator
from gkr_subword_prefix import modules as consumer_modules


class SubwordLengthTests(unittest.TestCase):
    def test_complete_fixed_scope(self):
        self.assertEqual(generator.COLUMNS,tuple(range(9)))
        for column in generator.COLUMNS:
            entries=generator.metadata_plan(column)
            self.assertEqual([entry['table'] for entry in entries],[0,29,30,42,43])
            modules=dict(generator.modules(column));stem=f'Airbender.Proofs.GKRProtocol.SubwordRegionLengths.Column{column}'
            self.assertEqual(modules[stem+'.Certificate'].count('theorem checked :'),1)
            self.assertEqual(modules[stem+'.Bindings'].count('numeric_data_binding'),5)
            self.assertEqual(modules[stem].count('theorem length'),5)
            for table in [44,45]:self.assertNotIn(f' := region {table} ',modules[stem+'.Data'])

    def test_native_consumers_retain_program_proofs(self):
        for column in generator.COLUMNS:
            native=list(consumer_modules(column))[-1][1]
            self.assertEqual(native.count(f'Airbender.Compiler.SubwordRegionLengths.Column{column}.length'),5)
            for region in [5,6]:
                statement=next(line for line in native.splitlines() if line.startswith(f'theorem regionLength{region} '))
                self.assertTrue(statement.endswith(':= by decide +kernel'))

    def test_untracked_data_stops_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);path=root/'Airbender/Proofs/GKRProtocol/SubwordRegionLengths/Column0/Data.lean'
            path.parent.mkdir(parents=True);path.write_text('unrelated untracked source\n')
            with patch('gkr_packed_rotate_boundary.LEAN',root),patch('sys.argv',['gkr_packed_subword_lengths.py','--column','0','--write']),contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,'untracked capture source'):generator.main()
            self.assertEqual(path.read_text(),'unrelated untracked source\n')


if __name__=='__main__':unittest.main()
