"""Keep complete fixed sample arrays and exact bindings in every capture."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import generate_array_samples as generator


class ArraySampleTests(unittest.TestCase):
    def test_complete_fixed_samples(self):
        self.assertEqual([(s[0],s[1],s[2],s[3]) for s in generator.SAMPLES],
                         [('subword-memory',29,1,1),('subword-memory',43,1,1),('subword-memory',43,2,1),('shift-binop',9,2,0)])
        expected=[lambda i:256*i,lambda i:i if i<128 else i+65280,lambda i:65535 if i<128 else 0,lambda i:i//8]
        for spec,formula in zip(generator.SAMPLES,expected):
            self.assertEqual(generator.values(spec),[formula(i) for i in range(256)])

    def test_numeric_checks_and_exact_bindings(self):
        modules=dict(generator.modules())
        for family,checks in [('Subword',2),('Shift',1)]:
            source=modules[f'Airbender.Proofs.Tables.{family}SampleChecks']
            self.assertNotIn('Airbender.Data.',source)
            self.assertEqual(source.count(':= by decide +kernel'),checks)
            bindings=modules[f'Airbender.Proofs.Tables.{family}SampleBindings']
            self.assertEqual(bindings.count('numeric_data_binding'),3 if family=='Subword' else 1)

    def test_untracked_data_stops_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);path=root/'Airbender/Proofs/Tables/SubwordSampleChecks.lean'
            path.parent.mkdir(parents=True);path.write_text('unrelated untracked source\n')
            with patch('gkr_packed_rotate_boundary.LEAN',root),patch('sys.argv',['generate_array_samples.py','--write']),contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,'untracked capture source'):generator.main()
            self.assertEqual(path.read_text(),'unrelated untracked source\n')


if __name__=='__main__':unittest.main()
