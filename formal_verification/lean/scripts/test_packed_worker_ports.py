"""Check source fidelity, complete captures and stale dimension rejection."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gkr_packed_worker_ports as packed


class WorkerPorts(unittest.TestCase):
    def test_both_modes_and_complete_result(self):
        self.assertEqual(len(packed.CASES),4)
        for case in packed.CASES:
            modules=dict(packed.modules(case))
            self.assertEqual(len(modules),5)
            certificate=modules['Airbender.Proofs.GKRProtocol.WorkerPortChecks.'+case+'.Certificate']
            self.assertEqual(certificate.count('by decide +kernel'),1)
            bindings=modules['Airbender.Proofs.GKRProtocol.WorkerPortChecks.'+case+'.Bindings']
            self.assertIn('congrArg₂ NumericWorkerPortChecks.Data.mk columns_binding bounds_binding',bindings)
            self.assertEqual(bindings.count('NumericQueryFrameChecks.complete_binding'),2)
            self.assertNotIn('set_option maxHeartbeats',bindings)

    def test_exact_original_values_and_token_proofs(self):
        for case in packed.CASES:
            family,mode,_=packed.identity(case)
            _,old=packed.legacy.module(family,mode)
            inputs=packed.input_text(case)
            _,native=packed.native(case)
            for name in ['originalIndices','logicalValues']:
                self.assertIn(packed.block(old,name),inputs)
            for first,last in [('source_read_tokens','original_assignment'),('row_token_from_base','read_tokens_from_base')]:
                fragment=old[old.index('theorem '+first):old.index('theorem '+last)]
                self.assertIn(fragment,native)
            self.assertIn('WorkerPortChecks.'+case+'.facts.1.1',native)

    def test_stale_dimensions_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'dimensions.json'
            values=json.loads(packed.DIMENSIONS.read_text())
            values[packed.CASES[0]]['source_sha256']='0'*64
            path.write_text(json.dumps(values))
            with patch.object(packed,'DIMENSIONS',path):
                with self.assertRaisesRegex(ValueError,'refresh worker source dimensions'):
                    list(packed.modules(packed.CASES[0]))


if __name__=='__main__':unittest.main()
