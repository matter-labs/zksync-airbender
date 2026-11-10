"""Check complete source bindings, exact references and legacy preservation."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gkr_packed_helper_validity as packed


class HelperValidity(unittest.TestCase):
    def test_complete_capture_and_both_modes(self):
        self.assertEqual(len(packed.CASES),11)
        for case in packed.CASES:
            modules=dict(packed.modules(case));self.assertEqual(len(modules),5)
            prefix='Airbender.Proofs.GKRProtocol.HelperValidityChecks.'+case
            self.assertEqual(modules[prefix+'.Certificate'].count('by decide +kernel'),1)
            binding=modules[prefix+'.Bindings']
            self.assertEqual(binding.count('NumericQueryFrameChecks.complete_binding'),3)
            self.assertIn('capture_eq data original coordinates_binding borrowBound_binding',binding)
            self.assertNotIn('set_option maxHeartbeats',binding)
            self.assertIn('phase 0',modules[prefix+'.Inputs'])
            self.assertNotIn('NumericHelperValidity',modules[prefix+'.Inputs'])

    def test_exact_semantic_finalizer_and_phase_order(self):
        for case in packed.CASES:
            source=packed.original(case);native=packed.native(case)[1]
            self.assertIn(source[source.index('theorem helper_graph_extends'):],native)
            self.assertIn('phase 1 using_checks Airbender.Compiler.HelperValidityChecks.'+case,native)
            self.assertNotIn('maxHeartbeats',native)

    def test_stale_source_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'dimensions.json';entries=json.loads(packed.DIMENSIONS.read_text());entries[packed.CASES[0]]['source_sha256']='0'*64;path.write_text(json.dumps(entries))
            with patch.object(packed,'DIMENSIONS',path):
                with self.assertRaisesRegex(ValueError,'refresh helper source dimensions'):list(packed.modules(packed.CASES[0]))


if __name__=='__main__':unittest.main()
