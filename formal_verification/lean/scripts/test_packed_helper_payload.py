"""Check complete candidate coverage and original helper phase ownership."""
import unittest
from pathlib import Path
import gkr_packed_helper_payload as packed
import gkr_helper_instances as legacy


class HelperPayload(unittest.TestCase):
    def test_complete_candidates_and_cache_modes(self):
        self.assertEqual(len(packed.CASES), 22)
        self.assertEqual(set(packed.CASES), set(packed.ALL_CASES))
        for case in packed.CASES:
            modules = dict(packed.modules(case))
            stem = 'Airbender.Proofs.GKRProtocol.HelperPayloadChecks.' + case
            self.assertEqual(len(modules), 5)
            ids = [row['native_leaf'] for row in packed.selectors(case)['operands']]
            certificate = modules[stem + '.Certificate']
            self.assertEqual(certificate.count('by decide +kernel'), 1)
            self.assertEqual(certificate.count('NumericNativePayloadChecks.checked_at'), len(ids))
            self.assertEqual(modules[stem + '.Bindings'].count('row0_source'), 2)
            self.assertIn('NumericQueryFrameChecks.complete_binding', modules[stem + '.Bindings'])
            for leaf in ids:
                self.assertIn('native.candidate' + str(leaf), modules[stem + '.Typed'])
                self.assertIn('theorem operand' + str(leaf), certificate)
            self.assertNotIn('witness := []', '\n'.join(modules.values()))

    def test_original_data_before_numeric_imports(self):
        for case in packed.CASES:
            text = packed.inputs(case)
            self.assertIn('phase 0', text)
            self.assertNotIn('NumericNativePayloadChecks', text)
            native = packed.native(case)[1]
            self.assertIn('phase 1 using_checks Airbender.Compiler.HelperPayloadChecks.' + case, native)
            self.assertNotIn('maxHeartbeats', native)
            self.assertEqual(text.count('maxHeartbeats 2000000 in'), int(case.startswith('BlakeRound')))
            self.assertEqual(list(legacy.modules(packed.capture_name(case), case)),
                             [('Airbender.Proofs.GKRProtocol.HelperPayloadChecks.' + case + '.Inputs', text), packed.native(case)])

    def test_ci_requires_all_adopted_cases(self):
        import re
        workflow = (packed.LEAN.parents[1] / '.github/workflows/formal-verification.yml').read_text()
        line = next(line for line in workflow.splitlines() if 'numeric-helper-payload-kernel-controls ' in line)
        # Default controls include every adopted case and the legacy path.
        self.assertIn('python3 scripts/check_helper_payload_controls.py', line)
        self.assertNotIn('--case', line)
        self.assertIn('numeric-helper-payload-interface python3 scripts/gkr_helper_instances.py --check', workflow)


if __name__ == '__main__':
    unittest.main()
