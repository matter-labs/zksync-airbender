"""Check original memory predicate coverage and both cache modes."""
import unittest
import gkr_packed_memory_payload as packed
import gkr_memory_certificate as legacy


class MemoryPayload(unittest.TestCase):
    def test_complete_original_predicates(self):
        for case in packed.CASES:
            selected = list(packed.entries(case))
            cert = packed.selectors(case)
            expected = 1 + 2 * len(cert['leaves']) + sum(
                len(group['native_leaves']) + int(group['mask'] is not None)
                for group in cert['groups'].values())
            self.assertEqual(len(selected), expected)
            modules = dict(packed.modules(case))
            stem = 'Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.' + case
            self.assertEqual(modules[stem + '.Certificate'].count('by decide +kernel'), 1)
            self.assertEqual(modules[stem + '.Certificate'].count('NumericNativePayloadChecks.checked_at'), expected)
            self.assertIn('projection_source_binding', modules[stem + '.Bindings'])
            self.assertNotIn('witness := []', '\n'.join(modules.values()))

    def test_original_data_and_cache_modes(self):
        for case in packed.CASES:
            partner = case[:-6] + 'Uncached' if case.endswith('Cached') else case[:-8] + 'Cached'
            self.assertIn(partner, packed.CASES)
            text = packed.inputs(case)
            self.assertIn('phase 0', text)
            self.assertNotIn('NumericMemoryPayloadChecks', text)
            self.assertNotIn('maxHeartbeats', packed.native(case)[1])
            self.assertEqual(list(legacy.modules(packed.capture_name(case), case)),
                [('Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.' + case + '.Inputs', text), packed.native(case)])

    def test_ci_requires_every_adopted_mode(self):
        workflow = (packed.LEAN.parents[1] / '.github/workflows/formal-verification.yml').read_text()
        line = next(line for line in workflow.splitlines() if 'numeric-memory-payload-kernel-controls ' in line)
        self.assertIn('python3 scripts/check_memory_payload_controls.py', line)
        self.assertNotIn('--case', line)


if __name__ == '__main__':
    unittest.main()
