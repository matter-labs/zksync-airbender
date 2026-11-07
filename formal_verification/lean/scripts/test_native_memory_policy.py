"""Native budget qualification controls; no native processes or Lean builds."""
from pathlib import Path
import tempfile
import unittest

import qualify_native_memory as policy


class NativeMemoryPolicy(unittest.TestCase):
    def test_host_capacity_and_current_available_memory_are_required(self):
        self.assertTrue(policy.qualify(32 * 1024 * policy.MIB, 20 * 1024 * policy.MIB)['qualified'])
        self.assertFalse(policy.qualify(8 * 1024 * policy.MIB, 8 * 1024 * policy.MIB)['qualified'])
        self.assertFalse(policy.qualify(32 * 1024 * policy.MIB, 10 * 1024 * policy.MIB)['qualified'])

    def test_cgroup_limits_and_current_usage_cannot_be_hidden_by_host_ram(self):
        host = 64 * 1024 * policy.MIB
        self.assertFalse(policy.qualify(host, host, [(8 * 1024 * policy.MIB, 0)])['qualified'])
        self.assertFalse(policy.qualify(host, host, [(16 * 1024 * policy.MIB, 4 * 1024 * policy.MIB)])['qualified'])
        self.assertTrue(policy.qualify(host, host, [(24 * 1024 * policy.MIB, 4 * 1024 * policy.MIB)])['qualified'])

    def test_visible_parent_cgroup_limit_is_enforced(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            proc, group = root / 'proc', root / 'cgroup'
            (proc / 'self').mkdir(parents=True)
            (group / 'parent/job').mkdir(parents=True)
            (proc / 'meminfo').write_text('MemTotal: 67108864 kB\nMemAvailable: 52428800 kB\n')
            (proc / 'self/cgroup').write_text('0::/parent/job\n')
            (group / 'memory.max').write_text('max\n')
            (group / 'parent/memory.max').write_text(str(8 * 1024 * policy.MIB))
            (group / 'parent/memory.current').write_text('0\n')
            self.assertFalse(policy.inspect(proc, group)['qualified'])

    def test_report_keeps_lean_limits_separate(self):
        report = policy.qualify(64 * 1024 * policy.MIB, 32 * 1024 * policy.MIB)
        self.assertEqual((report['lean_footprint_mib'], report['lean_resident_mib']), (2560, 5120))
        self.assertEqual((report['native_footprint_mib'], report['native_resident_mib']), (8192, 12288))

    def test_restored_inactive_file_cache_can_be_reclaimed(self):
        host = 64 * 1024 * policy.MIB
        limit, used, cache = [value * 1024 * policy.MIB for value in (16, 6, 4)]
        self.assertTrue(policy.qualify(host, host, [(limit, used, cache)])['qualified'])
        self.assertFalse(policy.qualify(host, host, [(limit, used, 0)])['qualified'])


if __name__ == '__main__':
    unittest.main()
