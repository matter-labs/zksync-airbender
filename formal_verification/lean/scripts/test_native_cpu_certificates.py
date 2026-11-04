"""Reject stale finite CPU certificate domains before starting Lean compilation."""

import json
from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]


def explicit_bounds(source):
    return [int(value) for value in re.findall(
        r"simpa only \[UnifiedReduced\.constraint_count\] using \(show \w+ < (\d+) by omega\)",
        source)] + [int(value) for value in re.findall(
        r"have \w+ : \w+ < (\d+) := by simpa only \[UnifiedReduced\.constraint_count\] using bound",
        source)]


def covers_native(intervals, count):
    cursor = 0
    for lower, upper in sorted(intervals):
        if lower != cursor or upper <= lower or upper > count:
            return False
        cursor = upper
    return cursor == count


class NativeCPUCertificates(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        layout = REPO / "cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json"
        cls.count = len(json.loads(layout.read_text())["structured_statements"])

    def test_every_explicit_unified_count_matches_native(self):
        checked = 0
        for path in (ROOT / "Tests").rglob("*.lean"):
            bounds = explicit_bounds(path.read_text())
            checked += len(bounds)
            self.assertTrue(all(value == self.count for value in bounds),
                            f"{path.relative_to(ROOT)}: {bounds}; native={self.count}")
        self.assertGreater(checked, 0)

    def test_all_four_program_rows_cover_exactly_the_native_equations(self):
        source = (ROOT / "Tests/AirbenderUnifiedNative.lean").read_text()
        groups = {}
        for match in re.finditer(r"private theorem (\w+)_polynomials_(\d+)\b([\s\S]*?)(?=\nprivate theorem |\Z)", source):
            body = match[3]
            lower = re.search(r"lower : (\d+) ≤ i", body)
            upper = re.search(r"upper : i < (\d+)", body)
            self.assertIsNotNone(upper)
            groups.setdefault(match[1], []).append((int(lower[1]) if lower else 0, int(upper[1])))
        self.assertEqual(set(groups), {"lui", "addi", "sw", "lw"})
        for family, intervals in groups.items():
            self.assertTrue(covers_native(intervals, self.count), (family, intervals))

    def test_consumed_message_checks_cover_exactly_the_native_equations(self):
        source = (ROOT / "Tests/PathGConsumedMessage/Core.lean").read_text()
        intervals = []
        for match in re.finditer(r"private theorem cpu_check_(\d+)\b([\s\S]*?)(?=\nprivate theorem |\Z)", source):
            span = re.search(r"\.drop (\d+)\)\.take (\d+)\)", match[2])
            self.assertIsNotNone(span)
            lower, length = map(int, span.groups())
            self.assertEqual(int(match[1]), lower)
            intervals.append((lower, lower + length))
        self.assertTrue(covers_native(intervals, self.count), intervals)

    def test_missing_overlapping_and_outside_native_ranges_are_rejected(self):
        self.assertTrue(covers_native([(0, 16), (16, 24)], 24))
        for intervals in ([(0, 16)], [(0, 16), (15, 24)], [(0, 16), (16, 25)],
                          [(0, 16), (17, 24)], [(0, 16), (16, 16), (16, 24)]):
            self.assertFalse(covers_native(intervals, 24), intervals)
        self.assertEqual(explicit_bounds(
            "have short : i < 129 := by simpa only [UnifiedReduced.constraint_count] using bound"), [129])


if __name__ == "__main__":
    unittest.main()
