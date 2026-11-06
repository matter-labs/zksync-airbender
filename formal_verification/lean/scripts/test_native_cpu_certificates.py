"""Reject stale native certificate and runtime expectations before Lean compilation."""

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


def missing_artifact_imports(source):
    """Find runtime artifact references absent from its project import closure."""
    imports = lambda text: re.findall(r"^import\s+([\w.]+)", text, re.M)
    pending = imports(source)
    reachable = set()
    while pending:
        module = pending.pop()
        if module in reachable:
            continue
        reachable.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        if path.is_file():
            pending.extend(imports(path.read_text()))
    referenced = set(re.findall(r"\b(\w+)\.importedConstraints\w*", source))
    return {name for name in referenced
            if f"Airbender.Review.Circuits.{name}.Artifact" not in reachable}


class NativeCPUCertificates(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        layout = REPO / "cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json"
        cls.layout = json.loads(layout.read_text())
        cls.count = len(cls.layout["structured_statements"])

    def test_consumed_message_transport_checks_every_native_pooled_tag(self):
        placement = {json.dumps(arg, sort_keys=True): int(column)
                     for column, arg in self.layout["placement_data"].items()}
        tags = []
        for query in self.layout["generic_lookups"]:
            tag = query["columns"][-1]
            self.assertEqual(tag["constant"], 0)
            self.assertEqual(len(tag["linear_terms"]), 1)
            coefficient, arg = tag["linear_terms"][0]
            self.assertEqual(coefficient, (1 << 32) % 2013265921)
            if "ScratchSpace" in arg:
                arg = self.layout["scratch_space_mapping_rev"][str(arg["ScratchSpace"])]
            tags.append(placement[json.dumps(arg, sort_keys=True)])
        source = (ROOT / "Tests/PathGConsumedMessage/Core.lean").read_text()
        contracts = []
        for match in re.finditer(r"private theorem cpu_(?:tags|query_transport)\b([\s\S]*?)(?=\nprivate theorem |\Z)", source):
            explicit = re.search(r"\(\[([\d, ]+)\] : List Nat\)", match[1])
            self.assertIsNotNone(explicit)
            contracts.append([int(value) for value in explicit[1].split(",")])
        self.assertEqual(contracts, [tags, tags])
        self.assertEqual([int(value) for value in re.findall(r"using tags (\d+) \(by decide\)", source)], tags)

    def test_consumed_message_store_and_stencil_use_native_word_address_column(self):
        word = self.layout["range_check_16_lookup_expressions"][0]["input"]
        self.assertEqual(word["constant"], 0)
        self.assertEqual(len(word["linear_terms"]), 1)
        coefficient, arg = word["linear_terms"][0]
        self.assertEqual(coefficient, (1 << 32) % 2013265921)
        if "ScratchSpace" in arg:
            arg = self.layout["scratch_space_mapping_rev"][str(arg["ScratchSpace"])]
        placement = {json.dumps(value, sort_keys=True): int(column)
                     for column, value in self.layout["placement_data"].items()}
        column = placement[json.dumps(arg, sort_keys=True)]
        for filename, name in (("Data", "cpuStoreAssignment"), ("Native", "newStoreStencil")):
            source = (ROOT / f"Tests/PathGConsumedMessage/{filename}.lean").read_text()
            body = re.search(r"(?:private )?def " + name + r"\b([\s\S]*?)(?=\n(?:private )?(?:def|theorem) |\Z)", source)
            self.assertIsNotNone(body)
            indices = re.findall(r"else if column = (\d+) then 24\b", body[1])
            self.assertEqual(indices, [str(column)], name)

    def test_shift_query_projection_matches_native_pooled_columns(self):
        placement = {json.dumps(arg, sort_keys=True): int(column)
                     for column, arg in self.layout["placement_data"].items()}
        columns = []
        for query in self.layout["generic_lookups"]:
            row = []
            for expression in query["columns"]:
                self.assertEqual(expression["constant"], 0)
                terms = expression["linear_terms"]
                if not terms:
                    row.append(None)
                    continue
                self.assertEqual(len(terms), 1)
                coefficient, arg = terms[0]
                self.assertEqual(coefficient, (1 << 32) % 2013265921)
                if "ScratchSpace" in arg:
                    arg = self.layout["scratch_space_mapping_rev"][str(arg["ScratchSpace"])]
                row.append(placement[json.dumps(arg, sort_keys=True)])
            columns.append(row)
        source = (ROOT / "Tests/UnifiedShift.lean").read_text()
        body = source.split("private def queryValues ", 1)[1].split("\nprivate theorem ", 1)[0]
        literals = [int(value) for value in re.findall(r"assignment kind (\d+)", body)]
        self.assertEqual(literals, columns[0][:3] + columns[0][-1:])
        self.assertEqual(columns[0][3:9], [None] * 6)
        base = re.search(r"base := (\d+) \+ (\d+) \* \(slot.val - 1\)", body)
        self.assertIsNotNone(base)
        start, stride = map(int, base.groups())
        for slot, row in enumerate(columns[1:]):
            tag = start + stride * slot
            self.assertEqual(row, list(range(tag + 1, tag + 9)) + [None, tag])

    def test_every_explicit_unified_count_matches_native(self):
        checked = 0
        for path in (ROOT / "Tests").rglob("*.lean"):
            bounds = explicit_bounds(path.read_text())
            checked += len(bounds)
            self.assertTrue(all(value == self.count for value in bounds),
                            f"{path.relative_to(ROOT)}: {bounds}; native={self.count}")
        self.assertGreater(checked, 0)

    def test_runtime_importer_metadata_matches_native_artifacts(self):
        source = (ROOT / "Tests/ArtifactImport.lean").read_text()
        paths = dict(re.findall(r'let\s+(\w+)\s+←\s+IO\.FS\.readFile\s+"([^"]+)"', source))
        circuits = {name: json.loads((ROOT / paths[data]).read_text())
                    for name, data in re.findall(r"let\s+\.ok\s+(\w+)\s*:=\s*parseCircuit\s+(\w+)", source)
                    if data in paths}
        self.assertGreaterEqual(len(circuits), 9)
        fields = {"structured_statements", "range_check_16_lookup_expressions",
                  "timestamp_range_check_lookup_expressions", "generic_lookups", "layers"}
        checked = 0
        for name, circuit in circuits.items():
            for field, expected in re.findall(r"\b" + re.escape(name) + r"\.(\w+)\.size\s*==\s*(\d+)", source):
                if field in fields:
                    checked += 1
                    with self.subTest(circuit=name, field=field):
                        self.assertEqual(int(expected), len(circuit[field]))
        for query, name, method in re.findall(r"let\s+\.ok\s+(\w+)\s*:=\s*(\w+)\.(\w+)", source):
            if name not in circuits:
                continue
            field = ("range_check_16_lookup_expressions" if method == "range16Expressions"
                     else "generic_lookups" if method.endswith("Queries") else None)
            if field:
                for expected in re.findall(r"\b" + re.escape(query) + r"\.size\s*==\s*(\d+)", source):
                    checked += 1
                    with self.subTest(circuit=name, query=query):
                        self.assertEqual(int(expected), len(circuits[name][field]))
        self.assertGreaterEqual(checked, 23)

    def test_runtime_importer_can_reach_every_referenced_artifact(self):
        source = (ROOT / "Tests/ArtifactImport.lean").read_text()
        self.assertEqual(missing_artifact_imports(source), set())
        missing_mul_div = source.replace(
            "import Airbender.Review.Circuits.MulDiv.Artifact\n", "")
        self.assertEqual(missing_artifact_imports(missing_mul_div), {"MulDiv"})

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
