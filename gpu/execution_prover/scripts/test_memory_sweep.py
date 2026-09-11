#!/usr/bin/env python3
"""CPU-only regression tests for memory_sweep.py (no binary, no GPU).

    python3 gpu/execution_prover/scripts/test_memory_sweep.py
"""

import csv
import io
import json
import sys
import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import memory_sweep as ms  # noqa: E402

GIB = ms.GIB
CIRCUITS = [ms.BIGINT, "unrolled_unified", "unrolled_non_memory_add_sub_lui_auipc_mop"]
CONFIGS = ["cfg_a", "cfg_b"]
FIELDS = ["arena_bytes", "circuit", "configuration", "geometry", "setup", "witness_commitment",
          "witness_opening", "memory", "failure_stage", "raw_samples_ms", "proof_fingerprint", "fits",
          "input_bytes", "peak_bytes", "timing_samples", "median_ms", "min_ms", "max_ms", "preferred"]


def row(budget, circuit, configuration, fits=True, samples=(3.0, 1.0, 2.0, 5.0, 4.0), **overrides):
    """A valid runner row; `overrides` corrupt individual fields for negative tests."""
    values = dict.fromkeys(FIELDS, "")
    values.update(arena_bytes=str(budget), circuit=circuit, configuration=configuration, geometry="{}",
                  setup="full", witness_commitment="full", witness_opening="full", memory="full",
                  fits="true" if fits else "false", input_bytes="100", preferred="false")
    if fits:
        median, low, high = ms.summary_of(list(samples))
        values.update(raw_samples_ms=json.dumps(list(samples)), proof_fingerprint="12345",
                      peak_bytes=str(budget - 1), timing_samples=str(len(samples)),
                      median_ms=repr(median), min_ms=repr(low), max_ms=repr(high))
    else:
        values.update(raw_samples_ms="[]", failure_stage="target_with_largest_follower")
    values.update(overrides)
    return values


def full_rows(budget, circuit, fits=(True, True)):
    return [row(budget, circuit, cfg, fits=fit) for cfg, fit in zip(CONFIGS, fits)]


class ResourceSnapshot(unittest.TestCase):
    def test_only_successful_empty_process_census_is_idle(self):
        self.assertFalse(ms.compute_apps_present({"compute_apps": "pid, process_name, used_gpu_memory [MiB]\n"}))
        for census in ("", "<unavailable: error>", "unexpected response", "pid, process_name\n123, prover"):
            self.assertTrue(ms.compute_apps_present({"compute_apps": census}))


class GibLabel(unittest.TestCase):
    def test_exact_labels_round_trip(self):
        for budget in (16 * GIB, 31 * GIB + GIB // 2, 20 * GIB + ms.MIB, 17 * GIB + 3 * ms.MIB):
            label = ms.gib_label(budget)
            self.assertEqual(ms.parse_budget_gib(label), budget)
        self.assertEqual(ms.gib_label(48 * GIB), "48")
        self.assertEqual(ms.gib_label(31 * GIB + GIB // 2), "31.5")
        self.assertEqual(ms.gib_label(ms.MIB), "0.0009765625")

    def test_rejects_non_mib_budgets(self):
        with self.assertRaises(ValueError):
            ms.gib_label(GIB + 1)


class TimingValidity(unittest.TestCase):
    def check(self, expected_problem, **overrides):
        problems = ms.row_problems(row(32 * GIB, CIRCUITS[0], "cfg_a", **overrides), 32 * GIB, 5, False)
        self.assertTrue(any(expected_problem in p for p in problems), problems)

    def test_valid_row_has_no_problems(self):
        self.assertEqual(ms.row_problems(row(32 * GIB, CIRCUITS[0], "cfg_a"), 32 * GIB, 5, False), [])

    def test_missing_timing(self):
        self.check("raw samples", raw_samples_ms="[]", timing_samples="0", median_ms="")

    def test_incomplete_rounds(self):
        self.check("exactly 5", raw_samples_ms="[1.0,2.0,3.0]", timing_samples="3")

    def test_nonfinite_or_nonpositive_samples(self):
        self.check("finite and positive", raw_samples_ms="[1.0,2.0,3.0,4.0,0.0]")
        self.check("finite and positive", raw_samples_ms='[1.0,2.0,3.0,4.0,"nan"]')

    def test_summary_disagreement(self):
        self.check("disagree", median_ms="9.0")

    def test_missing_fingerprint_and_peak(self):
        self.check("fingerprint", proof_fingerprint="")
        self.check("peak_bytes exceeds", peak_bytes=str(32 * GIB + 1))
        self.check("lacks peak_bytes", peak_bytes="")

    def test_failure_stage_on_fitting_row(self):
        self.check("failure stage", failure_stage="setup_init:x")

    def test_non_fitting_row_with_timing_is_invalid(self):
        stale = row(32 * GIB, CIRCUITS[0], "cfg_a")
        stale["fits"] = "false"
        problems = ms.row_problems(stale, 32 * GIB, 5, False)
        self.assertTrue(any("non-fitting row carries timing" in p for p in problems), problems)

    def test_arena_mismatch(self):
        self.assertTrue(ms.row_problems(row(32 * GIB, CIRCUITS[0], "cfg_a"), 34 * GIB, 5, False))

    def test_fit_only_needs_no_timing(self):
        untimed = row(32 * GIB, CIRCUITS[0], "cfg_a", raw_samples_ms="[]", timing_samples="0",
                      median_ms="", min_ms="", max_ms="")
        self.assertEqual(ms.row_problems(untimed, 32 * GIB, 5, True), [])
        self.assertTrue(ms.row_problems(untimed, 32 * GIB, 5, False))


class RowSetCompleteness(unittest.TestCase):
    def test_one_row_per_configuration(self):
        rows = full_rows(32 * GIB, CIRCUITS[0])
        self.assertEqual(ms.validate_rows(rows, 32 * GIB, CIRCUITS[0], CONFIGS, 5, False), [])
        self.assertTrue(ms.validate_rows(rows[:1], 32 * GIB, CIRCUITS[0], CONFIGS, 5, False))
        self.assertTrue(ms.validate_rows(rows + rows[:1], 32 * GIB, CIRCUITS[0], CONFIGS, 5, False))

    def test_incomplete_timing_is_not_complete(self):
        rows = full_rows(32 * GIB, CIRCUITS[0])
        rows[0]["timing_samples"] = "2"
        rows[0]["raw_samples_ms"] = "[1.0,2.0]"
        self.assertTrue(ms.validate_rows(rows, 32 * GIB, CIRCUITS[0], CONFIGS, 5, False))


class Qualification(unittest.TestCase):
    def verdict(self, rows_by_circuit, fit_only=False, full=True):
        return ms.qualify(rows_by_circuit, CIRCUITS, 5, fit_only, full)

    def test_all_circuits_fit_is_accepted_with_winners(self):
        rows = {c: full_rows(32 * GIB, c) for c in CIRCUITS}
        rows[CIRCUITS[1]][1]["median_ms"] = "0.5"
        rows[CIRCUITS[1]][1]["min_ms"] = "0.1"
        rows[CIRCUITS[1]][1]["max_ms"] = "0.9"
        rows[CIRCUITS[1]][1]["raw_samples_ms"] = "[0.1,0.3,0.5,0.7,0.9]"
        verdict = self.verdict(rows)
        self.assertEqual(verdict["status"], "accepted")
        self.assertEqual(verdict["winners"][CIRCUITS[1]], "cfg_b")
        self.assertEqual(verdict["winners"][CIRCUITS[0]], "cfg_a")  # tie -> name

    def test_any_circuit_without_fit_rejects(self):
        rows = {c: full_rows(32 * GIB, c) for c in CIRCUITS}
        rows[CIRCUITS[2]] = full_rows(32 * GIB, CIRCUITS[2], fits=(False, False))
        verdict = self.verdict(rows)
        self.assertEqual(verdict["status"], "rejected")
        self.assertIn(CIRCUITS[2], verdict["reason"])

    def test_bigint_rejection_with_others_missing(self):
        rows = {CIRCUITS[0]: full_rows(32 * GIB, CIRCUITS[0], fits=(False, False))}
        self.assertEqual(self.verdict(rows)["status"], "rejected")

    def test_missing_run_is_incomplete_not_accepted(self):
        rows = {c: full_rows(32 * GIB, c) for c in CIRCUITS[:2]}
        self.assertEqual(self.verdict(rows)["status"], "incomplete")

    def test_restricted_set_is_partial(self):
        rows = {c: full_rows(32 * GIB, c) for c in CIRCUITS}
        self.assertEqual(self.verdict(rows, full=False)["status"], "partial")

    def test_fit_only_records_every_circuit_without_presets(self):
        rows = {c: full_rows(32 * GIB, c) for c in CIRCUITS}
        rows[CIRCUITS[1]] = full_rows(32 * GIB, CIRCUITS[1], fits=(False, False))
        verdict = self.verdict(rows, fit_only=True)
        self.assertEqual(verdict["status"], "fit_only")
        self.assertEqual(verdict["fits"], {CIRCUITS[0]: True, CIRCUITS[1]: False, CIRCUITS[2]: True})
        self.assertEqual(verdict["winners"], {})

    def test_untimed_fit_never_qualifies_a_timed_sweep(self):
        rows = {c: full_rows(32 * GIB, c) for c in CIRCUITS}
        for r in rows[CIRCUITS[0]]:
            r.update(raw_samples_ms="[]", timing_samples="0", median_ms="", min_ms="", max_ms="")
        self.assertEqual(self.verdict(rows)["status"], "rejected")


class Refinement(unittest.TestCase):
    def test_boundary_and_winner_change_points(self):
        coarse = {34 * GIB, 32 * GIB, 30 * GIB, 28 * GIB}
        state = {
            34 * GIB: {"status": "accepted", "winners": {"a": "x"}},
            32 * GIB: {"status": "accepted", "winners": {"a": "y"}},
            30 * GIB: {"status": "rejected", "winners": {}},
            28 * GIB: {"status": "rejected", "winners": {}},
        }
        plan = dict(ms.refinement_candidates(state, coarse))
        self.assertEqual(set(plan), {34 * GIB, 32 * GIB})
        self.assertEqual(plan[32 * GIB], [32 * GIB - GIB // 2, 31 * GIB, 30 * GIB + GIB // 2])
        state[32 * GIB]["winners"] = {"a": "x"}
        self.assertEqual(set(dict(ms.refinement_candidates(state, coarse))), {32 * GIB})


class ResumeValidation(unittest.TestCase):
    """completed_rows must reject partial or altered CSVs even when state says complete."""

    def make(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        out = Path(tmp.name)
        coordinator = ms.Coordinator.__new__(ms.Coordinator)
        coordinator.out = out
        coordinator.configurations = CONFIGS
        coordinator.args = type("Args", (), {"rounds": 5, "fit_only": False})()
        coordinator.state = {"runs": {}}
        coordinator.fieldnames = None
        return coordinator

    def record(self, coordinator, budget, circuit, rows):
        directory = coordinator.run_dir(budget, circuit)
        directory.mkdir(parents=True)
        path = directory / "rows.csv"
        ms.write_rows(path, FIELDS, rows)
        coordinator.state["runs"][coordinator.run_key(budget, circuit)] = {
            "status": "complete", "rows_sha256": ms.sha256_of(path)}
        return path

    def test_valid_complete_run_is_reused(self):
        c = self.make()
        self.record(c, 32 * GIB, CIRCUITS[0], full_rows(32 * GIB, CIRCUITS[0]))
        self.assertIsNotNone(c.completed_rows(32 * GIB, CIRCUITS[0]))

    def test_partial_csv_is_not_complete(self):
        c = self.make()
        self.record(c, 32 * GIB, CIRCUITS[0], full_rows(32 * GIB, CIRCUITS[0])[:1])
        self.assertIsNone(c.completed_rows(32 * GIB, CIRCUITS[0]))

    def test_incomplete_timing_is_not_complete(self):
        c = self.make()
        rows = full_rows(32 * GIB, CIRCUITS[0])
        rows[1].update(raw_samples_ms="[1.0,2.0]", timing_samples="2")
        self.record(c, 32 * GIB, CIRCUITS[0], rows)
        self.assertIsNone(c.completed_rows(32 * GIB, CIRCUITS[0]))

    def test_altered_csv_hash_is_not_complete(self):
        c = self.make()
        path = self.record(c, 32 * GIB, CIRCUITS[0], full_rows(32 * GIB, CIRCUITS[0]))
        path.write_text(path.read_text() + "\n")
        self.assertIsNone(c.completed_rows(32 * GIB, CIRCUITS[0]))

    def test_failed_status_is_not_complete(self):
        c = self.make()
        self.record(c, 32 * GIB, CIRCUITS[0], full_rows(32 * GIB, CIRCUITS[0]))
        c.state["runs"][c.run_key(32 * GIB, CIRCUITS[0])]["status"] = "failed"
        self.assertIsNone(c.completed_rows(32 * GIB, CIRCUITS[0]))


class OutputRederivation(unittest.TestCase):
    """Outputs and refinement must re-derive from validated runs, never from stored verdicts."""

    def make(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        out = Path(tmp.name)
        c = ms.Coordinator.__new__(ms.Coordinator)
        c.out = out
        c.state_path = out / "state.json"
        c.configurations = CONFIGS
        c.circuits = CIRCUITS
        c.full_circuit_set = True
        c.args = type("Args", (), {"rounds": 5, "fit_only": False, "max_refinement_points": None,
                                   "budgets": [34 * GIB, 32 * GIB]})()
        c.state = {"runs": {}, "budgets": {}}
        c.fieldnames = None
        return c

    def record(self, c, budget, circuit, rows):
        directory = c.run_dir(budget, circuit)
        directory.mkdir(parents=True)
        path = directory / "rows.csv"
        ms.write_rows(path, FIELDS, rows)
        c.state["runs"][c.run_key(budget, circuit)] = {"status": "complete", "rows_sha256": ms.sha256_of(path)}
        return path

    def test_corrupt_refinement_run_drops_that_budget_from_accepted_output(self):
        c = self.make()
        for budget in (34 * GIB, 33 * GIB + GIB // 2):
            for circuit in CIRCUITS:
                self.record(c, budget, circuit, full_rows(budget, circuit))
            c.state["budgets"][str(budget)] = {"status": "accepted", "winners": {x: "cfg_a" for x in CIRCUITS}}
        # Truncate one circuit's CSV of the refinement budget after the fact.
        broken = c.run_dir(33 * GIB + GIB // 2, CIRCUITS[1]) / "rows.csv"
        ms.write_rows(broken, FIELDS, full_rows(33 * GIB + GIB // 2, CIRCUITS[1])[:1])
        diagnostics, accepted = c.collect_rows()
        self.assertEqual({int(row["arena_bytes"]) for row in accepted}, {34 * GIB})
        self.assertEqual(sum(row["preferred"] == "true" for row in accepted), len(CIRCUITS))
        self.assertEqual(c.state["budgets"][str(33 * GIB + GIB // 2)]["status"], "incomplete")
        self.assertEqual(c.state["budgets"][str(34 * GIB)]["status"], "accepted")
        # The intact circuits of the broken budget are still in diagnostics.
        self.assertTrue(any(int(row["arena_bytes"]) == 33 * GIB + GIB // 2 for row in diagnostics))

    def test_stored_accepted_without_all_circuits_is_not_emitted(self):
        c = self.make()
        for circuit in CIRCUITS[:2]:
            self.record(c, 34 * GIB, circuit, full_rows(34 * GIB, circuit))
        c.state["budgets"][str(34 * GIB)] = {"status": "accepted", "winners": {x: "cfg_a" for x in CIRCUITS}}
        _, accepted = c.collect_rows()
        self.assertEqual(accepted, [])
        self.assertEqual(c.state["budgets"][str(34 * GIB)]["status"], "incomplete")

    def test_refine_revisits_stored_refinement_budgets(self):
        c = self.make()
        c.state["budgets"] = {
            str(34 * GIB): {"status": "accepted", "winners": {"a": "x"}},
            str(32 * GIB): {"status": "rejected", "winners": {}},
            str(33 * GIB + GIB // 2): {"status": "accepted", "winners": {"a": "x"}},
        }
        visited = []

        def fake_evaluate(budget):
            visited.append(budget)
            return {"status": "rejected" if budget < 33 * GIB + GIB // 2 else "accepted"}

        c.evaluate_budget = fake_evaluate
        c.refine()
        self.assertEqual(visited, [33 * GIB + GIB // 2, 33 * GIB])


class CsvRoundTrip(unittest.TestCase):
    def test_runner_style_booleans_parse(self):
        buffer = io.StringIO()
        writer = csv.DictWriter(buffer, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerow(row(32 * GIB, CIRCUITS[0], "cfg_a"))
        parsed = list(csv.DictReader(io.StringIO(buffer.getvalue())))[0]
        self.assertTrue(ms.timed_fit(parsed, 5, False))


class ConfigurationSelection(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.binary = self.root / "binary"
        self.binary.write_bytes(b"frozen binary")
        self.lock = self.root / "lock"
        self.lock.touch()

    def make(self, *extra):
        args = ms.build_parser().parse_args([
            "--binary", str(self.binary), "--gpu-lock", str(self.lock),
            "--output-dir", str(self.root / "results"), "--budgets-gib", "30", *extra])
        with patch.object(ms, "list_selectors", return_value=(CIRCUITS, CONFIGS)), \
                patch.object(ms, "command_output", return_value="test"):
            return ms.Coordinator(args)

    def test_default_keeps_all_configurations(self):
        self.assertEqual(self.make().configurations, CONFIGS)

    def test_unknown_configuration_rejected_before_work(self):
        with self.assertRaisesRegex(SystemExit, "unknown configurations"):
            self.make("--configurations", "typo")
        self.assertFalse((self.root / "results").exists())

    def test_resume_rejects_changed_policy_scope(self):
        c = self.make("--configurations", "cfg_b")
        self.assertTrue(c.full_circuit_set)
        self.assertEqual(c.identity["configurations"], ["cfg_b"])
        with self.assertRaisesRegex(SystemExit, "identity mismatch"):
            self.make("--resume")

    def test_single_policy_dispatched_and_all_circuits_still_required(self):
        c = self.make("--configurations", "cfg_b")

        def worker(command, **kwargs):
            spec = json.loads(Path(command[-1]).read_text())
            argv = spec["command"]
            self.assertEqual(argv[-2:], ["--configuration", "cfg_b"])
            self.assertEqual(argv.count("--configuration"), 1)
            ms.write_rows(Path(argv[argv.index("--output-csv") + 1]), FIELDS,
                          [row(30 * GIB, CIRCUITS[0], "cfg_b")])
            ms.write_json(Path(spec["meta"]), {"status": "exited", "returncode": 0})

        with patch.object(ms.subprocess, "run", side_effect=worker):
            rows = c.invoke(30 * GIB, CIRCUITS[0])
        self.assertEqual(len(rows), 1)
        self.assertIsNotNone(c.completed_rows(30 * GIB, CIRCUITS[0]))
        verdict = ms.qualify({CIRCUITS[0]: rows}, CIRCUITS, 5, False, True)
        self.assertEqual(verdict["status"], "incomplete")


if __name__ == "__main__":
    unittest.main()
