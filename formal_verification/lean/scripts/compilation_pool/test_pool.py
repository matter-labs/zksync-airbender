"""Policy tests and opt-in, lightweight process controls for one guarded pool.

Process controls launch only finite Python children. Run their orchestrator
without an outer guard: each case acquires the one real guard/lock itself.
"""
import argparse
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scripts import bounded_fv as serial_guard
from scripts.compilation_pool import guard, pool

RUN_PROCESS = False
PROCESS_OUTPUT = None
MIB = 1 << 20


def sample(pid, name="lean", footprint=1, resident=1):
    return serial_guard.Sample(serial_guard.ProcessInfo(pid, 1, name), footprint, resident)


def job(label="a", **updates):
    value = {"label": label, "argv": [sys.executable, "-c", "pass"],
             "cwd": str(ROOT), "dependencies": [], "seconds": 3,
             "reserved_footprint_mib": 128, "reserved_resident_mib": 256}
    value.update(updates)
    return value


class GuardPolicyTests(unittest.TestCase):
    def setUp(self):
        self.args = argparse.Namespace(mib=2560, resident_mib=5120, seconds=900)

    def test_worker_ceiling_includes_every_lean(self):
        for workers in (1, 2, 4):
            with self.subTest(workers=workers):
                samples = [sample(index + 1) for index in range(workers)]
                self.assertIsNone(guard.budget_reason(samples, self.args, 1, workers))
                self.assertEqual(guard.budget_reason(samples + [sample(99)], self.args, 1, workers),
                                 "Lean worker limit exceeded")

    def test_invalid_worker_limits_fail_closed(self):
        for workers in (0, 5, -1, True, False):
            with self.subTest(workers=workers), self.assertRaises(ValueError):
                guard.budget_reason([], self.args, 0, workers)

    def test_aggregate_footprint_byte_boundary(self):
        samples = [sample(1, footprint=1280 * MIB), sample(2, footprint=1280 * MIB)]
        self.assertIsNone(guard.budget_reason(samples, self.args, 900, 2))
        self.assertEqual(guard.budget_reason(samples + [sample(3, "python", 1, 1)], self.args, 1, 2),
                         "memory budget exceeded")

    def test_aggregate_resident_byte_boundary(self):
        samples = [sample(1, resident=2560 * MIB), sample(2, resident=2560 * MIB)]
        self.assertIsNone(guard.budget_reason(samples, self.args, 1, 2))
        self.assertEqual(guard.budget_reason(samples + [sample(3, "python", 1, 1)], self.args, 1, 2),
                         "memory budget exceeded")

    def test_wall_deadline_is_unchanged(self):
        self.assertIsNone(guard.budget_reason([], self.args, 900, 4))
        self.assertEqual(guard.budget_reason([], self.args, 900.001, 4),
                         "wall-time budget exceeded")

    def test_cli_rejects_invalid_workers_before_serial_delegate(self):
        for workers in (0, 5):
            with self.subTest(workers=workers), mock.patch.object(serial_guard, "main") as delegate:
                with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                    guard.main(["--lean-workers", str(workers)])
                delegate.assert_not_called()

    def test_delegate_emits_one_receipt_and_restores_serial_policy(self):
        previous = serial_guard.budget_reason

        def delegated(_argv):
            self.assertIsNone(serial_guard.budget_reason([sample(1), sample(2)], self.args, 1))
            print(json.dumps({"reason": "finished", "exit": 0, "live_owned_after": []}))
            return 0

        output = io.StringIO()
        with mock.patch.object(serial_guard, "main", side_effect=delegated), contextlib.redirect_stdout(output):
            self.assertEqual(guard.main(["--lean-workers", "2"]), 0)
        records = [json.loads(line) for line in output.getvalue().splitlines()]
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["lean_workers_limit"], 2)
        self.assertEqual(records[0]["lean_workers_peak"], 2)
        self.assertIs(serial_guard.budget_reason, previous)

    def test_delegate_error_restores_serial_policy(self):
        previous = serial_guard.budget_reason
        with mock.patch.object(serial_guard, "main", side_effect=RuntimeError("fixture")):
            with self.assertRaisesRegex(RuntimeError, "fixture"):
                guard.main([])
        self.assertIs(serial_guard.budget_reason, previous)


class ManifestPolicyTests(unittest.TestCase):
    def test_valid_dependency_graph_is_retained(self):
        jobs = [job("a"), job("b"), job("c", dependencies=["a", "b"])]
        self.assertEqual(pool.validate_manifest({"jobs": jobs}), jobs)

    def test_unknown_and_high_memory_are_exclusive(self):
        for value in ({}, {"reserved_footprint_mib": 100},
                      job(reserved_footprint_mib=1217), job(reserved_resident_mib=2497),
                      job(exclusive=True)):
            with self.subTest(value=value):
                self.assertTrue(pool.reservation(value)[2])
        self.assertEqual(pool.reservation({}), (2432.0, 4992.0, True))
        self.assertEqual(pool.reservation(job(reserved_footprint_mib=1216,
                                              reserved_resident_mib=2496)), (1216.0, 2496.0, False))

    def test_reservations_leave_128_mib_for_pool_overhead(self):
        self.assertEqual(pool.reservation(job(reserved_footprint_mib=2432,
                                              reserved_resident_mib=4992)), (2432.0, 4992.0, True))
        for field, values in (("reserved_footprint_mib", (0, -1, True, float("nan"), float("inf"), 2433)),
                              ("reserved_resident_mib", (0, -1, True, float("nan"), float("inf"), 4993))):
            for value in values:
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    pool.validate_manifest({"jobs": [job(**{field: value})]})

    def test_invalid_graphs_and_commands_fail_before_launch(self):
        cases = ([job("a"), job("a")], [job("../escape")],
                 [job(dependencies=["missing"])], [job("a", dependencies=["b"]), job("b", dependencies=["a"])],
                 [job(argv=[])], [job(argv="python")], [job(cwd="relative")])
        for jobs in cases:
            with self.subTest(jobs=jobs), self.assertRaises(ValueError):
                pool.validate_manifest({"jobs": jobs})

    def test_member_deadlines_cannot_exceed_900_seconds(self):
        for seconds in (0, -1, 901, float("nan"), float("inf")):
            with self.subTest(seconds=seconds), self.assertRaises(ValueError):
                pool.validate_manifest({"jobs": [job(seconds=seconds)]})

    def test_stale_exit_is_restricted_to_explicit_cached_queries(self):
        query = ["lake", "--no-cache", "--no-build", "--json", "query", "+Airbender:leanArts"]
        self.assertEqual(pool.validate_manifest({"jobs": [job(argv=query, allowed_exits=[0, 3])]}),
                         [job(argv=query, allowed_exits=[0, 3])])
        for argv, allowed in (([sys.executable, "-c", "pass"], [0, 3]), (query, [0, 7])):
            with self.subTest(argv=argv, allowed=allowed), self.assertRaises(ValueError):
                pool.validate_manifest({"jobs": [job(argv=argv, allowed_exits=allowed)]})


CHILD = r'''
import json, os, subprocess, sys, time
from pathlib import Path
spec = json.loads(sys.argv[1])
directory, label = Path(spec['directory']), spec['label']
def record(phase):
    (directory / (label + '.' + phase + '.json')).write_text(json.dumps({'time': time.monotonic(), 'pid': os.getpid()}))
record('start')
for name in spec.get('required', []):
    assert (directory / (name + '.end.json')).exists(), 'dependency was not completed: ' + name
deadline = time.monotonic() + 3
for name in spec.get('barrier', []):
    while not (directory / (name + '.start.json')).exists():
        if time.monotonic() > deadline:
            raise RuntimeError('ready-job barrier timed out: ' + name)
        time.sleep(.01)
if spec.get('orphan'):
    child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(15)'],
                             start_new_session=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    (directory / (label + '.orphan.json')).write_text(json.dumps({'pid': child.pid}))
if spec.get('mutate'):
    Path(spec['mutate']).write_text('changed')
time.sleep(spec.get('sleep', .1))
record('end')
sys.exit(spec.get('exit', 0))
'''


class ProcessTests(unittest.TestCase):
    def setUp(self):
        if not RUN_PROCESS:
            self.skipTest("opt in with --process-tests; run this orchestrator without an outer guard")
        self.directory = Path(tempfile.mkdtemp(prefix=self._testMethodName + "-", dir=PROCESS_OUTPUT))
        if PROCESS_OUTPUT is None:
            self.addCleanup(shutil.rmtree, self.directory)

    def member(self, label, **settings):
        payload = {"directory": str(self.directory), "label": label}
        for key in ("barrier", "required", "sleep", "exit", "orphan", "mutate"):
            if key in settings:
                payload[key] = settings.pop(key)
        return job(label, argv=[sys.executable, "-c", CHILD, json.dumps(payload)], **settings)

    def run_pool(self, jobs, workers=2, inputs=None, suffix="run"):
        manifest = self.directory / (suffix + ".manifest.json")
        output = self.directory / suffix
        manifest.write_text(json.dumps({"jobs": jobs, "inputs": inputs or {}}) + "\n")
        command = [sys.executable, "-m", "scripts.compilation_pool.guard", "--mib", "2560",
                   "--resident-mib", "5120", "--seconds", "8", "--lean-workers", str(workers),
                   "--log", str(self.directory / (suffix + ".aggregate.log")), "--", sys.executable,
                   "-m", "scripts.compilation_pool.pool", "--manifest", str(manifest),
                   "--output", str(output), "--workers", str(workers)]
        process = subprocess.Popen(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            stdout, stderr = process.communicate(timeout=25)
        except subprocess.TimeoutExpired:
            process.send_signal(signal.SIGINT)
            try:
                stdout, stderr = process.communicate(timeout=8)
            except subprocess.TimeoutExpired:
                process.kill()
                stdout, stderr = process.communicate()
            self.fail("aggregate guard did not finish its bounded cleanup: " + stdout + stderr)
        (self.directory / (suffix + ".guard.stdout.txt")).write_text(stdout)
        (self.directory / (suffix + ".guard.stderr.txt")).write_text(stderr)
        records = [json.loads(line) for line in stdout.splitlines() if line.startswith("{")]
        self.assertEqual(len(records), 1, stdout + stderr)
        metrics = records[0]
        self.assertEqual(metrics["live_owned_after"], [], metrics)
        self.assertEqual(metrics["lean_workers_limit"], workers)
        self.assertLessEqual(metrics["lean_workers_peak"], workers)
        self.assertEqual(metrics["reason"], "finished", metrics)
        state = json.loads((output / "state.json").read_text())
        return process.returncode, state, output

    def event(self, label, phase):
        return json.loads((self.directory / (label + "." + phase + ".json")).read_text())

    def assert_disjoint(self, left, right):
        self.assertTrue(self.event(left, "end")["time"] <= self.event(right, "start")["time"] or
                        self.event(right, "end")["time"] <= self.event(left, "start")["time"])

    def assert_gone(self, pid):
        deadline = time.monotonic() + 1
        while time.monotonic() < deadline:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                return
            time.sleep(.02)
        self.fail("owned fixture process still exists after guard cleanup: " + str(pid))

    def test_ready_jobs_overlap_then_dependent_runs(self):
        jobs = [self.member("a", barrier=["a", "b"]), self.member("b", barrier=["a", "b"]),
                self.member("c", dependencies=["a", "b"], required=["a", "b"])]
        code, state, output = self.run_pool(jobs)
        self.assertEqual(code, 0, state)
        self.assertEqual(state["concurrent_jobs_peak"], 2)
        self.assertLess(self.event("a", "start")["time"], self.event("b", "end")["time"])
        self.assertLess(self.event("b", "start")["time"], self.event("a", "end")["time"])
        self.assertGreaterEqual(self.event("c", "start")["time"],
                                max(self.event("a", "end")["time"], self.event("b", "end")["time"]))
        self.assertTrue(json.loads((output / "result.json").read_text())["passed"])

    def test_four_light_ready_jobs_overlap(self):
        labels = ["light" + str(index) for index in range(4)]
        jobs = [self.member(label, barrier=labels) for label in labels]
        code, state, output = self.run_pool(jobs, workers=4)
        self.assertEqual(code, 0, state)
        self.assertEqual(state["concurrent_jobs_peak"], 4)
        self.assertLess(max(self.event(label, "start")["time"] for label in labels),
                        min(self.event(label, "end")["time"] for label in labels))
        self.assertTrue(json.loads((output / "result.json").read_text())["passed"])

    def test_unknown_and_high_memory_members_run_alone(self):
        for suffix, reservations in (("unknown", {"reserved_footprint_mib": None}),
                                     ("high", {"reserved_footprint_mib": 1300, "reserved_resident_mib": 1800})):
            with self.subTest(kind=suffix):
                labels = [suffix + item for item in ("x", "a", "b")]
                jobs = [self.member(labels[0], **reservations), self.member(labels[1]), self.member(labels[2])]
                code, state, _ = self.run_pool(jobs, suffix=suffix)
                self.assertEqual(code, 0, state)
                for other in labels[1:]:
                    self.assert_disjoint(labels[0], other)

    def test_reservation_sums_limit_admission_below_worker_ceiling(self):
        for suffix, footprint, resident in (("footprint", 900, 1000), ("resident", 400, 1670)):
            with self.subTest(budget=suffix):
                labels = [suffix + str(index) for index in range(4)]
                jobs = [self.member(label, barrier=labels[index // 2 * 2:index // 2 * 2 + 2],
                                    reserved_footprint_mib=footprint, reserved_resident_mib=resident)
                        for index, label in enumerate(labels)]
                code, state, _ = self.run_pool(jobs, workers=4, suffix=suffix)
                self.assertEqual(code, 0, state)
                self.assertEqual(state["concurrent_jobs_peak"], 2)

    def test_two_exact_half_reservations_are_admitted(self):
        labels = ["a", "b"]
        jobs = [self.member(label, barrier=labels, reserved_footprint_mib=1216,
                            reserved_resident_mib=2496) for label in labels]
        code, state, _ = self.run_pool(jobs)
        self.assertEqual(code, 0, state)
        self.assertEqual(state["concurrent_jobs_peak"], 2)

    def test_failure_stops_dependents_and_reaps_owned_children(self):
        jobs = [self.member("bad", barrier=["bad", "sibling"], sleep=.5, exit=7),
                self.member("sibling", orphan=True, sleep=5),
                self.member("dependent", dependencies=["bad"]), self.member("pending")]
        code, state, output = self.run_pool(jobs)
        self.assertNotEqual(code, 0)
        self.assertEqual(state["active"], [])
        self.assertIn("Member failed", state["failure"])
        self.assertFalse((self.directory / "dependent.start.json").exists())
        self.assertFalse((self.directory / "pending.start.json").exists())
        self.assertFalse((output / "result.json").exists())
        self.assert_gone(self.event("sibling", "start")["pid"])
        self.assert_gone(self.event("sibling", "orphan")["pid"])

    def test_member_timeout_fails_even_with_outer_time_remaining(self):
        jobs = [self.member("slow", orphan=True, sleep=5, seconds=.7),
                self.member("dependent", dependencies=["slow"])]
        code, state, _ = self.run_pool(jobs)
        self.assertNotEqual(code, 0)
        self.assertIn("Member deadline exceeded", state["failure"])
        self.assertEqual(state["active"], [])
        self.assertFalse((self.directory / "dependent.start.json").exists())
        self.assert_gone(self.event("slow", "start")["pid"])
        self.assert_gone(self.event("slow", "orphan")["pid"])

    def test_changed_pinned_input_cannot_produce_success(self):
        source = self.directory / "pinned-input"
        source.write_text("original")
        expected = hashlib.sha256(source.read_bytes()).hexdigest()
        code, state, output = self.run_pool([self.member("mutator", mutate=str(source))],
                                             inputs={str(source): expected})
        self.assertNotEqual(code, 0)
        self.assertIn("Input changed", state["failure"])
        self.assertFalse((output / "result.json").exists())


def main():
    global RUN_PROCESS, PROCESS_OUTPUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--process-tests", action="store_true")
    parser.add_argument("--process-output", type=Path,
                        help="Fresh directory retaining lightweight child/control receipts")
    options, remaining = parser.parse_known_args()
    RUN_PROCESS = options.process_tests
    if options.process_output is not None:
        if not RUN_PROCESS or not options.process_output.is_absolute() or options.process_output.exists():
            parser.error("--process-output requires --process-tests and a fresh absolute directory")
        options.process_output.mkdir(parents=True)
        PROCESS_OUTPUT = str(options.process_output)
    unittest.main(argv=[sys.argv[0], *remaining], verbosity=2)


if __name__ == "__main__":
    main()
