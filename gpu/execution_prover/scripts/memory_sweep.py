#!/usr/bin/env python3
"""Measure explicit arena budgets; emit presets only when every circuit fits.

Each (budget, circuit) invocation holds the GPU lock separately. --resume
revalidates saved results and binary identity. --fit-only and --circuits are
for diagnostics and cannot produce presets.
"""

import argparse
import csv
import hashlib
import json
import math
import os
import platform
import signal
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

GIB = 1 << 30
MIB = 1 << 20
DEFAULT_BUDGETS = [30 * GIB]
BIGINT = "delegation_big_int_with_control"
STATE_FILE = "state.json"
DIAGNOSTICS_CSV = "diagnostics.csv"
ACCEPTED_CSV = "accepted.csv"
TERMINATE_GRACE_SECONDS = 30
RELATIVE_TOLERANCE = 1e-5


def sha256_of(path):
    digest = hashlib.sha256()
    with open(path, "rb") as source:
        for block in iter(lambda: source.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def gib_label(budget_bytes):
    """Exact decimal GiB label for the binary's --arena-gib parser.

    Any multiple of 1 MiB is an exact decimal with at most ten fractional
    digits (1 MiB / 1 GiB = 2^-10 = 0.0009765625).
    """
    if budget_bytes <= 0 or budget_bytes % MIB:
        raise ValueError(f"budget {budget_bytes} is not a positive multiple of 1 MiB")
    whole, remainder = divmod(budget_bytes, GIB)
    if remainder == 0:
        return str(whole)
    digits = str(remainder * 10**10 // GIB).rjust(10, "0").rstrip("0")
    text = f"{whole}.{digits}"
    assert Fraction(text) * GIB == budget_bytes
    return text


def parse_budget_gib(text):
    value = Fraction(text)
    budget = value * GIB
    if value <= 0 or budget.denominator != 1 or int(budget) % MIB:
        raise argparse.ArgumentTypeError("budgets must be positive exact multiples of 1 MiB")
    return int(budget)


def is_true(text):
    return (text or "").strip().lower() == "true"


def finite_positive(text):
    try:
        value = float(text)
    except (TypeError, ValueError):
        return None
    return value if math.isfinite(value) and value > 0 else None


def summary_of(samples):
    """Runner's TimingSummary: median averages the middle pair for even counts."""
    ordered = sorted(samples)
    middle = len(ordered) // 2
    median = (ordered[middle - 1] + ordered[middle]) / 2 if len(ordered) % 2 == 0 else ordered[middle]
    return median, ordered[0], ordered[-1]


def close(text, expected):
    value = finite_positive(text)
    return value is not None and math.isclose(value, expected, rel_tol=RELATIVE_TOLERANCE)


def row_problems(row, budget, rounds, fit_only):
    """Reasons a CSV row is not trustworthy evidence; empty when it is."""
    problems = []
    try:
        if int(row["arena_bytes"]) != budget:
            problems.append("arena_bytes differs from the budget")
    except (KeyError, ValueError):
        problems.append("arena_bytes missing")
    fits = is_true(row.get("fits"))
    timing_samples = int(row.get("timing_samples") or 0)
    if not fits:
        if timing_samples or (row.get("median_ms") or "").strip():
            problems.append("non-fitting row carries timing data")
        return problems
    if (row.get("failure_stage") or "").strip():
        problems.append("fitting row has a failure stage")
    if not (row.get("proof_fingerprint") or "").strip().isdigit():
        problems.append("fitting row lacks a proof fingerprint")
    try:
        if not 0 < int(row["peak_bytes"]) <= budget:
            problems.append("peak_bytes exceeds the arena")
    except (KeyError, ValueError):
        problems.append("fitting row lacks peak_bytes")
    if fit_only:
        return problems
    try:
        samples = json.loads(row.get("raw_samples_ms") or "[]")
    except json.JSONDecodeError:
        samples = None
    if not isinstance(samples, list) or len(samples) != rounds or timing_samples != rounds:
        problems.append(f"timing needs exactly {rounds} raw samples and timing_samples")
        return problems
    if any(finite_positive(sample) is None for sample in samples):
        problems.append("raw samples must be finite and positive")
        return problems
    median, low, high = summary_of([float(sample) for sample in samples])
    if not (close(row.get("median_ms"), median) and close(row.get("min_ms"), low)
            and close(row.get("max_ms"), high)):
        problems.append("median/min/max disagree with the raw samples")
    return problems


def validate_rows(rows, budget, circuit, configurations, rounds, fit_only):
    """One valid row per configuration for `circuit` at `budget`, or a list of problems."""
    mine = [row for row in rows if row.get("circuit") == circuit]
    problems = []
    seen = {row.get("configuration") for row in mine}
    if len(mine) != len(configurations) or seen != set(configurations):
        problems.append(f"expected {len(configurations)} distinct configurations, found {len(mine)}")
    for row in mine:
        for problem in row_problems(row, budget, rounds, fit_only):
            problems.append(f"{row.get('configuration')}: {problem}")
    return problems


def timed_fit(row, rounds, fit_only):
    return is_true(row.get("fits")) and not row_problems(row, int(row["arena_bytes"]), rounds, fit_only)


def fastest(rows):
    """Deterministic winner: lowest median, then configuration name."""
    return min(rows, key=lambda row: (float(row["median_ms"]), row["configuration"]))


def qualify(rows_by_circuit, circuits, rounds, fit_only, full_circuit_set):
    """Budget verdict from validated per-circuit rows (None = run missing/failed).

    Timed sweeps stop at the first circuit with no fitting timed policy, so
    later circuits may be absent. Fit-only sweeps record every circuit.
    """
    winners, fits, missing = {}, {}, []
    for circuit in circuits:
        rows = rows_by_circuit.get(circuit)
        if rows is None:
            missing.append(circuit)
            continue
        fitting = [row for row in rows if row["circuit"] == circuit and timed_fit(row, rounds, fit_only)]
        fits[circuit] = bool(fitting)
        if fitting and not fit_only:
            winners[circuit] = fastest(fitting)["configuration"]
    if fit_only:
        status = "fit_only" if not missing else "incomplete"
        return {"status": status, "fits": fits, "winners": {}, "missing": missing,
                "reason": "fit-only diagnostic; no presets"}
    failing = [c for c in circuits if fits.get(c) is False]
    if failing:
        return {"status": "rejected", "fits": fits, "winners": winners, "missing": missing,
                "reason": f"{failing[0]}: no fitting timed policy"}
    if missing:
        return {"status": "incomplete", "fits": fits, "winners": winners, "missing": missing,
                "reason": f"runs missing for {missing}"}
    if not full_circuit_set:
        return {"status": "partial", "fits": fits, "winners": winners, "missing": [],
                "reason": "restricted circuit set; diagnostic only"}
    return {"status": "accepted", "fits": fits, "winners": winners, "missing": [], "reason": None}


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def read_rows(path):
    with open(path, newline="") as source:
        reader = csv.DictReader(source)
        return list(reader), reader.fieldnames or []


def write_rows(path, fieldnames, rows):
    with open(path, "w", newline="") as sink:
        writer = csv.DictWriter(sink, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
# Locked worker: everything that touches the GPU runs inside the lock


def command_output(command):
    try:
        return subprocess.run(command, text=True, capture_output=True, timeout=60, check=True).stdout
    except (OSError, subprocess.SubprocessError) as error:
        return f"<unavailable: {error}>"


def gpu_snapshot():
    return {
        "nvidia_smi": command_output(
            ["nvidia-smi", "--query-gpu=name,uuid,driver_version,memory.total,memory.used,"
             "temperature.gpu,power.draw,clocks.current.sm,clocks.current.memory", "--format=csv"]),
        "compute_apps": command_output(
            ["nvidia-smi", "--query-compute-apps=pid,process_name,used_gpu_memory", "--format=csv"]),
    }


def compute_apps_present(snapshot):
    lines = [line for line in snapshot["compute_apps"].splitlines() if line.strip()]
    return (len(lines) != 1 or not lines[0].lower().startswith("pid,")
            or snapshot.get("nvidia_smi", "").startswith("<unavailable"))


def run_process_group(command, log_path, timeout):
    """Run `command` as its own process group; on timeout terminate the whole group."""
    with open(log_path, "w") as log:
        child = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            return child.wait(timeout=timeout), False
        except subprocess.TimeoutExpired:
            pass
        group = os.getpgid(child.pid)
        os.killpg(group, signal.SIGTERM)
        try:
            child.wait(timeout=TERMINATE_GRACE_SECONDS)
        except subprocess.TimeoutExpired:
            os.killpg(group, signal.SIGKILL)
            child.wait()
        return child.returncode, True


def locked_worker(spec_path):
    """Invoked only through with_gpu_lock.sh. Writes meta.json; exits nonzero on any failure."""
    spec = json.loads(Path(spec_path).read_text())
    meta = {"spec": spec, "started": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "gpu_before": gpu_snapshot()}
    if compute_apps_present(meta["gpu_before"]):
        meta["status"] = "busy"
        write_json(Path(spec["meta"]), meta)
        return 3
    started = time.monotonic()
    returncode, timed_out = run_process_group(spec["command"], spec["log"], spec["timeout"])
    meta.update(returncode=returncode, timed_out=timed_out, wall_seconds=time.monotonic() - started,
                finished=time.strftime("%Y-%m-%dT%H:%M:%S%z"), gpu_after=gpu_snapshot())
    meta["status"] = "exited" if returncode == 0 and not timed_out else "failed"
    if compute_apps_present(meta["gpu_after"]):
        meta["status"] = "failed"
        meta["orphaned_gpu_process"] = True
    write_json(Path(spec["meta"]), meta)
    return 0 if meta["status"] == "exited" else 1
# Coordinator


def list_selectors(binary):
    """`--list` needs no CUDA context; returns (circuits, configurations)."""
    output = subprocess.run([str(binary), "--list"], text=True, capture_output=True, check=True).stdout
    circuits, configurations = [], []
    for line in output.splitlines():
        kind, _, name = line.partition(" ")
        if kind == "circuit":
            circuits.append(name)
        elif kind == "configuration":
            configurations.append(name)
    if not circuits or not configurations:
        raise SystemExit("binary --list returned no selectors; build with --features memory_sweep")
    return circuits, configurations


class Coordinator:
    def __init__(self, args):
        self.args = args
        self.binary = args.binary.resolve()
        self.out = args.output_dir.resolve()
        self.lock = args.gpu_lock.resolve()
        if not self.lock.is_file():
            raise SystemExit(f"GPU lock script not found: {self.lock}")
        self.binary_sha256 = sha256_of(self.binary)
        self.all_circuits, self.configurations = list_selectors(self.binary)
        if args.configurations:
            unknown = sorted(set(args.configurations) - set(self.configurations))
            if unknown:
                raise SystemExit(f"unknown configurations: {unknown}; known: {self.configurations}")
            # Canonical order makes resume independent of CLI selector order.
            self.configurations = [name for name in self.configurations if name in args.configurations]
        circuits = args.circuits or self.all_circuits
        unknown = sorted(set(circuits) - set(self.all_circuits))
        if unknown:
            raise SystemExit(f"unknown circuits: {unknown}; known: {self.all_circuits}")
        if BIGINT not in self.all_circuits:
            raise SystemExit(f"binary does not list {BIGINT}")
        self.circuits = sorted(circuits, key=lambda name: (name != BIGINT, self.all_circuits.index(name)))
        self.full_circuit_set = set(self.circuits) == set(self.all_circuits)
        self.identity = {
            "binary": str(self.binary),
            "binary_sha256": self.binary_sha256,
            "rounds": args.rounds,
            "fit_only": args.fit_only,
            "device_id": args.device_id,
            "circuits": self.circuits,
            "configurations": self.configurations,
        }
        self.state_path = self.out / STATE_FILE
        self.state = self.load_or_create_state()
        self.fieldnames = None

    def load_or_create_state(self):
        if self.state_path.exists():
            if not self.args.resume:
                raise SystemExit(f"{self.out} already holds a sweep; pass --resume to continue it")
            state = json.loads(self.state_path.read_text())
            if state["identity"] != self.identity:
                mismatch = {k: (state["identity"].get(k), v) for k, v in self.identity.items()
                            if state["identity"].get(k) != v}
                raise SystemExit(f"--resume identity mismatch (stored, current): {mismatch}")
            return state
        if self.args.resume:
            raise SystemExit(f"--resume requested but {self.state_path} does not exist")
        self.out.mkdir(parents=True, exist_ok=True)
        state = {
            "identity": self.identity,
            "environment": {
                "hostname": platform.node(),
                "python": sys.version,
                "git_head": command_output(["git", "rev-parse", "HEAD"]).strip(),
                "git_status": command_output(["git", "status", "--short"]),
                "started": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
            },
            "requested_budgets_bytes": self.args.budgets,
            "runs": {},
            "budgets": {},
        }
        write_json(self.state_path, state)
        return state

    def save(self):
        write_json(self.state_path, self.state)

    def run_dir(self, budget, circuit):
        return self.out / "runs" / gib_label(budget) / circuit

    @staticmethod
    def run_key(budget, circuit):
        return f"{budget}:{circuit}"

    def completed_rows(self, budget, circuit):
        """Validated rows of a recorded complete run, or None. Never trusts a partial CSV."""
        record = self.state["runs"].get(self.run_key(budget, circuit))
        if not record or record.get("status") != "complete":
            return None
        csv_path = self.run_dir(budget, circuit) / "rows.csv"
        if not csv_path.exists() or sha256_of(csv_path) != record.get("rows_sha256"):
            return None
        rows, fieldnames = read_rows(csv_path)
        if validate_rows(rows, budget, circuit, self.configurations, self.args.rounds, self.args.fit_only):
            return None
        self.fieldnames = self.fieldnames or fieldnames
        return rows

    def invoke(self, budget, circuit):
        """Run the binary for one circuit at one budget through the locked worker."""
        directory = self.run_dir(budget, circuit)
        directory.mkdir(parents=True, exist_ok=True)
        csv_path, log_path, meta_path, spec_path = (
            directory / "rows.csv", directory / "run.log", directory / "meta.json", directory / "spec.json")
        for stale in (csv_path, meta_path):
            if stale.exists():
                stale.unlink()
        command = [
            str(self.binary), "--arena-gib", gib_label(budget), "--device-id", str(self.args.device_id),
            "--circuit", circuit, "--output-csv", str(csv_path),
        ]
        command += ["--fit-only"] if self.args.fit_only else ["--rounds", str(self.args.rounds)]
        for configuration in self.configurations:
            command += ["--configuration", configuration]
        write_json(spec_path, {
            "command": command, "log": str(log_path), "meta": str(meta_path),
            "timeout": self.args.run_timeout_seconds, "binary_sha256": self.binary_sha256,
            "budget_bytes": budget, "circuit": circuit,
        })
        print(f"[sweep] {gib_label(budget)} GiB {circuit}: running", flush=True)
        subprocess.run([str(self.lock), sys.executable, str(Path(__file__).resolve()),
                        "--locked-worker", str(spec_path)], check=False)
        meta = json.loads(meta_path.read_text()) if meta_path.exists() else {"status": "no_meta"}
        rows, problems = [], ["worker did not report a clean exit"]
        if meta.get("status") == "exited" and csv_path.exists():
            rows, fieldnames = read_rows(csv_path)
            problems = validate_rows(rows, budget, circuit, self.configurations, self.args.rounds, self.args.fit_only)
            self.fieldnames = self.fieldnames or fieldnames
        complete = not problems
        record = {"status": "complete" if complete else "failed", "worker_status": meta.get("status"),
                  "returncode": meta.get("returncode"), "wall_seconds": meta.get("wall_seconds"),
                  "finished": meta.get("finished")}
        if complete:
            record["rows_sha256"] = sha256_of(csv_path)
        else:
            record["problems"] = problems[:20]
        self.state["runs"][self.run_key(budget, circuit)] = record
        self.save()
        if not complete:
            message = f"{gib_label(budget)} GiB {circuit}: run not complete ({problems[0]}); see {log_path}"
            if self.args.keep_going:
                print(f"[sweep] {message}", flush=True)
                return None
            raise SystemExit(message)
        return rows

    def rows_for(self, budget, circuit):
        rows = self.completed_rows(budget, circuit)
        if rows is None:
            return self.invoke(budget, circuit)
        print(f"[sweep] {gib_label(budget)} GiB {circuit}: reusing validated run", flush=True)
        return rows

    def evaluate_budget(self, budget):
        """Always re-derive the verdict from validated run artifacts; never from stored status alone."""
        label = gib_label(budget)
        rows_by_circuit = {}
        for circuit in self.circuits:
            rows = self.rows_for(budget, circuit)
            if rows is None:
                break
            rows_by_circuit[circuit] = rows
            if not self.args.fit_only and not any(
                    row["circuit"] == circuit and timed_fit(row, self.args.rounds, False) for row in rows):
                break  # this circuit rejects the budget; the rest are not needed
        record = qualify(rows_by_circuit, self.circuits, self.args.rounds, self.args.fit_only, self.full_circuit_set)
        self.state["budgets"][str(budget)] = record
        self.save()
        reason = f" ({record['reason']})" if record["reason"] else ""
        print(f"[sweep] {label} GiB: {record['status']}{reason}", flush=True)
        return record

    def derive_verdicts(self):
        """Re-derive every budget verdict from validated run artifacts.

        Stored verdicts are never trusted for output: a budget is accepted
        only if, right now, every circuit has a validated complete run with a
        fitting timed policy. The re-derived verdicts replace the stored ones.
        """
        budgets = {int(key.split(":")[0]) for key in self.state["runs"]} | {int(b) for b in self.state["budgets"]}
        verdicts = {}
        for budget in sorted(budgets, reverse=True):
            rows_by_circuit = {}
            for circuit in self.circuits:
                rows = self.completed_rows(budget, circuit)
                if rows is not None:
                    rows_by_circuit[circuit] = rows
            verdict = qualify(rows_by_circuit, self.circuits, self.args.rounds, self.args.fit_only,
                              self.full_circuit_set)
            verdicts[budget] = (verdict, rows_by_circuit)
            self.state["budgets"][str(budget)] = verdict
        self.save()
        return verdicts

    def collect_rows(self):
        diagnostics, accepted = [], []
        for budget, (verdict, rows_by_circuit) in self.derive_verdicts().items():
            for circuit in self.circuits:
                rows = rows_by_circuit.get(circuit)
                if rows is None:
                    continue
                mine = [row for row in rows if row["circuit"] == circuit]
                diagnostics.extend(mine)
                if verdict["status"] != "accepted":
                    continue
                winner = verdict["winners"][circuit]
                for row in mine:
                    row = dict(row)
                    row["preferred"] = "true" if (row["configuration"] == winner
                                                  and timed_fit(row, self.args.rounds, False)) else "false"
                    accepted.append(row)
        return diagnostics, accepted

    def write_outputs(self):
        diagnostics, accepted = self.collect_rows()
        if self.fieldnames is None:
            print("[sweep] no complete runs; nothing to write", flush=True)
            return
        write_rows(self.out / DIAGNOSTICS_CSV, self.fieldnames, diagnostics)
        ordered = sorted(self.state["budgets"].items(), key=lambda item: -int(item[0]))
        summary = {
            "binary_sha256": self.binary_sha256,
            "mode": "fit_only" if self.args.fit_only else "timed",
            "configurations": self.configurations,
            "selection_scope": "fastest among the selected configurations only",
            "budgets": {gib_label(int(b)): r for b, r in ordered},
            "accepted_budgets_gib": [gib_label(int(b)) for b, r in ordered if r["status"] == "accepted"],
            "scope": "synthetic maximum-shape inputs on the recorded GPU; an accepted budget fits every circuit",
        }
        accepted_path = self.out / ACCEPTED_CSV
        presets_allowed = self.full_circuit_set and not self.args.fit_only
        if presets_allowed and accepted:
            write_rows(accepted_path, self.fieldnames, accepted)
            summary["accepted_csv"] = str(accepted_path)
            if self.args.emit_rust:
                subprocess.run([str(self.binary), "--generate-policy", "--input-csv", str(accepted_path),
                                "--output-rust", str(self.args.emit_rust)], check=True)
                summary["generated_rust"] = str(self.args.emit_rust)
        else:
            if accepted_path.exists():
                accepted_path.unlink()
            summary["accepted_csv"] = None
            summary["note"] = ("fit-only or restricted run: presets are never produced" if not presets_allowed
                               else "no budget fit every circuit")
        write_json(self.out / "summary.json", summary)
        print(json.dumps(summary, indent=2), flush=True)

    def run(self):
        for budget in sorted(self.args.budgets, reverse=True):
            self.evaluate_budget(budget)
        self.write_outputs()


def build_parser():
    here = Path(__file__).resolve()
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--binary", type=Path, help="frozen gpu_memory_sweep release binary")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--budgets-gib", type=parse_budget_gib, nargs="+", dest="budgets", default=DEFAULT_BUDGETS,
                        help="exact GiB values (default: 48 down to 16 in 2 GiB steps)")
    parser.add_argument("--circuits", nargs="+", help="restrict to stable circuit names (diagnostic only)")
    parser.add_argument("--configurations", nargs="+",
                        help="measure only these policies; presets still require every circuit")
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--fit-only", action="store_true",
                        help="collect fit results for every circuit without timing; never produces presets")
    parser.add_argument("--device-id", type=int, default=0)
    parser.add_argument("--gpu-lock", type=Path, default=here.parents[3] / ".agents" / "bin" / "with_gpu_lock.sh")
    parser.add_argument("--run-timeout-seconds", type=float, default=None,
                        help="terminate the whole prover process group after this many seconds")
    parser.add_argument("--resume", action="store_true", help="continue a sweep in --output-dir after validating identity")
    parser.add_argument("--keep-going", action="store_true", help="record a failed invocation and continue")
    parser.add_argument("--emit-rust", type=Path, help="also run --generate-policy on the accepted-only CSV")
    parser.add_argument("--locked-worker", type=Path, help=argparse.SUPPRESS)
    return parser


def main():
    parser = build_parser()
    args = parser.parse_args()
    if args.locked_worker:
        sys.exit(locked_worker(args.locked_worker))
    if args.binary is None or args.output_dir is None:
        parser.error("--binary and --output-dir are required")
    if args.rounds < 1:
        parser.error("--rounds must be positive")
    if len(set(args.budgets)) != len(args.budgets):
        parser.error("duplicate budgets")
    if not args.binary.is_file():
        parser.error(f"binary not found: {args.binary}")
    Coordinator(args).run()


if __name__ == "__main__":
    main()
