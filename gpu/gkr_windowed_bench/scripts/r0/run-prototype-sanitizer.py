#!/usr/bin/env python3
"""Run the deterministic prototype-bank sanitizer factor cover."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import pathlib
import subprocess
import sys
import tempfile
import time
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[4]
DEFAULT_RUNNER = ROOT / "target/windowed-gkr-r0-prototype-bank/post-review/replacement/run_windowed_r0_prototype_bank"
DEFAULT_CORPUS = ROOT / "gpu/gkr_windowed_bench/artifacts/windowed_r0_corpus_v1.bin"
DEFAULT_ARTIFACT = ROOT / "target/windowed-gkr-r0-prototype-bank/post-review/replacement"
DEFAULT_COVER = ROOT / "target/windowed-gkr-r0-prototype-bank/sanitizer/cover.json"
DEFAULT_OUTPUT = ROOT / "target/windowed-gkr-r0-prototype-bank/sanitizer/campaign-v4-schema2"
DEFAULT_LOCK = ROOT / ".agents/bin/with_gpu_lock.sh"


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def atomic(path: pathlib.Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data); handle.flush(); os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def slug(value: str) -> str:
    return value.replace("/", "--")


def validate_device_identity(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError("missing sanitizer device identity")
    for field in (
        "cuda_device_index", "compute_capability_major", "compute_capability_minor",
        "cuda_driver_version", "cuda_runtime_version", "default_shared_memory_bytes",
        "opt_in_shared_memory_bytes",
    ):
        if type(value.get(field)) is not int or value[field] < 0:
            raise ValueError("invalid sanitizer numeric device identity")
    if value["default_shared_memory_bytes"] > value["opt_in_shared_memory_bytes"]:
        raise ValueError("invalid sanitizer shared-memory limits")
    clock = value.get("clock_policy")
    if not isinstance(clock, dict) or clock.get("uuid", "").lower() != value.get("uuid", "").lower() \
            or clock.get("name") != value.get("name") or not clock.get("raw_query"):
        raise ValueError("invalid sanitizer clock-policy identity")
    return value


def lock_identity(value: str) -> dict[str, Any]:
    if value == "none":
        return {"mode": "none", "path": None, "sha256": None}
    path = pathlib.Path(value).resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise ValueError(f"GPU lock wrapper is not executable: {path}")
    return {"mode": "repository_file_lock", "path": str(path), "sha256": sha256(path)}


def wrap(command: list[str], lock: dict[str, Any]) -> list[str]:
    return ([lock["path"]] if lock["mode"] == "repository_file_lock" else []) + command


def query_device(runner: pathlib.Path, lock: dict[str, Any]) -> tuple[dict[str, Any], list[str]]:
    command = wrap([str(runner), "--mode", "device-info", "--repo-root", str(ROOT)], lock)
    result = subprocess.run(command, capture_output=True, check=False)
    lines = result.stdout.decode().splitlines()
    if result.returncode != 0 or len(lines) != 1:
        raise RuntimeError("sanitizer device identity query failed")
    return validate_device_identity(json.loads(lines[0])), command


def validate_driver(path: pathlib.Path, lock: dict[str, Any], expected: str | None = None) -> str:
    observed = sha256(path)
    if expected is not None and observed != expected:
        raise ValueError(f"sanitizer driver hash mismatch: {path}")
    text = path.read_text(errors="replace")
    markers = (
        "[with_gpu_lock] waiting for GPU lock:",
        "[with_gpu_lock] acquired GPU lock:",
        "[with_gpu_lock] releasing GPU lock:",
    )
    if lock["mode"] == "repository_file_lock":
        if any(text.count(marker) != 1 for marker in markers) \
                or "status=0" not in next(line for line in text.splitlines() if markers[2] in line):
            raise ValueError(f"sanitizer GPU-lock lifecycle mismatch: {path}")
    elif any(marker in text for marker in markers):
        raise ValueError(f"unlocked sanitizer unexpectedly has lock lifecycle: {path}")
    return observed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--runner", default=str(DEFAULT_RUNNER))
    parser.add_argument("--corpus", default=str(DEFAULT_CORPUS))
    parser.add_argument("--artifact-root", default=str(DEFAULT_ARTIFACT))
    parser.add_argument("--cover", default=str(DEFAULT_COVER))
    parser.add_argument("--output-root", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--gpu-lock", default=str(DEFAULT_LOCK))
    parser.add_argument("--coordinate", default="inits_and_teardowns:3")
    parser.add_argument("--log", type=int, default=12)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    runner = pathlib.Path(args.runner).resolve()
    corpus = pathlib.Path(args.corpus).resolve()
    artifact = pathlib.Path(args.artifact_root).resolve()
    cover_path = pathlib.Path(args.cover).resolve()
    output = pathlib.Path(args.output_root).resolve()
    lock = lock_identity(args.gpu_lock)
    cover = json.loads(cover_path.read_text())
    if cover["universe"] != cover["covered"]:
        raise ValueError("sanitizer factor cover is incomplete")
    total = complete = reused = 0
    commands = []
    for row in cover["rows"]:
        for tool in row["tools"]:
            total += 1
            directory = output / slug(row["configuration_id"]) / tool
            base_command = [
                "compute-sanitizer", "--tool", tool, "--target-processes", "all",
                "--error-exitcode", "99", "--kernel-name", f"kernel_name={row['symbol']}",
                "--log-file", str(directory / "sanitizer.log"),
                str(runner), "--mode", "correctness", "--repo-root", str(ROOT),
                "--corpus", str(corpus),
                "--artifact-root", str(artifact),
                "--output-root", str(output), "--candidate", row["configuration_id"],
                "--coordinate", args.coordinate, "--log", str(args.log), "--seed", str(args.seed),
            ]
            if tool == "racecheck":
                insert = base_command.index("--target-processes")
                base_command[insert:insert] = ["--racecheck-report", "all"]
            command = wrap(base_command, lock)
            current_identity = device_query_command = None
            if not args.dry_run:
                current_identity, device_query_command = query_device(runner, lock)
            binding = {
                "version": 2,
                "runner": str(runner),
                "runner_sha256": sha256(runner),
                "corpus": str(corpus),
                "corpus_sha256": sha256(corpus),
                "artifact_root": str(artifact),
                "cover": str(cover_path),
                "cover_sha256": sha256(cover_path),
                "configuration_id": row["configuration_id"],
                "candidate_id": row["candidate_id"],
                "symbol": row["symbol"],
                "tool": tool,
                "coordinate": args.coordinate,
                "log_trace": args.log,
                "seed": args.seed,
                "command": command,
                "execution": {"gpu_lock": lock, "command": command},
                "device_identity": current_identity,
                "device_query_command": device_query_command,
            }
            commands.append(command)
            if args.dry_run:
                continue
            bindings = directory / "bindings.json"
            checkpoint = directory / "checkpoint.json"
            rows_path = directory / "rows.jsonl"
            if bindings.is_file() and checkpoint.is_file() and rows_path.is_file():
                if json.loads(bindings.read_text()) != binding:
                    raise ValueError(f"immutable binding mismatch: {directory}")
                state = json.loads(checkpoint.read_text())
                if state.get("state") == "complete":
                    if state.get("version") != 2 or state.get("binding_sha256") != sha256(bindings):
                        raise ValueError(f"complete sanitizer binding mismatch: {directory}")
                    if state.get("rows_sha256") != sha256(rows_path) or state.get("sanitizer_sha256") != sha256(directory / "sanitizer.log"):
                        raise ValueError(f"complete sanitizer hash mismatch: {directory}")
                    rows = [json.loads(line) for line in rows_path.read_text().splitlines() if line]
                    if (len(rows) != 1 or state.get("device_identity") != current_identity
                            or rows[0].get("device_identity") != current_identity):
                        raise ValueError(f"complete sanitizer device mismatch: {directory}")
                    validate_driver(
                        directory / "driver.log", lock, state.get("driver_sha256")
                    )
                    wall = state.get("controller_command_wall_seconds")
                    if type(wall) not in (int, float) or not math.isfinite(wall) or wall <= 0:
                        raise ValueError(f"complete sanitizer command wall mismatch: {directory}")
                    reused += 1
                    continue
            directory.mkdir(parents=True, exist_ok=True)
            atomic(bindings, canonical(binding))
            atomic(checkpoint, canonical({"version": 2, "state": "started", "binding_sha256": sha256(bindings)}))
            rows_path.write_bytes(b"")
            session_started = time.monotonic()
            with rows_path.open("wb") as stdout, (directory / "driver.log").open("wb") as stderr:
                result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
            controller_command_wall_seconds = time.monotonic() - session_started
            if result.returncode != 0:
                raise RuntimeError(f"{tool} exited {result.returncode}: {directory}")
            rows = [json.loads(line) for line in rows_path.read_text().splitlines() if line]
            if (len(rows) != 1 or rows[0].get("version") != 2
                    or rows[0].get("configuration_id") != row["configuration_id"]
                    or not rows[0].get("passing")
                    or validate_device_identity(rows[0].get("device_identity")) != current_identity):
                raise ValueError(f"invalid sanitizer correctness row: {directory}")
            sanitizer_log = directory / "sanitizer.log"
            summary = (
                "ERROR SUMMARY: 0 errors"
                if tool == "memcheck"
                else "RACECHECK SUMMARY: 0 hazards displayed (0 errors, 0 warnings)"
            )
            if sanitizer_log.read_text().count(summary) != 1:
                raise ValueError(f"missing unique zero-error summary: {directory}")
            driver_sha256 = validate_driver(directory / "driver.log", lock)
            atomic(checkpoint, canonical({
                "version": 2, "state": "complete", "binding_sha256": sha256(bindings),
                "rows_sha256": sha256(rows_path), "sanitizer_sha256": sha256(sanitizer_log),
                "device_identity": rows[0]["device_identity"],
                "controller_command_wall_seconds": controller_command_wall_seconds,
                "driver_sha256": driver_sha256,
            }))
            complete += 1
            print(f"SANITIZER_COMPLETE {complete}/{total} {row['configuration_id']} {tool}", flush=True)
    if args.dry_run:
        print(json.dumps({"version": 2, "sessions": total, "commands": commands}, separators=(",", ":")))
    else:
        print(f"PROTOTYPE_SANITIZER_DONE total={total} complete={complete} reused={reused}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"prototype sanitizer error: {error}", file=sys.stderr)
        raise SystemExit(1)
