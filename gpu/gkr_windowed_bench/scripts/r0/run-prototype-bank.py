#!/usr/bin/env python3
"""Coordinate-major immutable controller for the R0 prototype bank."""

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
DEFAULT_CORPUS_MANIFEST = ROOT / "gpu/gkr_windowed_bench/artifacts/windowed_r0_corpus_v1.json"
DEFAULT_PROTOTYPES = ROOT / "gpu/gkr_windowed_bench/artifacts/windowed_r0_prototype_manifest_v1.json"
DEFAULT_ARTIFACT_ROOT = ROOT / "target/windowed-gkr-r0-prototype-bank/post-review/replacement"
DEFAULT_OUTPUT = ROOT / "target/windowed-gkr-r0-prototype-bank/correctness/campaign-v4-schema2"
DEFAULT_SCREEN = ROOT / "target/windowed-gkr-r0-prototype-bank/screen/coordinates.json"
DEFAULT_SCREEN_OUTPUT = ROOT / "target/windowed-gkr-r0-prototype-bank/screen/campaign-v4-schema2"
DEFAULT_LOCK = ROOT / ".agents/bin/with_gpu_lock.sh"


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def atomic_write(path: pathlib.Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text())


def parse_logs(text: str) -> list[int]:
    logs = [int(value) for value in text.split(",") if value]
    if not logs or len(logs) != len(set(logs)) or any(value <= 0 for value in logs):
        raise ValueError("logs must be unique positive integers")
    return logs


def validate_device_identity(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError("missing device identity")
    integer_fields = (
        "cuda_device_index", "compute_capability_major", "compute_capability_minor",
        "cuda_driver_version", "cuda_runtime_version", "default_shared_memory_bytes",
        "opt_in_shared_memory_bytes",
    )
    if any(type(value.get(field)) is not int or value[field] < 0 for field in integer_fields):
        raise ValueError("invalid numeric device identity field")
    if any(not isinstance(value.get(field), str) or not value[field] for field in (
        "uuid", "name", "cuda_toolkit_version",
    )):
        raise ValueError("invalid textual device identity field")
    clock = value.get("clock_policy")
    required_clock = (
        "raw_query", "uuid", "name", "compute_capability", "driver_version",
        "performance_state", "persistence_mode", "current_graphics_clock",
        "current_memory_clock", "max_graphics_clock", "max_memory_clock",
        "application_graphics_clock", "application_memory_clock",
        "clock_event_reasons_active",
    )
    if not isinstance(clock, dict) or any(
        not isinstance(clock.get(field), str) or not clock[field] for field in required_clock
    ):
        raise ValueError("invalid clock-policy identity")
    if clock["uuid"].lower() != value["uuid"].lower() or clock["name"] != value["name"]:
        raise ValueError("CUDA and clock-policy identities disagree")
    if value["default_shared_memory_bytes"] > value["opt_in_shared_memory_bytes"]:
        raise ValueError("default shared-memory limit exceeds opt-in limit")
    return value


def validate_launchability_identity(launchability: Any, identity: dict[str, Any]) -> None:
    if not isinstance(launchability, dict) or len(launchability) != 1:
        raise ValueError("malformed launchability")
    default = identity["default_shared_memory_bytes"]
    opt_in_limit = identity["opt_in_shared_memory_bytes"]
    if "launchable" in launchability:
        value = launchability["launchable"]
        if not isinstance(value, dict) or type(value.get("dynamic_shared_bytes")) is not int:
            raise ValueError("malformed launchable capacity")
        required = value["dynamic_shared_bytes"]
        opt_in = value.get("opt_in")
        if type(opt_in) is not bool or required < 0:
            raise ValueError("malformed launchable capacity")
        if (not opt_in and required > default) or (
            opt_in and not (default < required <= opt_in_limit)
        ):
            raise ValueError("launchable disposition contradicts device capacity")
    elif "unlaunchable_capacity" in launchability:
        value = launchability["unlaunchable_capacity"]
        if not isinstance(value, dict):
            raise ValueError("malformed unlaunchable capacity")
        required = value.get("required_bytes")
        limit = value.get("device_limit_bytes")
        if type(required) is not int or type(limit) is not int:
            raise ValueError("malformed unlaunchable capacity")
        if required <= opt_in_limit or limit != opt_in_limit:
            raise ValueError("unlaunchable disposition contradicts device capacity")
    else:
        raise ValueError("unknown launchability")


def lock_identity(value: str) -> dict[str, Any]:
    if value == "none":
        return {"mode": "none", "path": None, "sha256": None}
    path = pathlib.Path(value).resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise ValueError(f"GPU lock wrapper is not executable: {path}")
    return {"mode": "repository_file_lock", "path": str(path), "sha256": sha256(path)}


def wrap_command(command: list[str], lock: dict[str, Any]) -> list[str]:
    return ([lock["path"]] if lock["mode"] == "repository_file_lock" else []) + command


def query_current_device_identity(
    runner: pathlib.Path, lock: dict[str, Any]
) -> tuple[dict[str, Any], list[str]]:
    command = wrap_command(
        [str(runner), "--mode", "device-info", "--repo-root", str(ROOT)], lock
    )
    result = subprocess.run(command, capture_output=True, check=False)
    if result.returncode != 0:
        raise RuntimeError(
            f"device identity query exited {result.returncode}: "
            f"{result.stderr.decode(errors='replace').strip()}"
        )
    lines = [line for line in result.stdout.decode().splitlines() if line]
    if len(lines) != 1:
        raise ValueError("device identity query must emit exactly one JSON row")
    return validate_device_identity(json.loads(lines[0])), command


def validate_driver_evidence(
    driver_path: pathlib.Path, execution: dict[str, Any], expected_sha256: str | None = None
) -> str:
    if not driver_path.is_file():
        raise ValueError(f"missing driver log: {driver_path}")
    observed_sha256 = sha256(driver_path)
    if expected_sha256 is not None and observed_sha256 != expected_sha256:
        raise ValueError(f"driver log hash mismatch: {driver_path}")
    text = driver_path.read_text(errors="replace")
    lock = execution["gpu_lock"]
    lifecycle = (
        "[with_gpu_lock] waiting for GPU lock:",
        "[with_gpu_lock] acquired GPU lock:",
        "[with_gpu_lock] releasing GPU lock:",
    )
    if lock["mode"] == "repository_file_lock":
        if any(text.count(marker) != 1 for marker in lifecycle):
            raise ValueError(f"incomplete GPU-lock lifecycle: {driver_path}")
        release = next(line for line in text.splitlines() if lifecycle[2] in line)
        if "status=0" not in release:
            raise ValueError(f"GPU lock released with failure: {driver_path}")
    elif any(marker in text for marker in lifecycle):
        raise ValueError(f"unexpected GPU-lock lifecycle in unlocked session: {driver_path}")
    return observed_sha256


def validate_rows(
    rows_path: pathlib.Path,
    coordinate: dict[str, Any],
    log_trace: int,
    seed: int,
    expected_configs: set[str], expected_device_identity: dict[str, Any],
) -> list[dict[str, Any]]:
    rows = [json.loads(line) for line in rows_path.read_text().splitlines() if line]
    observed = {row.get("configuration_id") for row in rows}
    if len(rows) != len(expected_configs) or observed != expected_configs:
        raise ValueError(f"configuration coverage mismatch: {len(rows)} rows")
    identities = []
    for row in rows:
        key = (row.get("circuit"), row.get("layer"), row.get("log_trace"), row.get("seed"))
        expected = (coordinate["circuit"], coordinate["layer"], log_trace, seed)
        if key != expected or row.get("version") != 2:
            raise ValueError(f"row key mismatch: {key} != {expected}")
        identities.append(validate_device_identity(row.get("device_identity")))
        launchability = row.get("launchability", {})
        validate_launchability_identity(launchability, identities[-1])
        unlaunchable = "unlaunchable_capacity" in launchability
        if unlaunchable:
            if row.get("passing") or row.get("failure") != "unlaunchable_capacity":
                raise ValueError("malformed unlaunchable disposition")
        elif not row.get("passing") or row.get("failure") is not None:
            raise ValueError(f"failed launchable configuration {row['configuration_id']}")
        elif row.get("checksum") != row.get("expected_checksum"):
            raise ValueError(f"checksum mismatch {row['configuration_id']}")
    if identities[1:] and any(identity != identities[0] for identity in identities[1:]):
        raise ValueError("device identity changed within correctness session")
    if not identities or identities[0] != expected_device_identity:
        raise ValueError("runtime device identity differs from pre-session binding")
    return rows


def complete_is_reusable(
    directory: pathlib.Path, binding: dict[str, Any], coordinate: dict[str, Any], log_trace: int,
    seed: int, configs: set[str], expected_device_identity: dict[str, Any]
) -> bool:
    bindings_path = directory / "bindings.json"
    checkpoint_path = directory / "checkpoint.json"
    rows_path = directory / "rows.jsonl"
    if not (bindings_path.exists() and checkpoint_path.exists() and rows_path.exists()):
        return False
    if load_json(bindings_path) != binding:
        raise ValueError(f"immutable binding mismatch at {directory}")
    checkpoint = load_json(checkpoint_path)
    if checkpoint.get("state") != "complete":
        return False
    if checkpoint.get("version") != 2:
        raise ValueError(f"checkpoint version mismatch at {directory}")
    if checkpoint.get("binding_sha256") != sha256(bindings_path):
        raise ValueError(f"binding hash mismatch at {directory}")
    if checkpoint.get("rows_sha256") != sha256(rows_path):
        raise ValueError(f"rows hash mismatch at {directory}")
    rows = validate_rows(
        rows_path, coordinate, log_trace, seed, configs, expected_device_identity
    )
    if checkpoint.get("device_identity") != rows[0]["device_identity"]:
        raise ValueError(f"checkpoint device identity mismatch at {directory}")
    wall = checkpoint.get("controller_command_wall_seconds")
    if type(wall) not in (int, float) or not math.isfinite(wall) or wall <= 0:
        raise ValueError(f"checkpoint command wall mismatch at {directory}")
    validate_driver_evidence(
        directory / "driver.log", binding["execution"], checkpoint.get("driver_sha256")
    )
    return True


def correctness(args: argparse.Namespace) -> int:
    runner = pathlib.Path(args.runner).resolve()
    corpus = pathlib.Path(args.corpus).resolve()
    corpus_manifest = pathlib.Path(args.corpus_manifest).resolve()
    prototypes = pathlib.Path(args.prototype_manifest).resolve()
    artifact_root = pathlib.Path(args.artifact_root).resolve()
    output_root = pathlib.Path(args.output_root).resolve()
    for required in (runner, corpus, corpus_manifest, prototypes):
        if not required.is_file():
            raise ValueError(f"missing required file: {required}")
    if not os.access(runner, os.X_OK):
        raise ValueError(f"runner is not executable: {runner}")
    coordinates = load_json(corpus_manifest).get("coordinates", [])
    configurations = load_json(prototypes).get("configurations", [])
    config_ids = [row["configuration_id"] for row in configurations]
    if not coordinates or not config_ids or len(config_ids) != len(set(config_ids)):
        raise ValueError("empty/duplicate corpus or configuration manifest")
    logs = parse_logs(args.logs)
    lock = lock_identity(args.gpu_lock)
    completed = reused = 0
    for coordinate_index, coordinate in enumerate(coordinates):
        for log_index, log_trace in enumerate(logs):
            directory = output_root / f"log{log_trace}" / f"{coordinate['circuit']}--{coordinate['layer']}"
            rotated = (coordinate_index + log_index) % len(config_ids)
            ordered = config_ids[rotated:] + config_ids[:rotated]
            current_device_identity, device_query_command = query_current_device_identity(
                runner, lock
            )
            base_command = [
                str(runner), "--mode", "correctness", "--repo-root", str(ROOT),
                "--corpus", str(corpus), "--artifact-root", str(artifact_root),
                "--output-root", str(output_root), "--candidate", ",".join(ordered),
                "--coordinate", f"{coordinate['circuit']}:{coordinate['layer']}",
                "--log", str(log_trace), "--seed", str(args.seed),
            ]
            command = wrap_command(base_command, lock)
            binding = {
                "version": 2,
                "mode": "correctness",
                "runner": str(runner),
                "runner_sha256": sha256(runner),
                "corpus": str(corpus),
                "corpus_sha256": sha256(corpus),
                "corpus_manifest": str(corpus_manifest),
                "corpus_manifest_sha256": sha256(corpus_manifest),
                "prototype_manifest": str(prototypes),
                "prototype_manifest_sha256": sha256(prototypes),
                "artifact_root": str(artifact_root),
                "output_root": str(output_root),
                "coordinate": {"circuit": coordinate["circuit"], "layer": coordinate["layer"]},
                "log_trace": log_trace,
                "seed": args.seed,
                "configuration_ids": ordered,
                "device_identity": current_device_identity,
                "device_query_command": device_query_command,
                "execution": {"gpu_lock": lock, "command": command},
            }
            configs = set(config_ids)
            if complete_is_reusable(
                directory, binding, coordinate, log_trace, args.seed, configs,
                current_device_identity,
            ):
                reused += 1
                continue
            directory.mkdir(parents=True, exist_ok=True)
            atomic_write(directory / "bindings.json", canonical_bytes(binding))
            started = {
                "version": 2,
                "state": "started",
                "binding_sha256": sha256(directory / "bindings.json"),
            }
            atomic_write(directory / "checkpoint.json", canonical_bytes(started))
            rows_path = directory / "rows.jsonl"
            rows_path.write_bytes(b"")
            session_started = time.monotonic()
            with rows_path.open("wb") as stdout, (directory / "driver.log").open("wb") as stderr:
                result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
            controller_command_wall_seconds = time.monotonic() - session_started
            if result.returncode != 0:
                raise RuntimeError(f"runner exited {result.returncode}: {directory}")
            rows = validate_rows(
                rows_path, coordinate, log_trace, args.seed, configs, current_device_identity
            )
            driver_sha256 = validate_driver_evidence(
                directory / "driver.log", binding["execution"]
            )
            complete = {
                "version": 2,
                "state": "complete",
                "binding_sha256": sha256(directory / "bindings.json"),
                "rows_sha256": sha256(rows_path),
                "rows": len(rows),
                "launchable": sum("launchable" in row["launchability"] for row in rows),
                "unlaunchable_capacity": sum(
                    "unlaunchable_capacity" in row["launchability"] for row in rows
                ),
                "device_identity": validate_device_identity(rows[0]["device_identity"]),
                "controller_command_wall_seconds": controller_command_wall_seconds,
                "driver_sha256": driver_sha256,
            }
            atomic_write(directory / "checkpoint.json", canonical_bytes(complete))
            completed += 1
            print(
                f"complete={completed} reused={reused} coordinate={coordinate['circuit']}:{coordinate['layer']} log={log_trace}",
                flush=True,
            )
    print(f"PROTOTYPE_CORRECTNESS_DONE complete={completed} reused={reused}")
    return 0


def validate_screen_rows(
    rows_path: pathlib.Path, coordinate: dict[str, Any], ordered_configs: list[str],
    expected_device_identity: dict[str, Any],
) -> list[dict[str, Any]]:
    expected_configs = set(ordered_configs)
    rows = [json.loads(line) for line in rows_path.read_text().splitlines() if line]
    observed = {row.get("observation", {}).get("configuration_id") for row in rows}
    if len(rows) != len(expected_configs) or observed != expected_configs:
        raise ValueError(f"screen configuration coverage mismatch: {rows_path}")
    identities = []
    pilot_positions = []
    retained_positions = []
    shared_walls = set()
    for row in rows:
        observation = row.get("observation", {})
        key = (observation.get("circuit"), observation.get("layer"), observation.get("log_trace"))
        expected = (coordinate["circuit"], coordinate["layer"], coordinate["log_trace"])
        if key != expected or observation.get("seed") != 0 or observation.get("version") != 2:
            raise ValueError(f"screen key mismatch {key} != {expected}")
        identities.append(validate_device_identity(observation.get("device_identity")))
        validate_launchability_identity(observation.get("launchability"), identities[-1])
        for field in (
            "coordinate_cpu_setup_seconds", "coordinate_harness_setup_seconds",
            "reference_wall_seconds", "coordinate_execution_wall_seconds",
        ):
            if (type(row.get(field)) not in (int, float) or not math.isfinite(row[field])
                    or row[field] <= 0):
                raise ValueError(f"invalid screen wall field {field}")
        shared_walls.add((
            row["coordinate_cpu_setup_seconds"], row["coordinate_harness_setup_seconds"],
            row["reference_wall_seconds"], row["coordinate_execution_wall_seconds"],
        ))
        launchability = observation.get("launchability", {})
        if "unlaunchable_capacity" in launchability:
            if (observation.get("passing") or observation.get("failure") != "unlaunchable_capacity"
                    or row.get("samples") or row.get("pilot_samples")):
                raise ValueError(f"invalid screen capacity fact {key}")
            if row.get("candidate_wall_seconds") != 0.0:
                raise ValueError(f"capacity row has candidate work: {key}")
            continue
        if not observation.get("passing") or observation.get("failure") is not None:
            raise ValueError(f"failed screen configuration {observation.get('configuration_id')}")
        if (type(row.get("candidate_wall_seconds")) not in (int, float)
                or not math.isfinite(row["candidate_wall_seconds"])
                or row["candidate_wall_seconds"] <= 0):
            raise ValueError("invalid candidate wall")
        pilot = row.get("pilot_median_ms")
        retained = row.get("retained_samples")
        pilot_samples = row.get("pilot_samples")
        samples = row.get("samples")
        if type(pilot) not in (int, float) or pilot <= 0 or type(retained) is not int:
            raise ValueError("invalid pilot/cardinality")
        expected_retained = min(50, max(5, math.ceil(100.0 / pilot)))
        if retained != expected_retained or len(pilot_samples) != 5 or len(samples) != retained + 2:
            raise ValueError("screen retained sample calibration mismatch")
        if [sample.get("warmup") for sample in pilot_samples] != [True, True, False, False, False]:
            raise ValueError("screen pilot warmup sequence mismatch")
        if [sample.get("warmup") for sample in samples] != [True, True] + [False] * retained:
            raise ValueError("screen warmup sequence mismatch")
        if any(type(sample.get("warmup")) is not bool for sample in pilot_samples + samples):
            raise ValueError("screen warmup must be an exact boolean")
        if any(type(sample.get("milliseconds")) not in (int, float)
               or not math.isfinite(sample["milliseconds"])
               or sample["milliseconds"] <= 0 for sample in pilot_samples + samples):
            raise ValueError("invalid screen duration")
        pilot_measured = [sample["milliseconds"] for sample in pilot_samples if not sample["warmup"]]
        if sorted(pilot_measured)[len(pilot_measured) // 2] != pilot:
            raise ValueError("screen pilot median does not match raw pilot samples")
        pilot_position = pilot_samples[0].get("pass_position")
        retained_position = samples[0].get("pass_position")
        if type(pilot_position) is not int or type(retained_position) is not int:
            raise ValueError("invalid screen pass position")
        pilot_positions.append((observation["configuration_id"], pilot_position))
        retained_positions.append((observation["configuration_id"], retained_position))
        for phase_samples, phase, pass_index, position in (
            (pilot_samples, "pilot", 0, pilot_position),
            (samples, "retained", 1, retained_position),
        ):
            if any(
                sample.get("version") != 2
                or sample.get("configuration_id") != observation["configuration_id"]
                or sample.get("circuit") != coordinate["circuit"]
                or sample.get("layer") != coordinate["layer"]
                or sample.get("log_trace") != coordinate["log_trace"]
                or sample.get("seed") != 0
                or sample.get("phase") != phase
                or sample.get("pass_index") != pass_index
                or sample.get("pass_position") != position
                for sample in phase_samples
            ):
                raise ValueError("screen sample identity mismatch")
            expected_indices = [0, 1] + list(range(len(phase_samples) - 2))
            if [sample.get("sample_index") for sample in phase_samples] != expected_indices:
                raise ValueError("screen sample-index sequence mismatch")
        checksums = {
            observation.get("checksum"), observation.get("expected_checksum"),
            row.get("pilot_correctness_checksum"), row.get("pilot_post_session_checksum"),
            row.get("retained_correctness_checksum"), row.get("retained_post_session_checksum"),
        }
        if None in checksums or len(checksums) != 1:
            raise ValueError("screen checksum drift")
    if identities[1:] and any(identity != identities[0] for identity in identities[1:]):
        raise ValueError("device identity changed within screen session")
    if not identities or identities[0] != expected_device_identity:
        raise ValueError("screen device identity differs from pre-session binding")
    if len(shared_walls) != 1:
        raise ValueError("coordinate-level wall accounting changed between rows")
    circuit_key = 0
    for byte in coordinate["circuit"].encode():
        circuit_key = (circuit_key * 131 + byte) & ((1 << 64) - 1)
    rotation = 0 if len(ordered_configs) == 1 else (
        (circuit_key + coordinate["layer"]) % (len(ordered_configs) - 1) + 1
    )
    retained_order = ordered_configs[rotation:] + ordered_configs[:rotation]
    launchable_ids = {configuration_id for configuration_id, _ in pilot_positions}
    expected_pilot = {
        configuration_id: position for position, configuration_id in enumerate(ordered_configs)
        if configuration_id in launchable_ids
    }
    expected_retained = {
        configuration_id: position for position, configuration_id in enumerate(retained_order)
        if configuration_id in launchable_ids
    }
    if dict(pilot_positions) != expected_pilot or dict(retained_positions) != expected_retained:
        raise ValueError("screen pass positions differ from deterministic schedule")
    return rows


def screen(args: argparse.Namespace) -> int:
    runner = pathlib.Path(args.runner).resolve()
    corpus = pathlib.Path(args.corpus).resolve()
    prototypes = pathlib.Path(args.prototype_manifest).resolve()
    artifact_root = pathlib.Path(args.artifact_root).resolve()
    screen_path = pathlib.Path(args.screen).resolve()
    output_root = pathlib.Path(args.output_root).resolve()
    for required in (runner, corpus, prototypes, screen_path):
        if not required.is_file():
            raise ValueError(f"missing required file: {required}")
    screen_rows = load_json(screen_path)["rows"]
    config_ids = [row["configuration_id"] for row in load_json(prototypes)["configurations"]]
    expected_configs = set(config_ids)
    lock = lock_identity(args.gpu_lock)
    completed = reused = 0
    for coordinate_index, coordinate in enumerate(screen_rows):
        directory = output_root / f"{coordinate['circuit']}--{coordinate['layer']}"
        rotation = coordinate_index % len(config_ids)
        ordered = config_ids[rotation:] + config_ids[:rotation]
        current_device_identity, device_query_command = query_current_device_identity(runner, lock)
        base_command = [
            str(runner), "--mode", "screen", "--repo-root", str(ROOT),
            "--corpus", str(corpus), "--artifact-root", str(artifact_root),
            "--output-root", str(output_root), "--candidate", ",".join(ordered),
            "--coordinate", f"{coordinate['circuit']}:{coordinate['layer']}",
            "--log", str(coordinate["log_trace"]), "--seed", "0",
        ]
        command = wrap_command(base_command, lock)
        binding = {
            "version": 2, "mode": "screen", "runner": str(runner),
            "runner_sha256": sha256(runner), "corpus": str(corpus),
            "corpus_sha256": sha256(corpus), "prototype_manifest": str(prototypes),
            "prototype_manifest_sha256": sha256(prototypes), "artifact_root": str(artifact_root),
            "output_root": str(output_root),
            "screen": str(screen_path), "screen_sha256": sha256(screen_path),
            "coordinate": {"circuit": coordinate["circuit"], "layer": coordinate["layer"]},
            "log_trace": coordinate["log_trace"], "seed": 0,
            "requested_bytes": coordinate["requested_bytes"], "configuration_ids": ordered,
            "device_identity": current_device_identity,
            "device_query_command": device_query_command,
            "execution": {"gpu_lock": lock, "command": command},
        }
        bindings_path = directory / "bindings.json"
        checkpoint_path = directory / "checkpoint.json"
        rows_path = directory / "rows.jsonl"
        if bindings_path.is_file() and checkpoint_path.is_file() and rows_path.is_file():
            if load_json(bindings_path) != binding:
                raise ValueError(f"immutable screen binding mismatch: {directory}")
            checkpoint = load_json(checkpoint_path)
            if checkpoint.get("state") == "complete":
                if checkpoint.get("version") != 2:
                    raise ValueError(f"screen checkpoint version mismatch: {directory}")
                if checkpoint.get("binding_sha256") != sha256(bindings_path):
                    raise ValueError(f"screen binding hash mismatch: {directory}")
                if checkpoint.get("rows_sha256") != sha256(rows_path):
                    raise ValueError(f"screen row hash mismatch: {directory}")
                rows = validate_screen_rows(
                    rows_path, coordinate, ordered, current_device_identity
                )
                if checkpoint.get("device_identity") != rows[0]["observation"]["device_identity"]:
                    raise ValueError(f"screen checkpoint device mismatch: {directory}")
                wall = checkpoint.get("controller_command_wall_seconds")
                if type(wall) not in (int, float) or not math.isfinite(wall) or wall <= 0:
                    raise ValueError(f"screen checkpoint wall mismatch: {directory}")
                if checkpoint.get("runner_coordinate_work_seconds") != rows[0]["coordinate_execution_wall_seconds"]:
                    raise ValueError(f"screen runner work mismatch: {directory}")
                validate_driver_evidence(
                    directory / "driver.log", binding["execution"],
                    checkpoint.get("driver_sha256"),
                )
                reused += 1
                continue
        directory.mkdir(parents=True, exist_ok=True)
        atomic_write(bindings_path, canonical_bytes(binding))
        atomic_write(checkpoint_path, canonical_bytes({
            "version": 2, "state": "started", "binding_sha256": sha256(bindings_path)
        }))
        rows_path.write_bytes(b"")
        session_started = time.monotonic()
        with rows_path.open("wb") as stdout, (directory / "driver.log").open("wb") as stderr:
            result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
        controller_command_wall_seconds = time.monotonic() - session_started
        if result.returncode != 0:
            raise RuntimeError(f"screen runner exited {result.returncode}: {directory}")
        rows = validate_screen_rows(rows_path, coordinate, ordered, current_device_identity)
        driver_sha256 = validate_driver_evidence(directory / "driver.log", binding["execution"])
        atomic_write(checkpoint_path, canonical_bytes({
            "version": 2, "state": "complete", "binding_sha256": sha256(bindings_path),
            "rows_sha256": sha256(rows_path), "rows": len(rows),
            "device_identity": validate_device_identity(rows[0]["observation"]["device_identity"]),
            "controller_command_wall_seconds": controller_command_wall_seconds,
            "runner_coordinate_work_seconds": rows[0]["coordinate_execution_wall_seconds"],
            "driver_sha256": driver_sha256,
        }))
        completed += 1
        print(f"SCREEN_COMPLETE {completed}/{len(screen_rows)} {coordinate['circuit']}:{coordinate['layer']}", flush=True)
    print(f"PROTOTYPE_SCREEN_DONE complete={completed} reused={reused}")
    return 0


def parser() -> argparse.ArgumentParser:
    top = argparse.ArgumentParser()
    sub = top.add_subparsers(dest="command", required=True)
    run = sub.add_parser("correctness")
    run.add_argument("--runner", default=str(DEFAULT_RUNNER))
    run.add_argument("--corpus", default=str(DEFAULT_CORPUS))
    run.add_argument("--corpus-manifest", default=str(DEFAULT_CORPUS_MANIFEST))
    run.add_argument("--prototype-manifest", default=str(DEFAULT_PROTOTYPES))
    run.add_argument("--artifact-root", default=str(DEFAULT_ARTIFACT_ROOT))
    run.add_argument("--output-root", default=str(DEFAULT_OUTPUT))
    run.add_argument("--gpu-lock", default=str(DEFAULT_LOCK))
    run.add_argument("--logs", default="3,12")
    run.add_argument("--seed", type=int, default=0)
    run_screen = sub.add_parser("screen")
    run_screen.add_argument("--runner", default=str(DEFAULT_RUNNER))
    run_screen.add_argument("--corpus", default=str(DEFAULT_CORPUS))
    run_screen.add_argument("--prototype-manifest", default=str(DEFAULT_PROTOTYPES))
    run_screen.add_argument("--artifact-root", default=str(DEFAULT_ARTIFACT_ROOT))
    run_screen.add_argument("--screen", default=str(DEFAULT_SCREEN))
    run_screen.add_argument("--output-root", default=str(DEFAULT_SCREEN_OUTPUT))
    run_screen.add_argument("--gpu-lock", default=str(DEFAULT_LOCK))
    return top


if __name__ == "__main__":
    try:
        parsed = parser().parse_args()
        raise SystemExit(correctness(parsed) if parsed.command == "correctness" else screen(parsed))
    except Exception as error:
        print(f"prototype controller error: {error}", file=sys.stderr)
        raise SystemExit(1)
