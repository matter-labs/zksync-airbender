#!/usr/bin/env python3
"""Deterministic, resumable scheduler for the natural R0 timing campaign."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import time
from typing import Any


GEOMETRIES = [
    "cta288_pair",
    "cta96_partitioned",
    "cta96_x0_major",
    "cta96_x1_major",
    "cta96_x2_major",
]
TRAVERSALS = ("forward", "reverse")
WARMUPS_PER_TRAVERSAL = 5
SAMPLES_PER_TRAVERSAL = 50


def fail(message: str) -> "NoReturn":
    raise SystemExit(message)


def rotated_points(points: list[str], index: int, traversal: str) -> list[str]:
    if not points:
        return []
    if traversal == "forward":
        rotation = index % len(points)
    elif traversal == "reverse":
        rotation = (-index - 1) % len(points)
    else:
        fail(f"unknown traversal {traversal}")
    return points[rotation:] + points[:rotation]


def envelope_pair_session_count(point_count: int, coordinate_count: int) -> int:
    if point_count < 0 or coordinate_count < 0:
        fail("envelope point and coordinate counts must be nonnegative")
    return point_count * coordinate_count * len(TRAVERSALS)


def projected_envelope_budget(
    *,
    pilot_wall_seconds: float,
    pilot_sessions: int,
    distinct_point_binaries: int,
    total_pair_sessions: int,
    completed_pair_sessions: int,
) -> dict[str, Any]:
    if pilot_wall_seconds <= 0 or pilot_sessions <= 0:
        fail("pilot wall time and session count must be positive")
    if distinct_point_binaries <= 0:
        fail("distinct point binary count must be positive")
    if not 0 <= completed_pair_sessions <= total_pair_sessions:
        fail("completed pair session count is outside the campaign")
    seconds_per_runner = pilot_wall_seconds / pilot_sessions
    remaining = total_pair_sessions - completed_pair_sessions
    return {
        "version": 1,
        "pilot_wall_seconds": pilot_wall_seconds,
        "pilot_sessions": pilot_sessions,
        "observed_wall_seconds_per_all_geometry_runner": seconds_per_runner,
        "distinct_point_binaries": distinct_point_binaries,
        "runner_invocations_per_pair_session": 2,
        "total_pair_sessions": total_pair_sessions,
        "completed_pair_sessions": completed_pair_sessions,
        "remaining_pair_sessions": remaining,
        "projected_remaining_lock_hours": seconds_per_runner * 2 * remaining / 3600.0,
        "hard_gate": False,
    }


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def build_flags_sha256(path: pathlib.Path) -> str:
    preimage = path.read_bytes()
    if preimage.endswith(b"\n"):
        preimage = preimage[:-1]
    return hashlib.sha256(preimage).hexdigest()


def source_tree_sha256(root: pathlib.Path) -> str:
    candidates: list[pathlib.Path] = []
    for directory_name in ("src", "native"):
        directory = root / directory_name
        if directory.is_dir():
            candidates.extend(path for path in directory.rglob("*") if path.is_file())
    for name in ("Cargo.toml", "build.rs"):
        path = root / name
        if path.is_file():
            candidates.append(path)
    if not candidates:
        candidates = [path for path in root.rglob("*") if path.is_file()]
    digest = hashlib.sha256()
    for path in sorted(candidates):
        relative = str(path.relative_to(root)).encode()
        contents = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "little"))
        digest.update(relative)
        digest.update(len(contents).to_bytes(8, "little"))
        digest.update(contents)
    return digest.hexdigest()


def atomic_json(path: pathlib.Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = (json.dumps(value, separators=(",", ":")) + "\n").encode()
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = pathlib.Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        temporary.unlink(missing_ok=True)


def coordinate_name(row: dict[str, Any]) -> str:
    return f"{row['circuit']}:{row['layer']}"


def coordinate_stem(row: dict[str, Any]) -> str:
    return f"{row['circuit']}-l{row['layer']}"


def ordered_coordinates(manifest: dict[str, Any], traversal: str) -> list[dict[str, Any]]:
    coordinates = list(manifest["coordinates"])
    if traversal == "reverse":
        coordinates.reverse()
    return coordinates


def rotated_geometries(index: int, traversal: str) -> list[str]:
    if traversal == "forward":
        rotation = index % len(GEOMETRIES)
    else:
        rotation = (-index - 1) % len(GEOMETRIES)
    return GEOMETRIES[rotation:] + GEOMETRIES[:rotation]


def load_json(path: pathlib.Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        fail(f"read {label} {path}: {error}")
    if not isinstance(value, dict):
        fail(f"{label} {path} is not a JSON object")
    return value


def validate_hash(name: str, value: Any) -> str:
    if not isinstance(value, str) or len(value) != 64 or any(
        byte not in "0123456789abcdef" for byte in value
    ):
        fail(f"{name} is not lowercase SHA-256")
    return value


def session_binding(
    *,
    row: dict[str, Any],
    traversal: str,
    geometries: list[str],
    production: dict[str, Any],
    runner_hash: str,
    bundle_hash: str,
    source_hash: str,
    build_flags_hash: str,
) -> dict[str, Any]:
    bindings = production.get("bindings")
    if not isinstance(bindings, dict):
        fail(f"production bindings missing for {coordinate_name(row)}")
    for field in (
        "bundle_sha256",
        "coordinate_sha256",
        "input_sha256",
        "source_data_sha256",
        "independent_source_sha256",
        "challenge_sha256",
        "equality_point_sha256",
        "direct_eq_sha256",
        "factored_eq_sha256",
        "coefficient_sha256",
    ):
        validate_hash(f"production {field}", bindings.get(field))
    if bindings["bundle_sha256"] != bundle_hash:
        fail(f"production bundle binding mismatch for {coordinate_name(row)}")
    if bindings["coordinate_sha256"] != row["payload_sha256"]:
        fail(f"production coordinate binding mismatch for {coordinate_name(row)}")
    expected_coordinate = coordinate_name(row)
    if production.get("coordinate") != expected_coordinate:
        fail(f"production coordinate mismatch for {expected_coordinate}")
    if production.get("geometries") != GEOMETRIES:
        fail(f"production geometry coverage mismatch for {expected_coordinate}")
    checksum = validate_hash("production checksum", production.get("checksum"))
    return {
        "version": 1,
        "point": "natural",
        "coordinate": expected_coordinate,
        "traversal": traversal,
        "geometries": geometries,
        "warmups": WARMUPS_PER_TRAVERSAL,
        "samples": SAMPLES_PER_TRAVERSAL,
        "executable_sha256": runner_hash,
        "bundle_sha256": bundle_hash,
        "input_sha256": bindings["input_sha256"],
        "source_tree_sha256": source_hash,
        "build_flags_sha256": build_flags_hash,
        "expected_checksum": checksum,
        "production_bindings": bindings,
    }


def combined_rows_hash(session_dir: pathlib.Path) -> str:
    digest = hashlib.sha256()
    for geometry in GEOMETRIES:
        path = session_dir / f"{geometry}.samples.jsonl"
        if not path.is_file():
            fail(f"timing session did not create {path}")
        relative = path.name.encode()
        contents = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "little"))
        digest.update(relative)
        digest.update(len(contents).to_bytes(8, "little"))
        digest.update(contents)
    return digest.hexdigest()


def run_session(
    *,
    runner: pathlib.Path,
    lock_wrapper: pathlib.Path,
    session_dir: pathlib.Path,
    binding: dict[str, Any],
    resume: bool,
) -> bool:
    bindings_path = session_dir / "session-bindings.json"
    checkpoint_path = session_dir / "session.checkpoint.json"
    if bindings_path.exists():
        existing = load_json(bindings_path, "session bindings")
        if existing != binding:
            fail(f"binding mismatch for {binding['coordinate']} {binding['traversal']}")
    else:
        atomic_json(bindings_path, binding)

    if checkpoint_path.exists():
        checkpoint = load_json(checkpoint_path, "session checkpoint")
        expected_identity = {
            "version": 1,
            "coordinate": binding["coordinate"],
            "traversal": binding["traversal"],
            "bindings_sha256": sha256_file(bindings_path),
        }
        if any(checkpoint.get(key) != value for key, value in expected_identity.items()):
            fail(f"checkpoint binding mismatch for {binding['coordinate']} {binding['traversal']}")
        state = checkpoint.get("state")
        if state == "complete":
            actual = combined_rows_hash(session_dir)
            if checkpoint.get("rows_sha256") != actual:
                fail(f"complete rows hash mismatch for {binding['coordinate']} {binding['traversal']}")
            return False
        if state != "started":
            fail(f"unknown checkpoint state for {binding['coordinate']} {binding['traversal']}")
        if not resume:
            fail(f"started checkpoint requires --resume for {binding['coordinate']} {binding['traversal']}")

    session_dir.mkdir(parents=True, exist_ok=True)
    started = {
        "version": 1,
        "coordinate": binding["coordinate"],
        "traversal": binding["traversal"],
        "bindings_sha256": sha256_file(bindings_path),
        "state": "started",
        "rows_sha256": "",
    }
    atomic_json(checkpoint_path, started)

    command = [
        str(lock_wrapper),
        str(runner),
        "timing",
        "--point",
        binding["point"],
        "--coordinate",
        binding["coordinate"],
        "--geometries",
        ",".join(binding["geometries"]),
        "--traversal",
        binding["traversal"],
        "--warmups",
        str(binding["warmups"]),
        "--samples",
        str(binding["samples"]),
        "--expected-checksum",
        binding["expected_checksum"],
        "--session-bindings",
        str(bindings_path.resolve()),
        "--output-dir",
        str(session_dir.resolve()),
    ]
    if resume:
        command.append("--resume")
    stdout_path = session_dir / "stdout.jsonl"
    stderr_path = session_dir / "stderr.lock.txt"
    started_at = time.monotonic()
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
    if result.returncode != 0:
        fail(
            f"timing session failed status={result.returncode} "
            f"coordinate={binding['coordinate']} traversal={binding['traversal']}"
        )

    complete = {
        **started,
        "state": "complete",
        "rows_sha256": combined_rows_hash(session_dir),
        "harness_wall_seconds": time.monotonic() - started_at,
    }
    atomic_json(checkpoint_path, complete)
    return True


def pilot_coordinates(manifest: dict[str, Any]) -> list[str]:
    ordered = sorted(
        manifest["coordinates"],
        key=lambda row: (row["shape"]["records"], coordinate_name(row)),
    )
    selected = [ordered[0], ordered[len(ordered) // 2], ordered[-1]]
    return [coordinate_name(row) for row in selected]


def selected_coordinates(args: argparse.Namespace, manifest: dict[str, Any]) -> set[str] | None:
    selected = set(args.coordinate or [])
    if getattr(args, "pilot", False):
        selected.update(pilot_coordinates(manifest))
    return selected or None


def run_campaign(args: argparse.Namespace) -> None:
    manifest = load_json(args.manifest, "manifest")
    coordinates = manifest.get("coordinates")
    if not isinstance(coordinates, list) or len(coordinates) != 57:
        fail("timing manifest must contain exactly 57 coordinates")
    identities = [coordinate_name(row) for row in coordinates]
    if len(set(identities)) != len(identities):
        fail("timing manifest contains duplicate coordinates")
    if identities != sorted(identities):
        fail("timing manifest coordinates are not deterministic sorted order")

    runner_hash = sha256_file(args.runner)
    bundle_hash = sha256_file(args.bundle)
    source_hash = source_tree_sha256(args.source_root)
    build_flags_hash = build_flags_sha256(args.build_flags)
    validate_hash("manifest bundle_sha256", manifest.get("bundle_sha256"))
    if manifest["bundle_sha256"] != bundle_hash:
        fail("manifest bundle hash differs from the selected bundle")

    selected = selected_coordinates(args, manifest)
    selected_count = len(selected) if selected is not None else len(coordinates)
    total_sessions = selected_count * len(TRAVERSALS)
    visited = 0
    completed = 0
    reused = 0
    for traversal in TRAVERSALS:
        rows = ordered_coordinates(manifest, traversal)
        for index, row in enumerate(rows):
            if selected is not None and coordinate_name(row) not in selected:
                continue
            production_path = (
                args.production_root / coordinate_stem(row) / "input-bindings.json"
            )
            production = load_json(production_path, "production input binding")
            geometry_order = rotated_geometries(index, traversal)
            binding = session_binding(
                row=row,
                traversal=traversal,
                geometries=geometry_order,
                production=production,
                runner_hash=runner_hash,
                bundle_hash=bundle_hash,
                source_hash=source_hash,
                build_flags_hash=build_flags_hash,
            )
            session_dir = args.output_root / coordinate_stem(row) / traversal
            if run_session(
                runner=args.runner,
                lock_wrapper=args.lock_wrapper,
                session_dir=session_dir,
                binding=binding,
                resume=args.resume,
            ):
                completed += 1
            else:
                reused += 1
            visited += 1
            print(
                json.dumps(
                    {
                        "session": visited,
                        "total_sessions": total_sessions,
                        "coordinate": coordinate_name(row),
                        "traversal": traversal,
                        "completed": completed,
                        "reused": reused,
                    }
                ),
                flush=True,
            )
    print(json.dumps({"completed_sessions": completed, "reused_sessions": reused}))


def consolidate_production(
    row: dict[str, Any], directory: pathlib.Path
) -> dict[str, Any]:
    checkpoints = sorted(directory.glob("*.checkpoint.json"))
    if len(checkpoints) != len(GEOMETRIES):
        fail(f"production {coordinate_name(row)} has {len(checkpoints)} checkpoints, expected five")
    bindings = None
    checksum = None
    seen_geometries = []
    launches = []
    cells = None
    for checkpoint_path in checkpoints:
        checkpoint = load_json(checkpoint_path, "production checkpoint")
        if checkpoint.get("state") != "complete":
            fail(f"production checkpoint is not Complete: {checkpoint_path}")
        rows_path = checkpoint_path.with_name(
            checkpoint_path.name.replace(".checkpoint.json", ".observations.jsonl")
        )
        if sha256_file(rows_path) != checkpoint.get("rows_sha256"):
            fail(f"production rows hash mismatch: {rows_path}")
        lines = [json.loads(line) for line in rows_path.read_text().splitlines()]
        if len(lines) != 1:
            fail(f"production observation count mismatch: {rows_path}")
        observation = lines[0]
        key = observation.get("key", {})
        geometry = key.get("geometry")
        if geometry not in GEOMETRIES or geometry in seen_geometries:
            fail(f"production geometry mismatch: {rows_path}")
        if key.get("circuit") != row["circuit"] or key.get("layer") != row["layer"]:
            fail(f"production coordinate mismatch: {rows_path}")
        if key.get("traversal") is not None:
            fail(f"production row unexpectedly has a traversal: {rows_path}")
        if observation.get("production_rows") != row["trace_len"] // 8:
            fail(f"production row count mismatch: {rows_path}")
        if observation.get("shape") != row["shape"]:
            fail(f"production shape mismatch: {rows_path}")
        if observation.get("failure") is not None:
            fail(f"production observation failed: {rows_path}")
        if not all(observation.get(field) is not None for field in ("launch", "cells", "checksum")):
            fail(f"production observation is incomplete: {rows_path}")
        if checkpoint.get("key") != key or checkpoint.get("bindings") != observation.get("bindings"):
            fail(f"production checkpoint identity mismatch: {rows_path}")
        if bindings is None:
            bindings = observation["bindings"]
            checksum = observation["checksum"]
            cells = observation["cells"]
        elif (
            bindings != observation["bindings"]
            or checksum != observation["checksum"]
            or cells != observation["cells"]
        ):
            fail(f"production cross-geometry identity mismatch: {rows_path}")
        seen_geometries.append(geometry)
        launches.append(observation["launch"])
    if set(seen_geometries) != set(GEOMETRIES):
        fail(f"production geometry coverage mismatch for {coordinate_name(row)}")
    ordered_launches = [launches[seen_geometries.index(geometry)] for geometry in GEOMETRIES]
    return {
        "version": 1,
        "coordinate": coordinate_name(row),
        "bindings": bindings,
        "checksum": checksum,
        "geometries": GEOMETRIES,
        "production_rows": row["trace_len"] // 8,
        "shape": row["shape"],
        "launches": ordered_launches,
    }


def prepare_production(args: argparse.Namespace) -> None:
    manifest = load_json(args.manifest, "manifest")
    coordinates = manifest.get("coordinates")
    if not isinstance(coordinates, list) or len(coordinates) != 57:
        fail("production manifest must contain exactly 57 coordinates")
    selected = selected_coordinates(args, manifest)
    rows = [row for row in coordinates if selected is None or coordinate_name(row) in selected]
    for index, row in enumerate(rows, 1):
        directory = args.output_root / coordinate_stem(row)
        binding_path = directory / "input-bindings.json"
        if binding_path.exists():
            expected = consolidate_production(row, directory)
            if load_json(binding_path, "production input binding") != expected:
                fail(f"production binding mismatch for {coordinate_name(row)}")
            reused = True
        else:
            directory.mkdir(parents=True, exist_ok=True)
            command = [
                str(args.lock_wrapper),
                str(args.runner),
                "production",
                "--coordinate",
                coordinate_name(row),
                "--all-geometries",
                "--output-dir",
                str(directory.resolve()),
                "--point",
                "natural",
            ]
            if args.resume:
                command.append("--resume")
            with (directory / "stdout.jsonl").open("wb") as stdout, (
                directory / "stderr.lock.txt"
            ).open("wb") as stderr:
                result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
            if result.returncode != 0:
                fail(
                    f"production session failed status={result.returncode} "
                    f"coordinate={coordinate_name(row)}"
                )
            atomic_json(binding_path, consolidate_production(row, directory))
            reused = False
        print(
            json.dumps(
                {
                    "production_session": index,
                    "total_sessions": len(rows),
                    "coordinate": coordinate_name(row),
                    "reused": reused,
                }
            ),
            flush=True,
        )


def timing_budget(args: argparse.Namespace) -> None:
    manifest = load_json(args.manifest, "manifest")
    pilot = pilot_coordinates(manifest)
    wall_seconds = 0.0
    kernel_seconds = 0.0
    measured_kernel_seconds = 0.0
    completed = 0
    for coordinate in pilot:
        circuit, layer = coordinate.rsplit(":", 1)
        stem = f"{circuit}-l{layer}"
        for traversal in TRAVERSALS:
            directory = args.timing_root / stem / traversal
            checkpoint = load_json(directory / "session.checkpoint.json", "pilot checkpoint")
            if checkpoint.get("state") != "complete":
                fail(f"pilot checkpoint is not Complete: {coordinate} {traversal}")
            wall = checkpoint.get("harness_wall_seconds")
            if not isinstance(wall, (int, float)) or wall <= 0:
                fail(f"pilot checkpoint lacks harness wall time: {coordinate} {traversal}")
            wall_seconds += float(wall)
            for geometry in GEOMETRIES:
                rows = [
                    json.loads(line)
                    for line in (directory / f"{geometry}.samples.jsonl").read_text().splitlines()
                ]
                kernel_seconds += sum(float(row["milliseconds"]) for row in rows) / 1000.0
                measured_kernel_seconds += (
                    sum(float(row["milliseconds"]) for row in rows if not row["warmup"])
                    / 1000.0
                )
            completed += 1
    total_sessions = len(manifest["coordinates"]) * len(TRAVERSALS)
    remaining_sessions = total_sessions - completed
    report = {
        "version": 1,
        "pilot_coordinates": pilot,
        "completed_pilot_sessions": completed,
        "total_sessions": total_sessions,
        "remaining_sessions": remaining_sessions,
        "observed_harness_wall_seconds": wall_seconds,
        "observed_all_event_kernel_seconds": kernel_seconds,
        "observed_measured_kernel_seconds": measured_kernel_seconds,
        "projected_remaining_lock_hours": (wall_seconds / completed) * remaining_sessions / 3600.0,
        "projected_remaining_event_kernel_hours": (kernel_seconds / completed)
        * remaining_sessions
        / 3600.0,
        "hard_gate": False,
    }
    atomic_json(args.output, report)
    print(json.dumps(report, indent=2))


def recursive_evidence_hash(directory: pathlib.Path) -> str:
    digest = hashlib.sha256()
    paths = sorted(
        path
        for arm in ("child", "natural")
        for path in (directory / arm).rglob("*")
        if path.is_file()
    )
    if not paths:
        fail(f"paired timing session has no arm evidence: {directory}")
    for path in paths:
        relative = str(path.relative_to(directory)).encode()
        contents = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "little"))
        digest.update(relative)
        digest.update(len(contents).to_bytes(8, "little"))
        digest.update(contents)
    return digest.hexdigest()


def envelope_session_binding(
    *,
    point: dict[str, Any],
    natural: dict[str, Any],
    row: dict[str, Any],
    traversal: str,
    geometries: list[str],
    production: dict[str, Any],
    bundle_hash: str,
    source_hash: str,
    build_flags_hash: str,
) -> dict[str, Any]:
    coordinate = coordinate_name(row)
    if production.get("coordinate") != coordinate:
        fail(f"production coordinate mismatch for {coordinate}")
    if production.get("geometries") != GEOMETRIES:
        fail(f"production geometry coverage mismatch for {coordinate}")
    bindings = production.get("bindings")
    if not isinstance(bindings, dict):
        fail(f"production bindings missing for {coordinate}")
    for field in (
        "bundle_sha256",
        "coordinate_sha256",
        "input_sha256",
        "source_data_sha256",
        "independent_source_sha256",
        "challenge_sha256",
        "equality_point_sha256",
        "direct_eq_sha256",
        "factored_eq_sha256",
        "coefficient_sha256",
        "executable_sha256",
        "source_tree_sha256",
        "build_flags_sha256",
    ):
        validate_hash(f"production {field}", bindings.get(field))
    if bindings["bundle_sha256"] != bundle_hash:
        fail(f"production bundle binding mismatch for {coordinate}")
    if bindings["coordinate_sha256"] != row["payload_sha256"]:
        fail(f"production coordinate binding mismatch for {coordinate}")
    expected_checksum = validate_hash("production checksum", production.get("checksum"))
    return {
        "version": 1,
        "point_id": point["point_id"],
        "natural_point_id": natural["point_id"],
        "coordinate": coordinate,
        "traversal": traversal,
        "target_geometry": point["geometry"],
        "geometries": geometries,
        "arm_order": ["child", "natural"]
        if traversal == "forward"
        else ["natural", "child"],
        "warmups": WARMUPS_PER_TRAVERSAL,
        "samples": SAMPLES_PER_TRAVERSAL,
        "child": {
            "runner": point["runner"],
            "executable_sha256": point["executable_sha256"],
        },
        "natural": {
            "runner": natural["runner"],
            "executable_sha256": natural["executable_sha256"],
        },
        "bundle_sha256": bundle_hash,
        "input_sha256": bindings["input_sha256"],
        "source_tree_sha256": source_hash,
        "build_flags_sha256": build_flags_hash,
        "expected_checksum": expected_checksum,
        "production_bindings": bindings,
    }


def arm_session_binding(
    pair: dict[str, Any], arm: str
) -> dict[str, Any]:
    point = pair["point_id"] if arm == "child" else pair["natural_point_id"]
    runtime = pair[arm]
    return {
        "version": 1,
        "point": point,
        "coordinate": pair["coordinate"],
        "traversal": pair["traversal"],
        "geometries": pair["geometries"],
        "warmups": pair["warmups"],
        "samples": pair["samples"],
        "executable_sha256": runtime["executable_sha256"],
        "bundle_sha256": pair["bundle_sha256"],
        "input_sha256": pair["input_sha256"],
        "source_tree_sha256": pair["source_tree_sha256"],
        "build_flags_sha256": pair["build_flags_sha256"],
        "expected_checksum": pair["expected_checksum"],
        "production_bindings": pair["production_bindings"],
    }


def paired_session(args: argparse.Namespace) -> None:
    pair = load_json(args.pair_bindings, "pair bindings")
    if pair.get("version") != 1 or set(pair.get("arm_order", [])) != {
        "child",
        "natural",
    }:
        fail("invalid pair session binding")
    for arm in ("child", "natural"):
        runtime = pair.get(arm)
        if not isinstance(runtime, dict):
            fail(f"pair session lacks {arm} runtime")
        runner = pathlib.Path(runtime.get("runner", "")).resolve()
        if sha256_file(runner) != runtime.get("executable_sha256"):
            fail(f"pair session {arm} executable hash mismatch")
        binding = arm_session_binding(pair, arm)
        binding_path = args.session_dir / arm / "session-bindings.json"
        if binding_path.exists():
            if load_json(binding_path, f"{arm} session binding") != binding:
                fail(f"pair session {arm} binding mismatch")
        else:
            atomic_json(binding_path, binding)

    for arm in pair["arm_order"]:
        runtime = pair[arm]
        binding_path = args.session_dir / arm / "session-bindings.json"
        output_dir = args.session_dir / arm
        command = [
            runtime["runner"],
            "timing",
            "--point",
            pair["point_id"] if arm == "child" else pair["natural_point_id"],
            "--coordinate",
            pair["coordinate"],
            "--geometries",
            ",".join(pair["geometries"]),
            "--traversal",
            pair["traversal"],
            "--warmups",
            str(pair["warmups"]),
            "--samples",
            str(pair["samples"]),
            "--expected-checksum",
            pair["expected_checksum"],
            "--session-bindings",
            str(binding_path),
            "--output-dir",
            str(output_dir),
        ]
        if args.resume:
            command.append("--resume")
        (output_dir / "command.txt").write_text(shlex_join(command) + "\n")
        with (output_dir / "stdout.jsonl").open("wb") as stdout, (
            output_dir / "stderr.txt"
        ).open("wb") as stderr:
            result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
        if result.returncode != 0:
            fail(f"paired timing {arm} failed with status {result.returncode}")


def shlex_join(command: list[str]) -> str:
    import shlex

    return shlex.join(command)


def paired_checkpoint_reusable(
    checkpoint_path: pathlib.Path,
    bindings_path: pathlib.Path,
    session_dir: pathlib.Path,
) -> tuple[bool, str | None]:
    if not checkpoint_path.exists():
        return False, None
    checkpoint = load_json(checkpoint_path, "paired checkpoint")
    if checkpoint.get("bindings_sha256") != sha256_file(bindings_path):
        fail(f"paired checkpoint binding mismatch: {checkpoint_path}")
    state = checkpoint.get("state")
    if state == "complete":
        if checkpoint.get("evidence_sha256") != recursive_evidence_hash(session_dir):
            fail(f"paired checkpoint evidence mismatch: {checkpoint_path}")
        return True, state
    if state in ("launch_failed", "correctness_failed"):
        return True, state
    if state in ("started", "planned"):
        return False, state
    fail(f"unknown paired checkpoint state: {checkpoint_path}")


def run_envelope_pair(
    *,
    pair: dict[str, Any],
    session_dir: pathlib.Path,
    args: argparse.Namespace,
) -> str:
    session_dir.mkdir(parents=True, exist_ok=True)
    bindings_path = session_dir / "pair-bindings.json"
    checkpoint_path = session_dir / "pair.checkpoint.json"
    if bindings_path.exists():
        if load_json(bindings_path, "pair bindings") != pair:
            fail(f"paired session binding mismatch: {session_dir}")
    else:
        atomic_json(bindings_path, pair)
    reusable, state = paired_checkpoint_reusable(
        checkpoint_path, bindings_path, session_dir
    )
    if reusable:
        return state or "complete"
    if state == "started" and not args.resume:
        fail(f"Started paired session requires --resume: {session_dir}")
    command = [
        str(args.lock_wrapper),
        sys.executable,
        str(pathlib.Path(__file__).resolve()),
        "paired-session",
        "--pair-bindings",
        str(bindings_path),
        "--session-dir",
        str(session_dir),
    ]
    if args.resume:
        command.append("--resume")
    command_text = shlex_join(command)
    (session_dir / "command.txt").write_text(command_text + "\n")
    if args.dry_run:
        atomic_json(
            checkpoint_path,
            {
                "version": 1,
                "point_id": pair["point_id"],
                "coordinate": pair["coordinate"],
                "traversal": pair["traversal"],
                "state": "planned",
                "bindings_sha256": sha256_file(bindings_path),
                "evidence_sha256": "",
            },
        )
        return "planned"
    atomic_json(
        checkpoint_path,
        {
            "version": 1,
            "point_id": pair["point_id"],
            "coordinate": pair["coordinate"],
            "traversal": pair["traversal"],
            "state": "started",
            "bindings_sha256": sha256_file(bindings_path),
            "evidence_sha256": "",
        },
    )
    started_at = time.monotonic()
    with (session_dir / "stdout.lock.txt").open("wb") as stdout, (
        session_dir / "stderr.lock.txt"
    ).open("wb") as stderr:
        result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
    state = "complete" if result.returncode == 0 else "launch_failed"
    evidence_sha256 = recursive_evidence_hash(session_dir)
    atomic_json(
        checkpoint_path,
        {
            "version": 1,
            "point_id": pair["point_id"],
            "coordinate": pair["coordinate"],
            "traversal": pair["traversal"],
            "state": state,
            "exit_code": result.returncode,
            "bindings_sha256": sha256_file(bindings_path),
            "evidence_sha256": evidence_sha256,
            "harness_wall_seconds": time.monotonic() - started_at,
            "stdout_sha256": sha256_file(session_dir / "stdout.lock.txt"),
            "stderr_sha256": sha256_file(session_dir / "stderr.lock.txt"),
        },
    )
    return state


def correctness_point_complete(
    correctness: dict[str, Any], point_id: str
) -> bool:
    row = correctness.get("points", {}).get(point_id)
    if not isinstance(row, dict):
        return False
    if "reused_from" in row:
        row = correctness.get("points", {}).get(row["reused_from"])
    return (
        isinstance(row, dict)
        and row.get("correctness", {}).get("state") == "complete"
        and row.get("sanitizer", {}).get("state") == "complete"
    )


def envelope_campaign(args: argparse.Namespace) -> None:
    catalog = load_json(args.catalog, "point catalog")
    manifest = load_json(args.manifest, "manifest")
    correctness = load_json(args.correctness_evidence, "correctness evidence")
    points = catalog.get("points")
    coordinates = manifest.get("coordinates")
    if not isinstance(points, list) or not points:
        fail("envelope point catalog is empty")
    if not isinstance(coordinates, list) or len(coordinates) != 57:
        fail("envelope timing requires exactly 57 coordinates")
    bundle_hash = sha256_file(args.bundle)
    if catalog.get("bundle_sha256") != bundle_hash:
        fail("envelope timing bundle hash mismatch")
    source_hash = source_tree_sha256(args.source_root)
    build_flags_hash = build_flags_sha256(args.build_flags)
    successful = [point for point in points if point.get("outcome") == "success"]
    candidates = [
        point
        for point in successful
        if point.get("kind") != "natural"
        and correctness_point_complete(correctness, point["point_id"])
    ]
    if not candidates:
        fail("envelope timing has no correctness/sanitizer-valid child points")
    point_by_id = {point["point_id"]: point for point in successful}
    natural_by_geometry = catalog.get("natural_by_geometry")
    if not isinstance(natural_by_geometry, dict):
        fail("envelope catalog lacks natural point bindings")
    for point in candidates:
        if sha256_file(pathlib.Path(point["runner"])) != point["executable_sha256"]:
            fail(f"child executable hash mismatch: {point['point_id']}")
        natural = point_by_id.get(natural_by_geometry.get(point["geometry"]))
        if natural is None or not correctness_point_complete(
            correctness, natural["point_id"]
        ):
            fail(f"natural correctness evidence missing for {point['point_id']}")
        if sha256_file(pathlib.Path(natural["runner"])) != natural["executable_sha256"]:
            fail(f"natural executable hash mismatch: {point['point_id']}")

    selected_points = set(args.point or [])
    selected_coordinates = set(args.coordinate or [])
    if selected_points:
        unknown = selected_points - {point["point_id"] for point in candidates}
        if unknown:
            fail(f"unknown or ineligible selected point: {sorted(unknown)[0]}")
        candidates = [point for point in candidates if point["point_id"] in selected_points]
    selected_rows = [
        row
        for row in coordinates
        if not selected_coordinates or coordinate_name(row) in selected_coordinates
    ]
    total_pair_sessions = envelope_pair_session_count(
        len(candidates), len(selected_rows)
    )
    complete_before = 0
    for point in candidates:
        for row in selected_rows:
            for traversal in TRAVERSALS:
                checkpoint_path = (
                    args.output_root
                    / point["point_id"]
                    / coordinate_stem(row)
                    / traversal
                    / "pair.checkpoint.json"
                )
                if checkpoint_path.exists() and load_json(
                    checkpoint_path, "paired checkpoint"
                ).get("state") == "complete":
                    complete_before += 1
    pilot = load_json(args.pilot_budget, "Task 10 timing budget")
    budget = projected_envelope_budget(
        pilot_wall_seconds=float(pilot["observed_harness_wall_seconds"]),
        pilot_sessions=int(pilot["completed_pilot_sessions"]),
        distinct_point_binaries=len(
            {point["executable_sha256"] for point in successful}
        ),
        total_pair_sessions=total_pair_sessions,
        completed_pair_sessions=min(complete_before, total_pair_sessions),
    )
    budget.update(
        {
            "eligible_child_points": len(candidates),
            "coordinate_count": len(selected_rows),
            "traversal_count": len(TRAVERSALS),
            "all_geometry_outputs_per_runner": len(GEOMETRIES),
            "target_geometry_outputs_used_per_runner": 1,
            "ancillary_geometry_outputs_preserved_per_runner": len(GEOMETRIES) - 1,
            "assumption": (
                "Task 10 pilot wall time per immutable all-five runner; each bounded "
                "pair invokes child and exact natural executables once"
            ),
        }
    )
    atomic_json(args.budget_output, budget)
    print(json.dumps({"timing_budget": budget}), flush=True)

    completed = 0
    reused = 0
    failed = 0
    visited = 0
    started_at = time.monotonic()
    for traversal in TRAVERSALS:
        rows = ordered_coordinates(manifest, traversal)
        for coordinate_index, row in enumerate(rows):
            coordinate = coordinate_name(row)
            if selected_coordinates and coordinate not in selected_coordinates:
                continue
            ordered_ids = rotated_points(
                [point["point_id"] for point in candidates],
                coordinate_index,
                traversal,
            )
            for point_id in ordered_ids:
                point = point_by_id[point_id]
                natural = point_by_id[natural_by_geometry[point["geometry"]]]
                production_path = (
                    args.production_root / coordinate_stem(row) / "input-bindings.json"
                )
                production = load_json(production_path, "production input binding")
                geometries = rotated_geometries(coordinate_index, traversal)
                pair = envelope_session_binding(
                    point=point,
                    natural=natural,
                    row=row,
                    traversal=traversal,
                    geometries=geometries,
                    production=production,
                    bundle_hash=bundle_hash,
                    source_hash=source_hash,
                    build_flags_hash=build_flags_hash,
                )
                session_dir = (
                    args.output_root
                    / point_id
                    / coordinate_stem(row)
                    / traversal
                )
                checkpoint_path = session_dir / "pair.checkpoint.json"
                was_complete = False
                if checkpoint_path.exists():
                    checkpoint = load_json(checkpoint_path, "paired checkpoint")
                    was_complete = checkpoint.get("state") == "complete"
                state = run_envelope_pair(
                    pair=pair, session_dir=session_dir, args=args
                )
                if state == "complete":
                    if was_complete:
                        reused += 1
                    else:
                        completed += 1
                elif state == "planned":
                    pass
                else:
                    failed += 1
                visited += 1
                elapsed = max(time.monotonic() - started_at, 1e-9)
                eta = elapsed / visited * (total_pair_sessions - visited)
                print(
                    json.dumps(
                        {
                            "pair_session": visited,
                            "total_pair_sessions": total_pair_sessions,
                            "point": point_id,
                            "coordinate": coordinate,
                            "traversal": traversal,
                            "state": state,
                            "completed": completed,
                            "reused": reused,
                            "failed": failed,
                            "eta_seconds": eta,
                        }
                    ),
                    flush=True,
                )
    summary = {
        "version": 1,
        "catalog_sha256": sha256_file(args.catalog),
        "correctness_evidence_sha256": sha256_file(args.correctness_evidence),
        "eligible_child_points": len(candidates),
        "visited_pair_sessions": visited,
        "completed_pair_sessions": completed,
        "reused_pair_sessions": reused,
        "failed_pair_sessions": failed,
        "dry_run": args.dry_run,
    }
    atomic_json(args.output_root / "campaign-summary.json", summary)
    if failed:
        fail(f"envelope timing preserved {failed} failed paired sessions")
    print("R0_ENVELOPE_TIMING_OK")


def path_argument(value: str) -> pathlib.Path:
    return pathlib.Path(value).resolve()


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser()
    subcommands = result.add_subparsers(dest="command", required=True)
    run = subcommands.add_parser("run")
    run.add_argument("--manifest", type=path_argument, required=True)
    run.add_argument("--runner", type=path_argument, required=True)
    run.add_argument("--lock-wrapper", type=path_argument, required=True)
    run.add_argument("--bundle", type=path_argument, required=True)
    run.add_argument("--source-root", type=path_argument, required=True)
    run.add_argument("--build-flags", type=path_argument, required=True)
    run.add_argument("--production-root", type=path_argument, required=True)
    run.add_argument("--output-root", type=path_argument, required=True)
    run.add_argument("--resume", action="store_true")
    run.add_argument("--coordinate", action="append")
    run.add_argument("--pilot", action="store_true")
    prepare = subcommands.add_parser("prepare")
    prepare.add_argument("--manifest", type=path_argument, required=True)
    prepare.add_argument("--runner", type=path_argument, required=True)
    prepare.add_argument("--lock-wrapper", type=path_argument, required=True)
    prepare.add_argument("--output-root", type=path_argument, required=True)
    prepare.add_argument("--resume", action="store_true")
    prepare.add_argument("--coordinate", action="append")
    prepare.add_argument("--pilot", action="store_true")
    budget = subcommands.add_parser("budget")
    budget.add_argument("--manifest", type=path_argument, required=True)
    budget.add_argument("--timing-root", type=path_argument, required=True)
    budget.add_argument("--output", type=path_argument, required=True)
    envelope = subcommands.add_parser("envelope")
    envelope.add_argument("--catalog", type=path_argument, required=True)
    envelope.add_argument("--manifest", type=path_argument, required=True)
    envelope.add_argument("--correctness-evidence", type=path_argument, required=True)
    envelope.add_argument("--production-root", type=path_argument, required=True)
    envelope.add_argument("--bundle", type=path_argument, required=True)
    envelope.add_argument("--source-root", type=path_argument, required=True)
    envelope.add_argument("--build-flags", type=path_argument, required=True)
    envelope.add_argument("--lock-wrapper", type=path_argument, required=True)
    envelope.add_argument("--output-root", type=path_argument, required=True)
    envelope.add_argument("--pilot-budget", type=path_argument, required=True)
    envelope.add_argument("--budget-output", type=path_argument, required=True)
    envelope.add_argument("--point", action="append")
    envelope.add_argument("--coordinate", action="append")
    envelope.add_argument("--resume", action="store_true")
    envelope.add_argument("--dry-run", action="store_true")
    paired = subcommands.add_parser("paired-session")
    paired.add_argument("--pair-bindings", type=path_argument, required=True)
    paired.add_argument("--session-dir", type=path_argument, required=True)
    paired.add_argument("--resume", action="store_true")
    return result


def main() -> None:
    args = parser().parse_args()
    if args.command == "run":
        run_campaign(args)
    elif args.command == "prepare":
        prepare_production(args)
    elif args.command == "budget":
        timing_budget(args)
    elif args.command == "envelope":
        envelope_campaign(args)
    elif args.command == "paired-session":
        paired_session(args)
    else:
        fail(f"unknown command {args.command}")


if __name__ == "__main__":
    main()
