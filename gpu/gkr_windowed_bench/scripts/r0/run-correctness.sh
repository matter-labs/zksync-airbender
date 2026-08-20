#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$script_dir/../../../.." && pwd)
cd "$repo_root"

if [[ "${1:-}" == envelope ]]; then
  shift
  exec python3 - "$repo_root" "$@" <<'PY'
from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import shlex
import subprocess
import sys
import tempfile
import time
from typing import Any


REPO_ROOT = pathlib.Path(sys.argv[1])
GEOMETRIES = {
    "cta288_pair",
    "cta96_partitioned",
    "cta96_x0_major",
    "cta96_x1_major",
    "cta96_x2_major",
}
LOGS = (3, 8)
SEEDS = (0, 1, 0xDEAD_BEEF_CAFE_BABE)
HASH_FIELDS = (
    "bundle_sha256",
    "coordinate_sha256",
    "input_sha256",
    "source_data_sha256",
    "independent_source_sha256",
    "derived_source_sha256",
    "coefficient_sha256",
    "direct_eq_sha256",
    "factored_eq_sha256",
)


def fail(message: str) -> "NoReturn":
    raise SystemExit(message)


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_json(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def validate_hash(name: str, value: Any, *, optional: bool = False) -> str | None:
    if optional and value is None:
        return None
    if not isinstance(value, str) or len(value) != 64 or any(
        byte not in "0123456789abcdef" for byte in value
    ):
        fail(f"{name} is not lowercase SHA-256")
    return value


def atomic_json(path: pathlib.Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = (json.dumps(value, separators=(",", ":")) + "\n").encode()
    descriptor, name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = pathlib.Path(name)
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


def load_json(path: pathlib.Path) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        fail(f"read {path}: {error}")


def load_jsonl(path: pathlib.Path) -> list[dict[str, Any]]:
    rows = []
    try:
        for line_number, line in enumerate(path.read_text().splitlines(), 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                fail(f"{path}:{line_number}: row is not an object")
            rows.append(row)
    except (OSError, json.JSONDecodeError) as error:
        fail(f"read {path}: {error}")
    return rows


def coordinate_name(row: dict[str, Any]) -> str:
    return f"{row['circuit']}:{row['layer']}"


def coordinate_stem(row: dict[str, Any]) -> str:
    return f"{row['circuit']}-l{row['layer']}"


def group_key(point: dict[str, Any]) -> tuple[str, ...]:
    return (
        point["executable_sha256"],
        point["symbol"],
        point["geometry"],
        point["bundle_sha256"],
        point["correctness_spec_sha256"],
        point["sanitizer_spec_sha256"],
    )


def semantic_bindings_digest(rows: list[dict[str, Any]]) -> str:
    values = []
    for row in rows:
        binding = {}
        for field in HASH_FIELDS:
            value = row.get(field)
            binding[field] = validate_hash(
                f"correctness {field}", value, optional=field == "derived_source_sha256"
            )
        values.append(
            {
                "circuit": row.get("circuit"),
                "layer": row.get("layer"),
                "log_trace": row.get("log_trace"),
                "seed": row.get("seed"),
                "bindings": binding,
            }
        )
    return sha256_json(values)


def validate_rows(
    rows: list[dict[str, Any]],
    *,
    point: dict[str, Any],
    coordinate: dict[str, Any] | None,
    sanitizer: bool,
) -> str:
    expected_logs = (8,) if sanitizer else LOGS
    expected_seeds = (0,) if sanitizer else SEEDS
    coordinates = (
        {(coordinate["circuit"], coordinate["layer"])}
        if coordinate is not None
        else {(row.get("circuit"), row.get("layer")) for row in rows}
    )
    expected = {
        (circuit, layer, log_trace, seed, point["geometry"])
        for circuit, layer in coordinates
        for log_trace in expected_logs
        for seed in expected_seeds
    }
    observed = {
        (
            row.get("circuit"),
            row.get("layer"),
            row.get("log_trace"),
            row.get("seed"),
            row.get("geometry"),
        )
        for row in rows
    }
    if observed != expected or len(rows) != len(expected):
        fail(
            f"correctness row coverage mismatch for {point['point_id']}: "
            f"expected={len(expected)} observed={len(rows)}"
        )
    for row in rows:
        if row.get("version") != 1 or row.get("passing") is not True:
            fail(f"nonpassing correctness row for {point['point_id']}")
        for field in (
            "canonical_q_matches_compiled",
            "gpu_matches_canonical_q",
            "gpu_matches_compiled_q",
        ):
            if row.get(field) is not True:
                fail(f"correctness comparison {field} failed for {point['point_id']}")
        for field in (
            "canonical_p_sha256",
            "canonical_q_sha256",
            "compiled_q_sha256",
            "p_minus_q_sha256",
            "checksum",
        ):
            validate_hash(f"correctness {field}", row.get(field))
        if row.get("executable_sha256") != point["executable_sha256"]:
            fail(f"correctness executable mismatch for {point['point_id']}")
        if row.get("bundle_sha256") != point["bundle_sha256"]:
            fail(f"correctness bundle mismatch for {point['point_id']}")
        launch = row.get("launch")
        if not isinstance(launch, dict) or launch.get("symbol") != point["symbol"]:
            fail(f"correctness launch symbol mismatch for {point['point_id']}")
        cells = row.get("cells")
        if not isinstance(cells, list) or len(cells) != 27 or any(
            not isinstance(cell, dict)
            or not isinstance(cell.get("limbs"), list)
            or len(cell["limbs"]) != 4
            for cell in cells
        ):
            fail(f"correctness literal cell coverage mismatch for {point['point_id']}")
    return semantic_bindings_digest(sorted(rows, key=lambda row: (
        row["circuit"], row["layer"], row["log_trace"], row["seed"]
    )))


def checkpoint_is_terminal(
    checkpoint_path: pathlib.Path, command_sha256: str, stdout_path: pathlib.Path
) -> bool:
    if not checkpoint_path.exists():
        return False
    checkpoint = load_json(checkpoint_path)
    if checkpoint.get("command_sha256") != command_sha256:
        fail(f"checkpoint command binding mismatch: {checkpoint_path}")
    state = checkpoint.get("state")
    if state in ("complete", "launch_failed", "correctness_failed", "sanitizer_failed"):
        if checkpoint.get("stdout_sha256") != sha256_file(stdout_path):
            fail(f"checkpoint stdout binding mismatch: {checkpoint_path}")
        return True
    if state == "started":
        return False
    fail(f"unknown checkpoint state: {checkpoint_path}")


def write_command(path: pathlib.Path, command: list[str], point: dict[str, Any]) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    command_text = shlex.join(command)
    path.write_text(
        f"point_id={point['point_id']}\n"
        f"executable_sha256={point['executable_sha256']}\n"
        f"symbol={point['symbol']}\n"
        f"geometry={point['geometry']}\n"
        f"command={command_text}\n"
    )
    return hashlib.sha256(command_text.encode()).hexdigest()


def classify_failure(stdout_path: pathlib.Path, sanitizer: bool) -> str:
    if sanitizer:
        return "sanitizer_failed"
    try:
        rows = load_jsonl(stdout_path)
    except SystemExit:
        rows = []
    if any(row.get("passing") is False for row in rows):
        return "correctness_failed"
    return "launch_failed"


def run_focused(
    point: dict[str, Any],
    coordinates: list[dict[str, Any]],
    args: argparse.Namespace,
) -> dict[str, Any]:
    point_root = args.output_root / point["point_id"] / "focused"
    all_rows = []
    terminal_failure = None
    started_at = time.monotonic()
    for index, coordinate in enumerate(coordinates, 1):
        directory = point_root / coordinate_stem(coordinate)
        stdout_path = directory / "rows.jsonl"
        stderr_path = directory / "stderr.lock.txt"
        command_path = directory / "command.txt"
        checkpoint_path = directory / "checkpoint.json"
        command = [
            str(args.lock_wrapper),
            point["runner"],
            "correctness",
            "--coordinate",
            coordinate_name(coordinate),
            "--logs",
            "3,8",
            "--seeds",
            "0,1,16045690984503098046",
            "--geometries",
            point["geometry"],
        ]
        command_sha256 = write_command(command_path, command, point)
        if checkpoint_is_terminal(checkpoint_path, command_sha256, stdout_path):
            checkpoint = load_json(checkpoint_path)
        elif args.dry_run:
            checkpoint = {
                "version": 1,
                "point_id": point["point_id"],
                "coordinate": coordinate_name(coordinate),
                "state": "planned",
                "command_sha256": command_sha256,
            }
            atomic_json(checkpoint_path, checkpoint)
        else:
            if checkpoint_path.exists() and not args.resume:
                fail(f"Started correctness checkpoint requires --resume: {checkpoint_path}")
            atomic_json(
                checkpoint_path,
                {
                    "version": 1,
                    "point_id": point["point_id"],
                    "coordinate": coordinate_name(coordinate),
                    "state": "started",
                    "command_sha256": command_sha256,
                    "stdout_sha256": "",
                },
            )
            directory.mkdir(parents=True, exist_ok=True)
            with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
                result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
            state = "complete"
            if result.returncode == 0:
                try:
                    validate_rows(
                        load_jsonl(stdout_path),
                        point=point,
                        coordinate=coordinate,
                        sanitizer=False,
                    )
                except SystemExit:
                    state = "correctness_failed"
            else:
                state = classify_failure(stdout_path, False)
            checkpoint = {
                "version": 1,
                "point_id": point["point_id"],
                "coordinate": coordinate_name(coordinate),
                "state": state,
                "exit_code": result.returncode,
                "command_sha256": command_sha256,
                "stdout_sha256": sha256_file(stdout_path),
                "stderr_sha256": sha256_file(stderr_path),
            }
            atomic_json(checkpoint_path, checkpoint)
        if checkpoint["state"] == "complete":
            all_rows.extend(load_jsonl(stdout_path))
        elif checkpoint["state"] != "planned" and terminal_failure is None:
            terminal_failure = checkpoint["state"]
        elapsed = max(time.monotonic() - started_at, 1e-9)
        eta = elapsed / index * (len(coordinates) - index)
        print(
            json.dumps(
                {
                    "phase": "focused",
                    "point": point["point_id"],
                    "coordinate": index,
                    "coordinates": len(coordinates),
                    "state": checkpoint["state"],
                    "eta_seconds": eta,
                }
            ),
            flush=True,
        )
    if args.dry_run:
        return {"state": "planned", "coordinate_count": len(coordinates)}
    if terminal_failure is not None:
        return {"state": terminal_failure, "passing_rows": len(all_rows)}
    digest = validate_rows(all_rows, point=point, coordinate=None, sanitizer=False)
    return {
        "state": "complete",
        "coordinate_count": len(coordinates),
        "row_count": len(all_rows),
        "input_bindings_sha256": digest,
    }


def run_sanitizer(
    point: dict[str, Any],
    coordinates: list[dict[str, Any]],
    args: argparse.Namespace,
) -> dict[str, Any]:
    directory = args.output_root / point["point_id"] / "sanitizer"
    stdout_path = directory / "rows.jsonl"
    stderr_path = directory / "stderr.lock.txt"
    sanitizer_log = directory / "memcheck.log"
    command_path = directory / "command.txt"
    checkpoint_path = directory / "checkpoint.json"
    command = [
        str(args.lock_wrapper),
        "compute-sanitizer",
        "--tool",
        "memcheck",
        "--target-processes",
        "all",
        "--error-exitcode",
        "99",
        "--log-file",
        str(sanitizer_log.resolve()),
        point["runner"],
        "correctness",
        "--all",
        "--logs",
        "8",
        "--seeds",
        "0",
        "--geometries",
        point["geometry"],
    ]
    command_sha256 = write_command(command_path, command, point)
    if checkpoint_is_terminal(checkpoint_path, command_sha256, stdout_path):
        checkpoint = load_json(checkpoint_path)
    elif args.dry_run:
        checkpoint = {
            "version": 1,
            "point_id": point["point_id"],
            "state": "planned",
            "command_sha256": command_sha256,
        }
        atomic_json(checkpoint_path, checkpoint)
    else:
        if checkpoint_path.exists() and not args.resume:
            fail(f"Started sanitizer checkpoint requires --resume: {checkpoint_path}")
        atomic_json(
            checkpoint_path,
            {
                "version": 1,
                "point_id": point["point_id"],
                "state": "started",
                "command_sha256": command_sha256,
                "stdout_sha256": "",
            },
        )
        directory.mkdir(parents=True, exist_ok=True)
        with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
            result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
        state = "complete"
        if result.returncode != 0:
            state = "sanitizer_failed"
        else:
            try:
                rows = load_jsonl(stdout_path)
                if len(rows) != len(coordinates):
                    fail("sanitizer did not emit literal 57-coordinate coverage")
                validate_rows(rows, point=point, coordinate=None, sanitizer=True)
                if "ERROR SUMMARY: 0 errors" not in sanitizer_log.read_text():
                    fail("sanitizer log lacks literal zero-error summary")
            except (OSError, SystemExit):
                state = "sanitizer_failed"
        checkpoint = {
            "version": 1,
            "point_id": point["point_id"],
            "state": state,
            "exit_code": result.returncode,
            "command_sha256": command_sha256,
            "stdout_sha256": sha256_file(stdout_path),
            "stderr_sha256": sha256_file(stderr_path),
            "sanitizer_log_sha256": sha256_file(sanitizer_log)
            if sanitizer_log.is_file()
            else None,
        }
        atomic_json(checkpoint_path, checkpoint)
    if checkpoint["state"] == "planned":
        return {"state": "planned"}
    if checkpoint["state"] != "complete":
        return {"state": "sanitizer_failed"}
    rows = load_jsonl(stdout_path)
    return {
        "state": "complete",
        "coordinate_count": len(coordinates),
        "row_count": len(rows),
        "input_bindings_sha256": validate_rows(
            rows, point=point, coordinate=None, sanitizer=True
        ),
        "error_summary": "ERROR SUMMARY: 0 errors",
    }


def parse_args(values: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=pathlib.Path, required=True)
    parser.add_argument("--manifest", type=pathlib.Path, required=True)
    parser.add_argument("--lock-wrapper", type=pathlib.Path, required=True)
    parser.add_argument("--output-root", type=pathlib.Path, required=True)
    parser.add_argument("--phase", choices=("focused", "sanitizer", "all"), default="all")
    parser.add_argument("--point", action="append")
    parser.add_argument("--coordinate", action="append")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args(values)
    for field in ("catalog", "manifest", "lock_wrapper", "output_root"):
        setattr(args, field, getattr(args, field).resolve())
    return args


def main(values: list[str]) -> None:
    args = parse_args(values)
    catalog = load_json(args.catalog)
    manifest = load_json(args.manifest)
    coordinates = manifest.get("coordinates") if isinstance(manifest, dict) else None
    points = catalog.get("points") if isinstance(catalog, dict) else None
    if not isinstance(coordinates, list) or len(coordinates) != 57:
        fail("correctness campaign requires exactly 57 coordinates")
    if not isinstance(points, list) or not points:
        fail("correctness campaign point catalog is empty")
    args.output_root.mkdir(parents=True, exist_ok=True)
    selected_coordinates = set(args.coordinate or [])
    if selected_coordinates:
        known_coordinates = {coordinate_name(row) for row in coordinates}
        unknown = selected_coordinates - known_coordinates
        if unknown:
            fail(f"unknown selected correctness coordinate: {sorted(unknown)[0]}")
        coordinates = [
            row for row in coordinates if coordinate_name(row) in selected_coordinates
        ]
    representatives: dict[tuple[str, ...], str] = {}
    aliases: dict[str, str] = {}
    evidence: dict[str, Any] = {}
    successful = [point for point in points if point.get("outcome") == "success"]
    selected_points = set(args.point or [])
    if selected_points:
        unknown = selected_points - {point["point_id"] for point in successful}
        if unknown:
            fail(f"unknown selected correctness point: {sorted(unknown)[0]}")
        successful = [
            point for point in successful if point["point_id"] in selected_points
        ]
    for point in successful:
        if sha256_file(pathlib.Path(point["runner"])) != point["executable_sha256"]:
            fail(f"live point executable hash mismatch: {point['point_id']}")
        key = group_key(point)
        if key in representatives:
            aliases[point["point_id"]] = representatives[key]
        else:
            representatives[key] = point["point_id"]

    point_by_id = {point["point_id"]: point for point in successful}
    representative_ids = set(representatives.values())
    for index, point in enumerate(successful, 1):
        point_id = point["point_id"]
        point_root = args.output_root / point_id
        if point_id not in representative_ids:
            representative = aliases[point_id]
            representative_evidence = evidence.get(representative)
            if representative_evidence is None:
                fail(f"dedup representative not completed before alias: {point_id}")
            row = {"version": 1, "point_id": point_id, "reused_from": representative}
            atomic_json(point_root / "evidence.json", row)
            evidence[point_id] = row
            continue
        row: dict[str, Any] = {"version": 1, "point_id": point_id}
        if args.phase in ("focused", "all"):
            row["correctness"] = run_focused(point, coordinates, args)
        elif (point_root / "evidence.json").exists():
            row.update(load_json(point_root / "evidence.json"))
        if args.phase in ("sanitizer", "all"):
            row["sanitizer"] = run_sanitizer(point, coordinates, args)
        elif (point_root / "evidence.json").exists():
            existing = load_json(point_root / "evidence.json")
            if "sanitizer" in existing:
                row["sanitizer"] = existing["sanitizer"]
        atomic_json(point_root / "evidence.json", row)
        evidence[point_id] = row
        print(
            json.dumps(
                {
                    "point": index,
                    "points": len(successful),
                    "point_id": point_id,
                    "correctness": row.get("correctness", {}).get("state"),
                    "sanitizer": row.get("sanitizer", {}).get("state"),
                }
            ),
            flush=True,
        )
    summary = {
        "version": 1,
        "catalog_sha256": sha256_file(args.catalog),
        "manifest_sha256": sha256_file(args.manifest),
        "point_count": len(points),
        "successful_point_count": len(successful),
        "unique_evidence_groups": len(representatives),
        "aliases": aliases,
        "points": evidence,
        "dry_run": args.dry_run,
    }
    atomic_json(args.output_root / "evidence.json", summary)
    required_phases = {
        "focused": ("correctness",),
        "sanitizer": ("sanitizer",),
        "all": ("correctness", "sanitizer"),
    }[args.phase]
    if not args.dry_run and any(
        row.get("reused_from") is None
        and any(row.get(phase, {}).get("state") != "complete" for phase in required_phases)
        for row in evidence.values()
    ):
        fail("one or more envelope correctness/sanitizer groups failed")
    print("R0_ENVELOPE_CORRECTNESS_SANITIZERS_OK")


main(sys.argv[2:])
PY
fi

binary=${1:-target/release/run_windowed_r0_corpus}
binary=$(realpath -- "$binary")
test -x "$binary"

output_root=${R0_CORRECTNESS_OUTPUT_ROOT:-target/windowed-gkr-r0-corpus/correctness/r0-all-corpus-correctness/sanitizers}
mkdir -p "$output_root"
binary_sha256=$(sha256sum "$binary" | awk '{print $1}')
printf 'executable\tsha256\n%s\t%s\n' "$binary" "$binary_sha256" > "$output_root/executable.tsv"

geometries=(
  cta288_pair
  cta96_partitioned
  cta96_x0_major
  cta96_x1_major
  cta96_x2_major
)

for geometry in "${geometries[@]}"; do
  jsonl="$output_root/${geometry}.jsonl"
  sanitizer_log="$output_root/${geometry}.memcheck.log"
  driver_log="$output_root/${geometry}.driver.log"
  command_log="$output_root/${geometry}.command.txt"
  command=(
    compute-sanitizer
    --tool memcheck
    --target-processes all
    --error-exitcode 99
    --log-file "$sanitizer_log"
    "$binary"
    correctness
    --all
    --logs 8
    --seeds 0
    --geometries "$geometry"
  )
  {
    printf 'executable_sha256=%s\n' "$binary_sha256"
    printf 'command='
    printf '%q ' .agents/bin/with_gpu_lock.sh "${command[@]}"
    printf '\n'
  } > "$command_log"

  .agents/bin/with_gpu_lock.sh "${command[@]}" > "$jsonl" 2> "$driver_log"
  python3 - "$jsonl" "$geometry" "$binary_sha256" <<'PY'
import json
import sys

path, geometry, executable_sha256 = sys.argv[1:]
with open(path, encoding="utf-8") as source:
    rows = [json.loads(line) for line in source if line.strip()]
assert len(rows) == 57, (geometry, len(rows))
keys = {(row["circuit"], row["layer"], row["log_trace"], row["seed"], row["geometry"]) for row in rows}
assert len(keys) == 57, (geometry, len(keys))
for row in rows:
    assert row["geometry"] == geometry
    assert row["log_trace"] == 8 and row["seed"] == 0
    assert row["passing"] is True
    assert row["canonical_q_matches_compiled"] is True
    assert row["gpu_matches_canonical_q"] is True
    assert row["gpu_matches_compiled_q"] is True
    assert row["executable_sha256"] == executable_sha256
    assert len(row["cells"]) == 27
    assert all(len(cell["limbs"]) == 4 for cell in row["cells"])
PY
  rg -q 'ERROR SUMMARY: 0 errors' "$sanitizer_log"
  sha256sum "$jsonl" "$sanitizer_log" "$driver_log" "$command_log" > "$output_root/${geometry}.sha256"
done

printf 'R0_CORRECTNESS_SANITIZERS_OK\n'
