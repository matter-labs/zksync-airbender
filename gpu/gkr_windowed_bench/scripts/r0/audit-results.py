#!/usr/bin/env python3
"""Fail-closed audit and natural timing report for the R0 campaign."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import pathlib
import sqlite3
import statistics
from collections import defaultdict
from typing import Any


GEOMETRIES = [
    "cta288_pair",
    "cta96_partitioned",
    "cta96_x0_major",
    "cta96_x1_major",
    "cta96_x2_major",
]
TRAVERSALS = ("forward", "reverse")
R0_PRODUCTION_SEED = 0xDEAD_BEEF_CAFE_BABE
CURRENT_BASE_WEIGHT_KEYS = {
    "add_sub_lui_auipc_mop": "add_sub",
    "bigint_with_extended_control": "bigint",
    "inits_and_teardowns": "initial",
    "jump_branch_slt": "jump",
    "keccak_special5": "keccak",
    "mem_subword_only": "mem_subword",
    "mem_word_only": "mem_word",
    "shift_binop": "shift",
    "unsigned_mul_div": "mul_div",
}


def fail(message: str) -> "NoReturn":
    raise SystemExit(message)


def load_json(path: pathlib.Path) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        fail(f"read {path}: {error}")


def load_jsonl(path: pathlib.Path) -> list[dict[str, Any]]:
    rows = []
    try:
        for line_number, line in enumerate(path.read_text().splitlines(), 1):
            value = json.loads(line)
            if not isinstance(value, dict):
                fail(f"{path}:{line_number}: row is not an object")
            rows.append(value)
    except (OSError, json.JSONDecodeError) as error:
        fail(f"read {path}: {error}")
    return rows


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_json(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def cells_sha256(cells: Any) -> str:
    if not isinstance(cells, list) or len(cells) != 27:
        fail("R0 result must contain exactly 27 cells")
    digest = hashlib.sha256()
    for cell_index, cell in enumerate(cells):
        limbs = cell.get("limbs") if isinstance(cell, dict) else None
        if not isinstance(limbs, list) or len(limbs) != 4:
            fail(f"R0 result cell {cell_index} must contain four limbs")
        for limb in limbs:
            if not isinstance(limb, int) or isinstance(limb, bool) or not 0 <= limb <= 0xFFFFFFFF:
                fail(f"R0 result cell {cell_index} has an invalid limb")
            digest.update(limb.to_bytes(4, "little"))
    return digest.hexdigest()


def validate_hash(name: str, value: Any) -> str:
    if not isinstance(value, str) or len(value) != 64 or any(
        byte not in "0123456789abcdef" for byte in value
    ):
        fail(f"{name} is not lowercase SHA-256")
    return value


def exact_json_equal(actual: Any, expected: Any) -> bool:
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(
            exact_json_equal(actual[key], value) for key, value in expected.items()
        )
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(
            exact_json_equal(actual_value, expected_value)
            for actual_value, expected_value in zip(actual, expected, strict=True)
        )
    return actual == expected


def combined_rows_hash(session_dir: pathlib.Path) -> str:
    digest = hashlib.sha256()
    for geometry in GEOMETRIES:
        path = session_dir / f"{geometry}.samples.jsonl"
        relative = path.name.encode()
        contents = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "little"))
        digest.update(relative)
        digest.update(len(contents).to_bytes(8, "little"))
        digest.update(contents)
    return digest.hexdigest()


def source_tree_sha256(root: pathlib.Path) -> str:
    candidates = []
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


def build_flags_sha256(path: pathlib.Path) -> str:
    preimage = path.read_bytes()
    if preimage.endswith(b"\n"):
        preimage = preimage[:-1]
    return hashlib.sha256(preimage).hexdigest()


def row_field(row: dict[str, Any], field: str) -> Any:
    key = row.get("key")
    if isinstance(key, dict) and field in key:
        return key[field]
    return row.get(field)


def coordinate_name(row: dict[str, Any]) -> str:
    return f"{row['circuit']}:{row['layer']}"


def coordinate_stem(row: dict[str, Any]) -> str:
    return f"{row['circuit']}-l{row['layer']}"


def expected_result_key(
    row: dict[str, Any], geometry: str, traversal: str | None
) -> dict[str, Any]:
    trace_len = row.get("trace_len")
    if not isinstance(trace_len, int) or trace_len <= 0 or trace_len & (trace_len - 1):
        fail(f"manifest trace length is not a positive power of two: {coordinate_name(row)}")
    return {
        "point": "natural",
        "circuit": row["circuit"],
        "layer": row["layer"],
        "log_trace": trace_len.bit_length() - 1,
        "seed": R0_PRODUCTION_SEED,
        "geometry": geometry,
        "traversal": traversal,
    }


def expected_launches(row: dict[str, Any]) -> list[dict[str, Any]]:
    production_rows = row["trace_len"] // 8
    if production_rows % 32:
        fail(f"production rows are not divisible by 32: {coordinate_name(row)}")
    base_grid = production_rows // 32
    return [
        {
            "geometry": geometry,
            "symbol": f"ab_gkr_windowed_r0_{geometry}_kernel",
            "grid": [base_grid * (3 if geometry == "cta96_partitioned" else 1), 1, 1],
            "block": [288 if geometry == "cta288_pair" else 96, 1, 1],
        }
        for geometry in GEOMETRIES
    ]


def comparison(reference: float, candidate: float) -> tuple[float, str]:
    if reference <= 0.0 or candidate <= 0.0:
        fail("timing medians must be positive")
    speedup = reference / candidate
    if candidate < reference:
        percent = (reference / candidate - 1.0) * 100.0
        wording = f"{percent:.3f}% faster"
    elif candidate > reference:
        percent = (candidate / reference - 1.0) * 100.0
        wording = f"{percent:.3f}% slower"
    else:
        wording = "0.000% faster"
    return speedup, wording


def point_evidence_key(point: dict[str, Any]) -> tuple[str, str, str, str, str, str]:
    point_id = point.get("point_id")
    if not isinstance(point_id, str) or not point_id:
        fail("point_id must be a nonempty string")
    values = []
    for field in (
        "executable_sha256",
        "bundle_sha256",
        "correctness_input_bindings_sha256",
        "sanitizer_input_bindings_sha256",
    ):
        values.append(validate_hash(f"{point_id} {field}", point.get(field)))
    geometry = point.get("geometry")
    symbol = point.get("symbol")
    if geometry not in GEOMETRIES:
        fail(f"{point_id} has invalid geometry")
    if not isinstance(symbol, str) or not symbol:
        fail(f"{point_id} has invalid symbol")
    return (values[0], symbol, geometry, values[1], values[2], values[3])


def envelope_dedup_audit(args: argparse.Namespace) -> None:
    catalog = load_json(args.points)
    evidence = load_json(args.evidence)
    points = catalog.get("points") if isinstance(catalog, dict) else None
    evidence_points = evidence.get("points") if isinstance(evidence, dict) else None
    if not isinstance(points, list) or not points:
        fail("envelope point catalog must contain points")
    if not isinstance(evidence_points, dict):
        fail("envelope evidence must contain a point map")

    representatives_by_key: dict[tuple[str, str, str, str, str, str], str] = {}
    representatives: list[str] = []
    reuse: dict[str, str] = {}
    seen_ids: set[str] = set()
    for point in points:
        if not isinstance(point, dict):
            fail("envelope point is not an object")
        point_id = point.get("point_id")
        if not isinstance(point_id, str) or point_id in seen_ids:
            fail(f"duplicate or invalid point id: {point_id!r}")
        seen_ids.add(point_id)
        key = point_evidence_key(point)
        representative = representatives_by_key.get(key)
        if representative is None:
            representatives_by_key[key] = point_id
            representatives.append(point_id)
        else:
            reuse[point_id] = representative

    if set(evidence_points) != seen_ids:
        fail("envelope evidence point coverage mismatch")
    for point_id in representatives:
        row = evidence_points[point_id]
        if not isinstance(row, dict):
            fail(f"invalid evidence row for {point_id}")
        if "reused_from" in row:
            fail(f"deduplication binding mismatch for {point_id}")
        if row.get("correctness") != "complete":
            fail(f"complete correctness evidence missing for {point_id}")
        if row.get("sanitizer") != "complete":
            fail(f"complete sanitizer evidence missing for {point_id}")
        if row.get("fully_timed") is not True:
            fail(f"complete timing evidence missing for {point_id}")
    for point_id, representative in reuse.items():
        row = evidence_points[point_id]
        if not isinstance(row, dict) or row != {"reused_from": representative}:
            fail(f"deduplication binding mismatch for {point_id}")

    result = {
        "version": 1,
        "point_count": len(points),
        "unique_evidence_groups": len(representatives),
        "representatives": representatives,
        "reuse": reuse,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print("WINDOWED_R0_ENVELOPE_DEDUP_AUDIT_OK")


def envelope_resource_comparison(
    point: dict[str, Any],
    natural: dict[str, Any],
    *,
    candidate_median_ms: float,
    natural_median_ms: float,
) -> dict[str, Any]:
    speedup, wording = comparison(natural_median_ms, candidate_median_ms)
    point_opcodes = point.get("opcodes")
    natural_opcodes = natural.get("opcodes")
    if not isinstance(point_opcodes, dict) or not isinstance(natural_opcodes, dict):
        fail("envelope resources must contain opcode maps")
    opcode_names = sorted(set(point_opcodes) | set(natural_opcodes))
    opcode_changes = {}
    for name in opcode_names:
        candidate_value = point_opcodes.get(name, 0)
        natural_value = natural_opcodes.get(name, 0)
        if type(candidate_value) is not int or type(natural_value) is not int:
            fail(f"invalid opcode count for {name}")
        delta = candidate_value - natural_value
        if delta:
            opcode_changes[name] = delta
    return {
        "median_ms": candidate_median_ms,
        "natural_median_ms": natural_median_ms,
        "speedup": speedup,
        "wording": wording,
        "registers": point.get("registers"),
        "stack_bytes": point.get("stack_bytes"),
        "local_bytes": point.get("local_bytes"),
        "shared_bytes": point.get("shared_bytes"),
        "spill_loads": point.get("ldl"),
        "spill_stores": point.get("stl"),
        "actual_active_blocks": point.get("inferred_active_blocks"),
        "occupancy": point.get("inferred_occupancy"),
        "opcode_changes": opcode_changes,
    }


def envelope_disposition(
    build_outcome: str,
    correctness_state: str | None,
    sanitizer_state: str | None,
    timing_state: str | None,
) -> str:
    if build_outcome != "success":
        return "compile-failed"
    if correctness_state == "launch_failed":
        return "launch-failed"
    if correctness_state != "complete":
        return "correctness-failed"
    if sanitizer_state != "complete":
        return "sanitizer-failed"
    if timing_state == "complete":
        return "fully-timed"
    return "launch-failed"


def envelope_catalog(args: argparse.Namespace) -> None:
    manifest = load_json(args.manifest)
    coordinates = manifest.get("coordinates") if isinstance(manifest, dict) else None
    if not isinstance(coordinates, list) or len(coordinates) != 57:
        fail("envelope catalog requires exactly 57 coordinates")
    bundle_hash = sha256_file(args.bundle)
    if manifest.get("bundle_sha256") != bundle_hash:
        fail("envelope catalog bundle hash mismatch")

    try:
        with args.point_dag.open(newline="") as stream:
            dag_rows = list(csv.DictReader(stream, delimiter="\t"))
    except OSError as error:
        fail(f"read {args.point_dag}: {error}")
    if not dag_rows:
        fail("envelope point DAG is empty")

    correctness_spec = {
        "bundle_sha256": bundle_hash,
        "coordinates": [
            [row.get("circuit"), row.get("layer"), row.get("payload_sha256")]
            for row in coordinates
        ],
        "logs": [3, 8],
        "seeds": [0, 1, 0xDEAD_BEEF_CAFE_BABE],
    }
    sanitizer_spec = {
        "bundle_sha256": bundle_hash,
        "coordinates": correctness_spec["coordinates"],
        "log": 8,
        "seed": 0,
    }
    points = []
    seen: set[str] = set()
    for dag_row in dag_rows:
        point_id = dag_row.get("point_id")
        if not point_id or point_id in seen:
            fail(f"duplicate or invalid envelope point id: {point_id!r}")
        seen.add(point_id)
        point_dir = args.build_root / point_id
        point_json = load_json(point_dir / "point.json")
        outcome_json = load_json(point_dir / "outcome.json")
        if point_json.get("point_id") != point_id or outcome_json.get("point_id") != point_id:
            fail(f"point identity mismatch: {point_id}")
        outcome = dag_row.get("outcome")
        if outcome != outcome_json.get("outcome"):
            fail(f"point outcome mismatch: {point_id}")
        base = {
            "point_id": point_id,
            "parents": []
            if dag_row.get("parents") == "-"
            else dag_row.get("parents", "").split(","),
            "geometry": dag_row.get("geometry"),
            "kind": dag_row.get("kind"),
            "symbol": point_json.get("symbol"),
            "outcome": outcome,
            "min_blocks": int(dag_row.get("min_blocks", "0")),
            "maxreg": int(dag_row.get("maxreg", "0")),
            "target_active_blocks": int(dag_row.get("target_active_blocks", "0")),
            "correctness_spec_sha256": sha256_json(correctness_spec),
            "sanitizer_spec_sha256": sha256_json(sanitizer_spec),
            "correctness_input_bindings_sha256": sha256_json(correctness_spec),
            "sanitizer_input_bindings_sha256": sha256_json(sanitizer_spec),
            "bundle_sha256": bundle_hash,
        }
        if outcome == "success":
            runner = point_dir / "timing" / "run_windowed_r0_corpus"
            recorded_hash = validate_hash(
                f"{point_id} executable", dag_row.get("timing_binary_sha256")
            )
            if sha256_file(runner) != recorded_hash:
                fail(f"point executable hash mismatch: {point_id}")
            resources = outcome_json.get("resources")
            if not isinstance(resources, dict) or resources.get("binary_sha256") != recorded_hash:
                fail(f"point resources mismatch: {point_id}")
            base.update(
                {
                    "runner": str(runner.resolve()),
                    "executable_sha256": recorded_hash,
                    "source_tree_sha256": validate_hash(
                        f"{point_id} source tree", dag_row.get("source_tree_sha256")
                    ),
                    "registers": int(dag_row.get("registers", "0")),
                    "stack_bytes": int(dag_row.get("stack_bytes", "0")),
                    "local_bytes": int(dag_row.get("local_bytes", "0")),
                    "shared_bytes": int(dag_row.get("shared_bytes", "0")),
                    "ldl": int(dag_row.get("ldl", "0")),
                    "stl": int(dag_row.get("stl", "0")),
                    "inferred_active_blocks": int(
                        dag_row.get("inferred_active_blocks", "0")
                    ),
                    "inferred_occupancy": float(
                        dag_row.get("inferred_occupancy", "0")
                    ),
                    "opcodes": resources.get("opcodes"),
                }
            )
            point_evidence_key(base)
        points.append(base)

    natural_by_geometry = {
        point["geometry"]: point["point_id"]
        for point in points
        if point["outcome"] == "success" and point["kind"] == "natural"
    }
    if set(natural_by_geometry) != set(GEOMETRIES):
        fail("envelope catalog requires one natural point per geometry")
    result = {
        "version": 1,
        "point_dag": str(args.point_dag),
        "point_dag_sha256": sha256_file(args.point_dag),
        "manifest": str(args.manifest),
        "manifest_sha256": sha256_file(args.manifest),
        "bundle": str(args.bundle),
        "bundle_sha256": bundle_hash,
        "correctness_spec": correctness_spec,
        "sanitizer_spec": sanitizer_spec,
        "natural_by_geometry": natural_by_geometry,
        "points": points,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print("WINDOWED_R0_ENVELOPE_CATALOG_OK")


def correctness_semantic_digest(rows: list[dict[str, Any]]) -> str:
    fields = (
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
    values = []
    for row in sorted(
        rows,
        key=lambda value: (
            value.get("circuit"),
            value.get("layer"),
            value.get("log_trace"),
            value.get("seed"),
        ),
    ):
        bindings = {}
        for field in fields:
            value = row.get(field)
            if field == "derived_source_sha256" and value is None:
                bindings[field] = None
            else:
                bindings[field] = validate_hash(f"correctness {field}", value)
        values.append(
            {
                "circuit": row.get("circuit"),
                "layer": row.get("layer"),
                "log_trace": row.get("log_trace"),
                "seed": row.get("seed"),
                "bindings": bindings,
            }
        )
    return sha256_json(values)


def audit_envelope_correctness(
    args: argparse.Namespace,
    catalog: dict[str, Any],
    manifest_by_name: dict[str, dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    campaign = load_json(args.correctness_root / "evidence.json")
    point_rows = campaign.get("points") if isinstance(campaign, dict) else None
    if not isinstance(point_rows, dict):
        fail("envelope correctness evidence lacks point map")
    points = catalog["points"]
    point_by_id = {point["point_id"]: point for point in points}
    if set(point_rows) != {
        point["point_id"] for point in points if point.get("outcome") == "success"
    }:
        fail("envelope correctness point coverage mismatch")
    results: dict[str, dict[str, Any]] = {}
    for point in points:
        point_id = point["point_id"]
        if point.get("outcome") != "success":
            results[point_id] = {
                "correctness_state": None,
                "sanitizer_state": None,
            }
            continue
        evidence = point_rows[point_id]
        if not isinstance(evidence, dict):
            fail(f"invalid correctness evidence row: {point_id}")
        reused_from = evidence.get("reused_from")
        if reused_from is not None:
            representative = point_by_id.get(reused_from)
            if representative is None or point_evidence_key(point) != point_evidence_key(
                representative
            ):
                fail(f"deduplication binding mismatch for {point_id}")
            representative_result = results.get(reused_from)
            if representative_result is None:
                fail(f"deduplication representative order mismatch for {point_id}")
            results[point_id] = {**representative_result, "reused_from": reused_from}
            continue

        point_root = args.correctness_root / point_id
        correctness = evidence.get("correctness")
        sanitizer = evidence.get("sanitizer")
        if not isinstance(correctness, dict) or not isinstance(sanitizer, dict):
            fail(f"incomplete correctness evidence summary: {point_id}")
        correctness_state = correctness.get("state")
        sanitizer_state = sanitizer.get("state")

        focused_dirs = sorted((point_root / "focused").glob("*"))
        if len(focused_dirs) != 57:
            fail(f"focused correctness coordinate coverage mismatch: {point_id}")
        focused_rows: list[dict[str, Any]] = []
        observed_coordinates = set()
        for directory in focused_dirs:
            command_path = directory / "command.txt"
            checkpoint_path = directory / "checkpoint.json"
            rows_path = directory / "rows.jsonl"
            checkpoint = load_json(checkpoint_path)
            command = command_path.read_text()
            if (
                ".agents/bin/with_gpu_lock.sh" not in command
                or point["runner"] not in command
                or f"--geometries {point['geometry']}" not in command
            ):
                fail(f"focused correctness command mismatch: {command_path}")
            if checkpoint.get("stdout_sha256") != sha256_file(rows_path):
                fail(f"focused correctness rows hash mismatch: {rows_path}")
            coordinate = checkpoint.get("coordinate")
            if coordinate not in manifest_by_name or coordinate in observed_coordinates:
                fail(f"focused correctness coordinate mismatch: {checkpoint_path}")
            observed_coordinates.add(coordinate)
            rows = load_jsonl(rows_path)
            if checkpoint.get("state") == "complete":
                expected = {
                    (log_trace, seed)
                    for log_trace in (3, 8)
                    for seed in (0, 1, 0xDEAD_BEEF_CAFE_BABE)
                }
                if {
                    (row.get("log_trace"), row.get("seed")) for row in rows
                } != expected or len(rows) != 6:
                    fail(f"focused correctness row coverage mismatch: {rows_path}")
            focused_rows.extend(rows)
        if observed_coordinates != set(manifest_by_name):
            fail(f"focused correctness manifest coverage mismatch: {point_id}")
        for row in focused_rows:
            if (
                row.get("geometry") != point["geometry"]
                or row.get("executable_sha256") != point["executable_sha256"]
                or row.get("bundle_sha256") != point["bundle_sha256"]
            ):
                fail(f"focused correctness immutable binding mismatch: {point_id}")
            launch = row.get("launch")
            if not isinstance(launch, dict) or launch.get("symbol") != point["symbol"]:
                fail(f"focused correctness symbol mismatch: {point_id}")
            for field in (
                "canonical_p_sha256",
                "canonical_q_sha256",
                "compiled_q_sha256",
                "p_minus_q_sha256",
            ):
                validate_hash(f"focused {field}", row.get(field))
        if correctness_state == "complete":
            if len(focused_rows) != 342 or any(
                row.get("passing") is not True for row in focused_rows
            ):
                fail(f"complete focused correctness is not literal 342-row success: {point_id}")
            if correctness.get("input_bindings_sha256") != correctness_semantic_digest(
                focused_rows
            ):
                fail(f"focused input binding digest mismatch: {point_id}")
        elif correctness_state not in ("launch_failed", "correctness_failed"):
            fail(f"invalid focused correctness disposition: {point_id}")

        sanitizer_root = point_root / "sanitizer"
        sanitizer_checkpoint = load_json(sanitizer_root / "checkpoint.json")
        sanitizer_rows_path = sanitizer_root / "rows.jsonl"
        sanitizer_rows = load_jsonl(sanitizer_rows_path)
        sanitizer_command = (sanitizer_root / "command.txt").read_text()
        if (
            ".agents/bin/with_gpu_lock.sh compute-sanitizer" not in sanitizer_command
            or point["runner"] not in sanitizer_command
            or f"--geometries {point['geometry']}" not in sanitizer_command
        ):
            fail(f"sanitizer command mismatch: {point_id}")
        if sanitizer_checkpoint.get("stdout_sha256") != sha256_file(
            sanitizer_rows_path
        ):
            fail(f"sanitizer rows hash mismatch: {point_id}")
        for row in sanitizer_rows:
            if (
                row.get("geometry") != point["geometry"]
                or row.get("executable_sha256") != point["executable_sha256"]
                or row.get("bundle_sha256") != point["bundle_sha256"]
            ):
                fail(f"sanitizer immutable binding mismatch: {point_id}")
        if sanitizer_state == "complete":
            if (
                len(sanitizer_rows) != 57
                or len(
                    {
                        (row.get("circuit"), row.get("layer"))
                        for row in sanitizer_rows
                    }
                )
                != 57
                or any(
                    row.get("log_trace") != 8
                    or row.get("seed") != 0
                    or row.get("passing") is not True
                    for row in sanitizer_rows
                )
            ):
                fail(f"sanitizer lacks literal 57-coordinate success: {point_id}")
            if "ERROR SUMMARY: 0 errors" not in (
                sanitizer_root / "memcheck.log"
            ).read_text():
                fail(f"sanitizer evidence lacks zero-error summary: {point_id}")
            if sanitizer.get("input_bindings_sha256") != correctness_semantic_digest(
                sanitizer_rows
            ):
                fail(f"sanitizer input binding digest mismatch: {point_id}")
        elif sanitizer_state != "sanitizer_failed":
            fail(f"invalid sanitizer disposition: {point_id}")
        results[point_id] = {
            "correctness_state": correctness_state,
            "sanitizer_state": sanitizer_state,
            "correctness_input_bindings_sha256": correctness.get(
                "input_bindings_sha256"
            ),
            "sanitizer_input_bindings_sha256": sanitizer.get(
                "input_bindings_sha256"
            ),
        }
    return results


def paired_evidence_hash(directory: pathlib.Path) -> str:
    digest = hashlib.sha256()
    paths = sorted(
        path
        for arm in ("child", "natural")
        for path in (directory / arm).rglob("*")
        if path.is_file()
    )
    if not paths:
        fail(f"paired session contains no arm evidence: {directory}")
    for path in paths:
        relative = str(path.relative_to(directory)).encode()
        contents = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "little"))
        digest.update(relative)
        digest.update(len(contents).to_bytes(8, "little"))
        digest.update(contents)
    return digest.hexdigest()


def audit_timing_arm(
    directory: pathlib.Path,
    *,
    point_id: str,
    executable_sha256: str,
    coordinate: str,
    traversal: str,
    target_geometry: str,
    expected_checksum: str,
) -> list[float]:
    binding = load_json(directory / "session-bindings.json")
    if (
        binding.get("point") != point_id
        or binding.get("coordinate") != coordinate
        or binding.get("traversal") != traversal
        or binding.get("warmups") != 5
        or binding.get("samples") != 50
        or binding.get("executable_sha256") != executable_sha256
        or binding.get("expected_checksum") != expected_checksum
    ):
        fail(f"timing arm binding mismatch: {directory}")
    if set(binding.get("geometries", [])) != set(GEOMETRIES):
        fail(f"timing arm ancillary geometry coverage mismatch: {directory}")
    stdout_rows = load_jsonl(directory / "stdout.jsonl")
    if len(stdout_rows) != len(GEOMETRIES):
        fail(f"timing arm stdout coverage mismatch: {directory}")
    target_samples = None
    for geometry in GEOMETRIES:
        rows_path = directory / f"{geometry}.samples.jsonl"
        checkpoint_path = directory / f"{geometry}.checkpoint.json"
        rows = load_jsonl(rows_path)
        checkpoint = load_json(checkpoint_path)
        if checkpoint.get("state") != "complete" or checkpoint.get(
            "rows_sha256"
        ) != sha256_file(rows_path):
            fail(f"timing geometry checkpoint mismatch: {rows_path}")
        if len(rows) != 55:
            fail(f"timing sample count mismatch: {rows_path}")
        if [row.get("sample_index") for row in rows] != list(range(55)):
            fail(f"timing sample indices mismatch: {rows_path}")
        if [row.get("warmup") for row in rows] != [True] * 5 + [False] * 50:
            fail(f"timing warmup ordering mismatch: {rows_path}")
        for row in rows:
            key = row.get("key")
            if (
                not isinstance(key, dict)
                or key.get("point") != point_id
                or f"{key.get('circuit')}:{key.get('layer')}" != coordinate
                or key.get("geometry") != geometry
                or key.get("traversal") != traversal
                or key.get("seed") != R0_PRODUCTION_SEED
            ):
                fail(f"timing sample key mismatch: {rows_path}")
            duration = row.get("milliseconds")
            if (
                isinstance(duration, bool)
                or not isinstance(duration, (int, float))
                or not math.isfinite(float(duration))
                or duration < 0
            ):
                fail(f"timing duration mismatch: {rows_path}")
        if geometry == target_geometry:
            target_samples = [
                float(row["milliseconds"]) for row in rows if not row["warmup"]
            ]
    output_by_geometry = {
        row.get("key", {}).get("geometry"): row for row in stdout_rows
    }
    target_output = output_by_geometry.get(target_geometry)
    if (
        target_output is None
        or target_output.get("correctness_checksum") != expected_checksum
        or target_output.get("post_session_checksum") != expected_checksum
        or target_output.get("warmups") != 5
        or target_output.get("samples") != 50
    ):
        fail(f"timing production checksum mismatch: {directory}")
    if target_samples is None or len(target_samples) != 50:
        fail(f"target timing samples missing: {directory}")
    return target_samples


def envelope_audit(args: argparse.Namespace) -> None:
    catalog = load_json(args.catalog)
    manifest = load_json(args.manifest)
    points = catalog.get("points") if isinstance(catalog, dict) else None
    coordinates = manifest.get("coordinates") if isinstance(manifest, dict) else None
    if not isinstance(points, list) or not isinstance(coordinates, list) or len(coordinates) != 57:
        fail("invalid envelope catalog or manifest")
    manifest_by_name = {coordinate_name(row): row for row in coordinates}
    if len(manifest_by_name) != 57:
        fail("envelope manifest contains duplicate coordinates")
    correctness = audit_envelope_correctness(args, catalog, manifest_by_name)
    point_by_id = {point["point_id"]: point for point in points}
    natural_by_geometry = catalog.get("natural_by_geometry", {})
    candidates = [
        point
        for point in points
        if point.get("outcome") == "success"
        and point.get("kind") != "natural"
        and correctness[point["point_id"]]["correctness_state"] == "complete"
        and correctness[point["point_id"]]["sanitizer_state"] == "complete"
    ]
    expected_session_paths = {
        args.timing_root
        / point["point_id"]
        / coordinate_stem(row)
        / traversal
        / "pair.checkpoint.json"
        for point in candidates
        for row in coordinates
        for traversal in TRAVERSALS
    }
    observed_session_paths = set(args.timing_root.glob("*/*/*/pair.checkpoint.json"))
    if observed_session_paths != expected_session_paths:
        fail(
            "envelope timing session coverage mismatch "
            f"missing={len(expected_session_paths - observed_session_paths)} "
            f"extra={len(observed_session_paths - expected_session_paths)}"
        )

    samples: dict[tuple[str, str, str, str], list[float]] = {}
    natural_sources: dict[str, str] = {}
    timing_states: dict[str, str] = {}
    for point in candidates:
        point_id = point["point_id"]
        natural_id = natural_by_geometry.get(point["geometry"])
        natural = point_by_id.get(natural_id)
        if natural is None:
            fail(f"natural point missing for {point_id}")
        point_state = "complete"
        for row in coordinates:
            coordinate = coordinate_name(row)
            production = load_json(
                args.production_root / coordinate_stem(row) / "input-bindings.json"
            )
            for traversal in TRAVERSALS:
                directory = (
                    args.timing_root
                    / point_id
                    / coordinate_stem(row)
                    / traversal
                )
                binding = load_json(directory / "pair-bindings.json")
                checkpoint = load_json(directory / "pair.checkpoint.json")
                if (
                    binding.get("point_id") != point_id
                    or binding.get("natural_point_id") != natural_id
                    or binding.get("coordinate") != coordinate
                    or binding.get("traversal") != traversal
                    or binding.get("target_geometry") != point["geometry"]
                    or binding.get("child", {}).get("executable_sha256")
                    != point["executable_sha256"]
                    or binding.get("natural", {}).get("executable_sha256")
                    != natural["executable_sha256"]
                    or binding.get("input_sha256")
                    != production.get("bindings", {}).get("input_sha256")
                    or binding.get("expected_checksum") != production.get("checksum")
                ):
                    fail(f"paired timing immutable binding mismatch: {directory}")
                if checkpoint.get("bindings_sha256") != sha256_file(
                    directory / "pair-bindings.json"
                ):
                    fail(f"paired timing checkpoint binding mismatch: {directory}")
                command = (directory / "command.txt").read_text()
                if (
                    ".agents/bin/with_gpu_lock.sh" not in command
                    or " paired-session " not in command
                ):
                    fail(f"paired timing lock command mismatch: {directory}")
                if checkpoint.get("state") != "complete":
                    if checkpoint.get("state") not in (
                        "launch_failed",
                        "correctness_failed",
                    ):
                        fail(f"invalid paired timing disposition: {directory}")
                    point_state = checkpoint["state"]
                    continue
                if checkpoint.get("evidence_sha256") != paired_evidence_hash(directory):
                    fail(f"paired timing evidence hash mismatch: {directory}")
                child_values = audit_timing_arm(
                    directory / "child",
                    point_id=point_id,
                    executable_sha256=point["executable_sha256"],
                    coordinate=coordinate,
                    traversal=traversal,
                    target_geometry=point["geometry"],
                    expected_checksum=production["checksum"],
                )
                natural_values = audit_timing_arm(
                    directory / "natural",
                    point_id=natural_id,
                    executable_sha256=natural["executable_sha256"],
                    coordinate=coordinate,
                    traversal=traversal,
                    target_geometry=point["geometry"],
                    expected_checksum=production["checksum"],
                )
                samples[(point_id, coordinate, traversal, "child")] = child_values
                samples[(point_id, coordinate, traversal, "natural")] = natural_values
                previous_source = natural_sources.get(natural_id)
                if previous_source is None or point_id < previous_source:
                    natural_sources[natural_id] = point_id
        timing_states[point_id] = point_state

    for geometry, natural_id in natural_by_geometry.items():
        source = natural_sources.get(natural_id)
        timing_states[natural_id] = "complete" if source is not None else "launch_failed"

    dispositions = []
    summaries = []
    for point in points:
        point_id = point["point_id"]
        state = correctness[point_id]
        disposition = envelope_disposition(
            point.get("outcome", ""),
            state.get("correctness_state"),
            state.get("sanitizer_state"),
            timing_states.get(point_id),
        )
        dispositions.append(
            {
                "point_id": point_id,
                "geometry": point.get("geometry"),
                "disposition": disposition,
                "correctness_reused_from": state.get("reused_from"),
            }
        )
        if disposition != "fully-timed":
            continue
        natural_id = natural_by_geometry[point["geometry"]]
        natural = point_by_id[natural_id]
        source_id = point_id if point.get("kind") != "natural" else natural_sources[natural_id]
        arm = "child" if point.get("kind") != "natural" else "natural"
        for row in coordinates:
            coordinate = coordinate_name(row)
            candidate_values = []
            natural_values = []
            for traversal in TRAVERSALS:
                candidate_values.extend(
                    samples[(source_id, coordinate, traversal, arm)]
                )
                natural_values.extend(
                    samples[(source_id, coordinate, traversal, "natural")]
                )
            if len(candidate_values) != 100 or len(natural_values) != 100:
                fail(f"aggregate envelope sample count mismatch: {point_id} {coordinate}")
            candidate_median = statistics.median(candidate_values)
            natural_median = statistics.median(natural_values)
            comparison_row = envelope_resource_comparison(
                point,
                natural,
                candidate_median_ms=candidate_median,
                natural_median_ms=natural_median,
            )
            summaries.append(
                {
                    "point_id": point_id,
                    "natural_point_id": natural_id,
                    "baseline_evidence_point": source_id,
                    "circuit": row["circuit"],
                    "layer": row["layer"],
                    "geometry": point["geometry"],
                    **comparison_row,
                }
            )

    if len(dispositions) != len(points) or len({row["point_id"] for row in dispositions}) != len(points):
        fail("envelope points do not have exactly one disposition")
    fully_timed_count = sum(
        row["disposition"] == "fully-timed" for row in dispositions
    )
    if len(summaries) != fully_timed_count * 57:
        fail("fully timed point report coverage mismatch")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "envelope-dispositions.json").write_text(
        json.dumps(dispositions, separators=(",", ":")) + "\n"
    )
    (args.output_dir / "envelope-summary.json").write_text(
        json.dumps(summaries, separators=(",", ":")) + "\n"
    )
    tsv_rows = []
    for row in summaries:
        tsv_rows.append(
            {
                **row,
                "opcode_changes": json.dumps(
                    row["opcode_changes"], sort_keys=True, separators=(",", ":")
                ),
            }
        )
    if tsv_rows:
        with (args.output_dir / "envelope-summary.tsv").open("w", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=list(tsv_rows[0]), delimiter="\t")
            writer.writeheader()
            writer.writerows(tsv_rows)
    audit_summary = {
        "version": 1,
        "point_count": len(points),
        "disposition_counts": dict(
            sorted(
                {
                    disposition: sum(
                        row["disposition"] == disposition for row in dispositions
                    )
                    for disposition in {
                        "compile-failed",
                        "launch-failed",
                        "correctness-failed",
                        "sanitizer-failed",
                        "fully-timed",
                    }
                }.items()
            )
        ),
        "comparison_rows": len(summaries),
        "selection_statement": None,
        "spill_points_discarded": 0,
    }
    (args.output_dir / "envelope-audit-summary.json").write_text(
        json.dumps(audit_summary, separators=(",", ":")) + "\n"
    )
    print(json.dumps(audit_summary, indent=2))
    print("WINDOWED_R0_ENVELOPE_AUDIT_OK")


def layer_weight(profile: Any, profile_name: str, circuit: str) -> int | None:
    if profile is None:
        return None
    if not isinstance(profile, list):
        fail(f"{profile_name} must be null or a layer list")
    total = 0
    for index, layer in enumerate(profile):
        if not isinstance(layer, dict):
            fail(f"{profile_name} layer {index} is not an object")
        invocations = layer.get("invocations")
        if not isinstance(invocations, int) or isinstance(invocations, bool) or invocations < 0:
            fail(f"{profile_name} layer {index} has invalid invocations")
        if layer.get("circuit") == circuit:
            total += invocations
    return total


def weights_for_circuit(weights: dict[str, Any], circuit: str) -> tuple[Any, Any, Any]:
    profiles = weights.get("profiles", {})
    current = profiles.get("current_base", {})
    if not isinstance(current, dict):
        fail("current_base must be an object")
    current_value = current.get(CURRENT_BASE_WEIGHT_KEYS.get(circuit, circuit))
    if current_value is not None and (
        type(current_value) is not int or current_value < 0
    ):
        fail(f"current_base has invalid weight for {circuit}")
    development = profiles.get("development_recursion_proxy")
    development_value = None
    if isinstance(development, dict):
        status = development.get("status")
        if status == "available":
            development_value = layer_weight(
                development.get("layers"),
                "development_recursion_proxy",
                circuit,
            )
        elif status != "unavailable":
            fail("development_recursion_proxy has invalid status")
    elif development is not None:
        fail("development_recursion_proxy must be an object")
    future_value = layer_weight(
        profiles.get("future_current_recursion"),
        "future_current_recursion",
        circuit,
    )
    return current_value, development_value, future_value


def audit_production(
    args: argparse.Namespace,
    manifest: dict[str, Any],
    session_bindings: dict[str, dict[str, Any]],
) -> None:
    if args.production_root is None:
        return
    coordinates = manifest.get("coordinates", [])
    expected_stems = {coordinate_stem(row) for row in coordinates}
    observed_stems = {
        path.parent.name for path in args.production_root.glob("*/input-bindings.json")
    }
    if observed_stems != expected_stems:
        fail(
            "production summary coverage mismatch "
            f"missing={sorted(expected_stems - observed_stems)[:3]} "
            f"extra={sorted(observed_stems - expected_stems)[:3]}"
        )

    for row in coordinates:
        coordinate = coordinate_name(row)
        directory = args.production_root / coordinate_stem(row)
        summary_path = directory / "input-bindings.json"
        summary = load_json(summary_path)
        timing_binding = session_bindings.get(coordinate)
        if timing_binding is None:
            fail(f"production coordinate has no timing binding: {coordinate}")
        bindings = timing_binding.get("production_bindings")
        if args.strict:
            for field in (
                "executable_sha256",
                "bundle_sha256",
                "input_sha256",
                "source_tree_sha256",
                "build_flags_sha256",
            ):
                if not isinstance(bindings, dict) or bindings.get(field) != timing_binding.get(field):
                    fail(f"production runtime binding mismatch field={field}: {summary_path}")
        expected_summary = {
            "version": 1,
            "coordinate": coordinate,
            "bindings": bindings,
            "checksum": timing_binding.get("expected_checksum"),
            "geometries": GEOMETRIES,
            "production_rows": row["trace_len"] // 8,
            "shape": row["shape"],
            "launches": expected_launches(row),
        }
        for field, expected_value in expected_summary.items():
            if not exact_json_equal(summary.get(field), expected_value):
                fail(f"production summary mismatch field={field}: {summary_path}")

        expected_prefixes = {
            f"natural--{coordinate_stem(row)}--{geometry}" for geometry in GEOMETRIES
        }
        observation_paths = sorted(directory.glob("*.observations.jsonl"))
        checkpoint_paths = sorted(directory.glob("*.checkpoint.json"))
        if {path.name.removesuffix(".observations.jsonl") for path in observation_paths} != expected_prefixes:
            fail(f"production observation coverage mismatch: {directory}")
        if {path.name.removesuffix(".checkpoint.json") for path in checkpoint_paths} != expected_prefixes:
            fail(f"production checkpoint coverage mismatch: {directory}")

        expected_launch_by_geometry = {
            launch["geometry"]: launch for launch in expected_summary["launches"]
        }
        observed_cells = None
        observed_preflight = None
        for geometry in GEOMETRIES:
            prefix = f"natural--{coordinate_stem(row)}--{geometry}"
            observation_path = directory / f"{prefix}.observations.jsonl"
            checkpoint_path = directory / f"{prefix}.checkpoint.json"
            rows = load_jsonl(observation_path)
            if len(rows) != 1:
                fail(f"production observation cardinality mismatch: {observation_path}")
            observation = rows[0]
            expected_key = expected_result_key(row, geometry, None)
            expected_observation = {
                "version": 1,
                "key": expected_key,
                "bindings": bindings,
                "production_rows": expected_summary["production_rows"],
                "shape": row["shape"],
                "launch": expected_launch_by_geometry[geometry],
                "checksum": expected_summary["checksum"],
                "failure": None,
            }
            for field, expected_value in expected_observation.items():
                if not exact_json_equal(observation.get(field), expected_value):
                    fail(
                        f"production observation mismatch field={field}: "
                        f"{observation_path}"
                    )
            cells = observation.get("cells")
            preflight = observation.get("preflight")
            if not isinstance(cells, list) or len(cells) != 27:
                fail(f"production observation has invalid cells: {observation_path}")
            if cells_sha256(cells) != expected_summary["checksum"]:
                fail(f"production cell checksum mismatch: {observation_path}")
            if not isinstance(preflight, dict):
                fail(f"production observation has invalid preflight: {observation_path}")
            if observed_cells is None:
                observed_cells = cells
                observed_preflight = preflight
            elif cells != observed_cells or preflight != observed_preflight:
                fail(f"production cross-geometry result drift: {observation_path}")

            checkpoint = load_json(checkpoint_path)
            expected_checkpoint = {
                "version": 1,
                "key": expected_key,
                "bindings": bindings,
                "state": "complete",
                "rows_sha256": sha256_file(observation_path),
            }
            for field, expected_value in expected_checkpoint.items():
                if not exact_json_equal(checkpoint.get(field), expected_value):
                    fail(
                        f"production checkpoint mismatch field={field}: "
                        f"{checkpoint_path}"
                    )
    print("WINDOWED_R0_PRODUCTION_AUDIT_OK")


def audit_nsys(
    args: argparse.Namespace,
    manifest: dict[str, Any],
    session_bindings: dict[str, dict[str, Any]],
) -> None:
    if args.nsys_root is None:
        return
    if args.production_root is None:
        fail("--nsys-root requires --production-root")
    metadata_paths = sorted(args.nsys_root.glob("*/launch-metadata.json"))
    if len(metadata_paths) != len(GEOMETRIES):
        fail(
            f"nsys audit found {len(metadata_paths)} launch metadata files, "
            f"expected {len(GEOMETRIES)}"
        )
    coordinates = manifest.get("coordinates", [])
    ordered = sorted(
        coordinates,
        key=lambda row: (
            row["shape"]["records"],
            f"{row['circuit']}:{row['layer']}",
        ),
    )
    representative_row = ordered[len(ordered) // 2]
    representative = f"{representative_row['circuit']}:{representative_row['layer']}"
    representative_stem = (
        f"{representative_row['circuit']}-l{representative_row['layer']}"
    )
    production = load_json(
        args.production_root / representative_stem / "input-bindings.json"
    )
    launches = production.get("launches")
    if not isinstance(launches, list):
        fail("representative production summary has no launch metadata")
    launches_by_geometry = {launch.get("geometry"): launch for launch in launches}
    if set(launches_by_geometry) != set(GEOMETRIES):
        fail("representative production launch geometry mismatch")
    bindings = session_bindings.get(representative)
    if bindings is None:
        fail("representative coordinate has no timing session bindings")

    seen: set[str] = set()
    for metadata_path in metadata_paths:
        metadata = load_json(metadata_path)
        geometry = metadata.get("geometry")
        if geometry not in GEOMETRIES or geometry in seen:
            fail(f"invalid or duplicate nsys geometry: {metadata_path}")
        seen.add(geometry)
        if metadata_path.parent.name != geometry:
            fail(f"nsys directory/geometry mismatch: {metadata_path}")
        if type(metadata.get("version")) is not int or metadata.get("version") != 1:
            fail(f"unsupported nsys metadata version: {metadata_path}")
        if metadata.get("coordinate") != representative:
            fail(f"nsys representative coordinate mismatch: {metadata_path}")
        expected_launch = launches_by_geometry[geometry]
        expected_fields = {
            "kernel_symbol": expected_launch.get("symbol"),
            "grid": expected_launch.get("grid"),
            "block": expected_launch.get("block"),
            "checksum": production.get("checksum"),
            "executable_sha256": bindings.get("executable_sha256"),
            "bundle_sha256": bindings.get("bundle_sha256"),
            "input_sha256": bindings.get("input_sha256"),
        }
        for field, expected_value in expected_fields.items():
            if not exact_json_equal(metadata.get(field), expected_value):
                fail(f"nsys {field} mismatch: {metadata_path}")
        if type(metadata.get("observed_launch_count")) is not int:
            fail(f"nsys target launch cardinality type mismatch: {metadata_path}")
        if metadata.get("observed_launch_count") != 1:
            fail(f"nsys target launch cardinality mismatch: {metadata_path}")

        report_path = metadata_path.parent / "profile.nsys-rep"
        database_path = metadata_path.parent / "profile.sqlite"
        report_hash = validate_hash("nsys report_sha256", metadata.get("report_sha256"))
        database_hash = validate_hash("nsys sqlite_sha256", metadata.get("sqlite_sha256"))
        if sha256_file(report_path) != report_hash:
            fail(f"nsys report hash mismatch: {report_path}")
        if sha256_file(database_path) != database_hash:
            fail(f"nsys sqlite hash mismatch: {database_path}")
        try:
            connection = sqlite3.connect(f"file:{database_path}?mode=ro", uri=True)
            observed = connection.execute(
                """
                SELECT kernel.gridX, kernel.gridY, kernel.gridZ,
                       kernel.blockX, kernel.blockY, kernel.blockZ
                  FROM CUPTI_ACTIVITY_KIND_KERNEL AS kernel
                  JOIN StringIds AS strings ON strings.id = kernel.shortName
                 WHERE strings.value = ?
                """,
                (metadata["kernel_symbol"],),
            ).fetchall()
            connection.close()
        except sqlite3.Error as error:
            fail(f"query nsys database {database_path}: {error}")
        if len(observed) != 1:
            fail(f"nsys observed {len(observed)} target launches: {database_path}")
        row = observed[0]
        if list(row[:3]) != metadata["grid"] or list(row[3:]) != metadata["block"]:
            fail(f"nsys observed launch dimensions mismatch: {database_path}")

    if seen != set(GEOMETRIES):
        fail("nsys geometry coverage mismatch")
    print("WINDOWED_R0_NSYS_AUDIT_OK")


def natural_audit(args: argparse.Namespace) -> None:
    if args.strict and any(
        value is None
        for value in (
            args.runner,
            args.bundle,
            args.source_root,
            args.build_flags,
            args.production_root,
            args.nsys_root,
        )
    ):
        fail(
            "--strict requires runner, bundle, source-root, build-flags, "
            "production-root, and nsys-root"
        )
    manifest = load_json(args.manifest)
    weights = load_json(args.weights)
    coordinates = manifest.get("coordinates", [])
    if len(coordinates) != 57:
        fail("natural audit requires exactly 57 manifest coordinates")
    manifest_by_name = {coordinate_name(row): row for row in coordinates}
    expected = {(f"{row['circuit']}:{row['layer']}", geometry) for row in coordinates for geometry in GEOMETRIES}
    coordinate_indices = {
        f"{row['circuit']}:{row['layer']}": index for index, row in enumerate(coordinates)
    }
    reverse_coordinates = list(reversed([f"{row['circuit']}:{row['layer']}" for row in coordinates]))
    reverse_indices = {coordinate: index for index, coordinate in enumerate(reverse_coordinates)}
    expected_checksums: dict[tuple[str, str], str] = {}
    session_bindings_by_coordinate: dict[str, dict[str, Any]] = {}
    session_bindings_by_identity: dict[tuple[str, str], dict[str, Any]] = {}
    binding_paths = sorted(args.timing_root.glob("*/*/session-bindings.json"))
    if len(binding_paths) != 114:
        fail(f"natural audit found {len(binding_paths)} session bindings, expected 114")
    for binding_path in binding_paths:
        binding = load_json(binding_path)
        coordinate = binding.get("coordinate")
        traversal = binding.get("traversal")
        if (
            type(binding.get("version")) is not int
            or binding.get("version") != 1
            or binding.get("point") != "natural"
            or coordinate not in coordinate_indices
            or traversal not in TRAVERSALS
        ):
            fail(f"session binding identity mismatch: {binding_path}")
        expected_binding_path = (
            args.timing_root
            / coordinate_stem(manifest_by_name[coordinate])
            / traversal
            / "session-bindings.json"
        )
        if binding_path != expected_binding_path:
            fail(f"session binding path mismatch: {binding_path}")
        index = (
            coordinate_indices[coordinate]
            if traversal == "forward"
            else reverse_indices[coordinate]
        )
        rotation = index % len(GEOMETRIES) if traversal == "forward" else (-index - 1) % len(GEOMETRIES)
        expected_order = GEOMETRIES[rotation:] + GEOMETRIES[:rotation]
        if not exact_json_equal(binding.get("geometries"), expected_order):
            fail(f"geometry rotation mismatch: {binding_path}")
        if binding.get("warmups") != 5 or binding.get("samples") != 50:
            fail(f"session cardinality binding mismatch: {binding_path}")
        for field in (
            "executable_sha256",
            "bundle_sha256",
            "input_sha256",
            "source_tree_sha256",
            "build_flags_sha256",
            "expected_checksum",
        ):
            validate_hash(f"session {field}", binding.get(field))
        production = binding.get("production_bindings")
        if not isinstance(production, dict) or production.get("input_sha256") != binding["input_sha256"]:
            fail(f"production input binding mismatch: {binding_path}")
        expected_checksums[(coordinate, traversal)] = binding["expected_checksum"]
        session_bindings_by_identity[(coordinate, traversal)] = binding
        previous = session_bindings_by_coordinate.get(coordinate)
        semantic = {
            key: value
            for key, value in binding.items()
            if key not in ("traversal", "geometries")
        }
        if previous is not None and previous != semantic:
            fail(f"forward/reverse session binding mismatch: {coordinate}")
        session_bindings_by_coordinate[coordinate] = semantic
        session_dir = binding_path.parent
        checkpoint = load_json(session_dir / "session.checkpoint.json")
        if type(checkpoint.get("version")) is not int or checkpoint.get("version") != 1:
            fail(f"session checkpoint version mismatch: {session_dir}")
        if checkpoint.get("state") != "complete":
            fail(f"session checkpoint is not Complete: {session_dir}")
        if checkpoint.get("coordinate") != coordinate or checkpoint.get("traversal") != traversal:
            fail(f"session checkpoint identity mismatch: {session_dir}")
        if checkpoint.get("bindings_sha256") != sha256_file(binding_path):
            fail(f"session binding hash mismatch: {session_dir}")
        if checkpoint.get("rows_sha256") != combined_rows_hash(session_dir):
            fail(f"session rows hash mismatch: {session_dir}")

        stdout_path = session_dir / "stdout.jsonl"
        stdout_rows = load_jsonl(stdout_path)
        if len(stdout_rows) != len(GEOMETRIES):
            fail(f"timing stdout cardinality mismatch: {stdout_path}")
        launch_by_geometry = {
            launch["geometry"]: launch
            for launch in expected_launches(manifest_by_name[coordinate])
        }
        for geometry, output in zip(binding["geometries"], stdout_rows, strict=True):
            expected_key = expected_result_key(
                manifest_by_name[coordinate], geometry, traversal
            )
            expected_output = {
                "key": expected_key,
                "correctness_checksum": binding["expected_checksum"],
                "post_session_checksum": binding["expected_checksum"],
                "warmups": 5,
                "samples": 50,
            }
            for field, expected_value in expected_output.items():
                if not exact_json_equal(output.get(field), expected_value):
                    fail(f"timing stdout mismatch field={field}: {stdout_path}")
            reused = output.get("reused")
            if not isinstance(reused, bool):
                fail(f"timing stdout reused flag mismatch: {stdout_path}")
            expected_launch = None if reused else launch_by_geometry[geometry]
            if not exact_json_equal(output.get("launch"), expected_launch):
                fail(f"timing stdout mismatch field=launch: {stdout_path}")

        if args.strict:
            expected_runtime = {
                "executable_sha256": sha256_file(args.runner),
                "bundle_sha256": sha256_file(args.bundle),
                "source_tree_sha256": source_tree_sha256(args.source_root),
                "build_flags_sha256": build_flags_sha256(args.build_flags),
            }
            for field, value in expected_runtime.items():
                if binding.get(field) != value:
                    fail(f"live {field} mismatch: {binding_path}")
            production_path = args.production_root / session_dir.parent.name / "input-bindings.json"
            production_summary = load_json(production_path)
            if production_summary.get("bindings") != production:
                fail(f"production summary binding mismatch: {binding_path}")
            if production_summary.get("checksum") != binding["expected_checksum"]:
                fail(f"production summary checksum mismatch: {binding_path}")
            task_bindings = dict(production)
            task_bindings.update(expected_runtime)
            for geometry in GEOMETRIES:
                geometry_checkpoint_path = session_dir / f"{geometry}.checkpoint.json"
                geometry_rows_path = session_dir / f"{geometry}.samples.jsonl"
                geometry_checkpoint = load_json(geometry_checkpoint_path)
                if (
                    type(geometry_checkpoint.get("version")) is not int
                    or geometry_checkpoint.get("version") != 1
                ):
                    fail(
                        "geometry checkpoint version mismatch: "
                        f"{geometry_checkpoint_path}"
                    )
                if geometry_checkpoint.get("state") != "complete":
                    fail(f"geometry checkpoint is not Complete: {geometry_checkpoint_path}")
                if not exact_json_equal(
                    geometry_checkpoint.get("key"),
                    expected_result_key(manifest_by_name[coordinate], geometry, traversal),
                ):
                    fail(f"geometry checkpoint key mismatch: {geometry_checkpoint_path}")
                if geometry_checkpoint.get("bindings") != task_bindings:
                    fail(f"geometry checkpoint binding mismatch: {geometry_checkpoint_path}")
                if geometry_checkpoint.get("rows_sha256") != sha256_file(geometry_rows_path):
                    fail(f"geometry rows hash mismatch: {geometry_rows_path}")

    print("WINDOWED_R0_TIMING_STDOUT_AUDIT_OK")
    audit_production(args, manifest, session_bindings_by_coordinate)
    audit_nsys(args, manifest, session_bindings_by_coordinate)

    by_key: dict[tuple[str, str], dict[str, list[dict[str, Any]]]] = defaultdict(
        lambda: defaultdict(list)
    )
    timing_paths = sorted(args.timing_root.glob("*/*/*.samples.jsonl"))
    if len(timing_paths) != 57 * len(TRAVERSALS) * len(GEOMETRIES):
        fail(f"natural audit found {len(timing_paths)} timing files, expected 570")
    for path in timing_paths:
        rows = load_jsonl(path)
        if not rows:
            fail(f"empty timing file {path}")
        coordinate = row_field(rows[0], "coordinate")
        if coordinate is None:
            circuit = row_field(rows[0], "circuit")
            layer = row_field(rows[0], "layer")
            coordinate = f"{circuit}:{layer}"
        geometry = row_field(rows[0], "geometry")
        traversal = row_field(rows[0], "traversal")
        if traversal not in TRAVERSALS:
            fail(f"bad traversal in {path}")
        if coordinate not in manifest_by_name:
            fail(f"unknown timing coordinate in {path}")
        expected_path = (
            args.timing_root
            / coordinate_stem(manifest_by_name[coordinate])
            / traversal
            / f"{geometry}.samples.jsonl"
        )
        if path != expected_path:
            fail(f"timing path/key mismatch: {path}")
        if (coordinate, traversal) not in session_bindings_by_identity:
            fail(f"timing file has no session binding: {path}")
        expected_key = expected_result_key(
            manifest_by_name[coordinate], geometry, traversal
        )
        if any(
            any(
                not exact_json_equal(row_field(row, field), value)
                for field, value in expected_key.items()
            )
            or (
                row_field(row, "coordinate") is not None
                and row_field(row, "coordinate") != coordinate
            )
            for row in rows
        ):
            fail(f"timing key mismatch in {path}")
        if len(rows) != 55:
            fail(f"{path} has {len(rows)} rows, expected 55")
        indices = [row.get("sample_index") for row in rows]
        if any(type(index) is not int for index in indices):
            fail(f"sample index type mismatch in {path}")
        if indices != list(range(55)):
            fail(f"noncontiguous sample indices in {path}")
        warmup_flags = [row.get("warmup") for row in rows]
        if any(type(flag) is not bool for flag in warmup_flags):
            fail(f"warmup flag type mismatch in {path}")
        if warmup_flags != [True] * 5 + [False] * 50:
            fail(f"warmup ordering mismatch in {path}")
        if sum(bool(row.get("warmup")) for row in rows) != 5:
            fail(f"{path} does not have five warmups")
        if sum(not bool(row.get("warmup")) for row in rows) != 50:
            fail(f"{path} does not have 50 measured samples")
        if any(
            isinstance(row.get("milliseconds"), bool)
            or not isinstance(row.get("milliseconds"), (int, float))
            for row in rows
        ):
            fail(f"timing duration type mismatch in {path}")
        if any(
            not math.isfinite(float(row["milliseconds"]))
            or row["milliseconds"] < 0
            for row in rows
        ):
            fail(f"invalid timing duration in {path}")
        expected_checksum = expected_checksums.get((coordinate, traversal))
        if expected_checksum is None:
            fail(f"missing session checksum binding for {path}")
        for row in rows:
            if row.get("checksum") is not None and row["checksum"] != expected_checksum:
                fail(f"sample checksum mismatch in {path}")
        by_key[(coordinate, geometry)][traversal].extend(rows)

    if set(by_key) != expected:
        missing = sorted(expected - set(by_key))
        extra = sorted(set(by_key) - expected)
        fail(f"timing key mismatch missing={missing[:3]} extra={extra[:3]}")

    summaries = []
    medians: dict[tuple[str, str], float] = {}
    for key in sorted(by_key):
        traversals = by_key[key]
        if set(traversals) != set(TRAVERSALS):
            fail(f"missing traversal for {key}")
        all_rows = traversals["forward"] + traversals["reverse"]
        if sum(bool(row["warmup"]) for row in all_rows) != 10:
            fail(f"aggregate warmup mismatch for {key}")
        samples = [float(row["milliseconds"]) for row in all_rows if not row["warmup"]]
        if len(samples) != 100:
            fail(f"aggregate measured sample mismatch for {key}")
        checksums = {row.get("checksum") for row in all_rows if row.get("checksum")}
        if len(checksums) > 1:
            fail(f"checksum drift for {key}")
        medians[key] = statistics.median(samples)

    coordinate_checksums: dict[str, set[str]] = defaultdict(set)
    for (coordinate, _traversal), checksum in expected_checksums.items():
        coordinate_checksums[coordinate].add(checksum)
    if any(len(values) != 1 for values in coordinate_checksums.values()):
        fail("cross-geometry checksum mismatch")

    for coordinate, geometry in sorted(medians):
        row = manifest_by_name[coordinate]
        reference = medians[(coordinate, "cta288_pair")]
        candidate = medians[(coordinate, geometry)]
        speedup, wording = comparison(reference, candidate)
        current, development, future = weights_for_circuit(weights, row["circuit"])
        summaries.append(
            {
                "circuit": row["circuit"],
                "layer": row["layer"],
                "production_rows": row["trace_len"] // 8,
                "records": row["shape"]["records"],
                "geometry": geometry,
                "median_ms": candidate,
                "reference_median_ms": reference,
                "speedup": speedup,
                "wording": wording,
                "current_base_weight": current,
                "development_proxy_weight": development,
                "future_current_weight": future,
            }
        )

    args.output_dir.mkdir(parents=True, exist_ok=True)
    json_path = args.output_dir / "natural-summary.json"
    json_path.write_text(json.dumps(summaries, separators=(",", ":")) + "\n")
    tsv_path = args.output_dir / "natural-summary.tsv"
    with tsv_path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(summaries[0]), delimiter="\t")
        writer.writeheader()
        writer.writerows(summaries)
    for row in summaries:
        print(
            f"{row['circuit']}:{row['layer']} {row['geometry']} "
            f"{row['median_ms']:.6f} ms {row['speedup']:.6f}x {row['wording']}"
        )
    print("WINDOWED_R0_NATURAL_TIMING_AUDIT_OK")


def path_argument(value: str) -> pathlib.Path:
    return pathlib.Path(value).resolve()


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser()
    subcommands = result.add_subparsers(dest="command", required=True)
    natural = subcommands.add_parser("natural")
    natural.add_argument("--manifest", type=path_argument, required=True)
    natural.add_argument("--weights", type=path_argument, required=True)
    natural.add_argument("--timing-root", type=path_argument, required=True)
    natural.add_argument("--nsys-root", type=path_argument)
    natural.add_argument("--output-dir", type=path_argument, required=True)
    natural.add_argument("--strict", action="store_true")
    natural.add_argument("--runner", type=path_argument)
    natural.add_argument("--bundle", type=path_argument)
    natural.add_argument("--source-root", type=path_argument)
    natural.add_argument("--build-flags", type=path_argument)
    natural.add_argument("--production-root", type=path_argument)
    dedup = subcommands.add_parser("envelope-dedup")
    dedup.add_argument("--points", type=path_argument, required=True)
    dedup.add_argument("--evidence", type=path_argument, required=True)
    dedup.add_argument("--output", type=path_argument, required=True)
    catalog = subcommands.add_parser("envelope-catalog")
    catalog.add_argument("--point-dag", type=path_argument, required=True)
    catalog.add_argument("--build-root", type=path_argument, required=True)
    catalog.add_argument("--manifest", type=path_argument, required=True)
    catalog.add_argument("--bundle", type=path_argument, required=True)
    catalog.add_argument("--output", type=path_argument, required=True)
    envelope = subcommands.add_parser("envelope")
    envelope.add_argument("--catalog", type=path_argument, required=True)
    envelope.add_argument("--manifest", type=path_argument, required=True)
    envelope.add_argument("--correctness-root", type=path_argument, required=True)
    envelope.add_argument("--timing-root", type=path_argument, required=True)
    envelope.add_argument("--production-root", type=path_argument, required=True)
    envelope.add_argument("--output-dir", type=path_argument, required=True)
    return result


def main() -> None:
    args = parser().parse_args()
    if args.command == "natural":
        natural_audit(args)
    elif args.command == "envelope-dedup":
        envelope_dedup_audit(args)
    elif args.command == "envelope-catalog":
        envelope_catalog(args)
    elif args.command == "envelope":
        envelope_audit(args)
    else:
        fail(f"unknown command {args.command}")


if __name__ == "__main__":
    main()
