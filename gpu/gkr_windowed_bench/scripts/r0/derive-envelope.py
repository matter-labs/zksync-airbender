#!/usr/bin/env python3
"""Derive and validate the deterministic R0 launch/register envelope."""

from __future__ import annotations

import argparse
import json
import pathlib
import sys
from typing import Any


THREADS_BY_GEOMETRY = {
    "cta288_pair": 288,
    "cta96_partitioned": 96,
    "cta96_x0_major": 96,
    "cta96_x1_major": 96,
    "cta96_x2_major": 96,
}
KINDS = ("natural", "launch", "maxreg", "combined")
RESOURCE_TUPLE_KEYS = (
    "registers",
    "stack_bytes",
    "local_bytes",
    "shared_bytes",
    "binary_sha256",
)


def fail(message: str) -> "NoReturn":
    raise SystemExit(message)


def load_json(path: pathlib.Path) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        fail(f"failed to read {path}: {error}")


def require_int(value: Any, label: str, *, positive: bool = False) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(f"{label} must be an integer")
    if positive and value <= 0:
        fail(f"{label} must be positive")
    return value


def validate_device(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail("device must be an object")
    device = dict(value)
    if not isinstance(device.get("device_id"), str) or not device["device_id"]:
        fail("device_id must be a nonempty string")
    for key in (
        "registers_per_sm",
        "max_threads_per_sm",
        "max_blocks_per_sm",
        "warp_size",
        "register_allocation_granularity",
    ):
        require_int(device.get(key), key, positive=True)
    if "shared_memory_per_sm" in device:
        require_int(device["shared_memory_per_sm"], "shared_memory_per_sm", positive=True)
    max_registers = device.get("max_registers_per_thread", 255)
    require_int(max_registers, "max_registers_per_thread", positive=True)
    device["max_registers_per_thread"] = max_registers
    return device


def physical_block_limit(device: dict[str, Any], threads: int, shared_bytes: int) -> int:
    limit = min(
        device["max_blocks_per_sm"],
        device["max_threads_per_sm"] // threads,
    )
    shared_per_sm = device.get("shared_memory_per_sm")
    if shared_per_sm is not None and shared_bytes > 0:
        limit = min(limit, shared_per_sm // shared_bytes)
    return limit


def register_cap(device: dict[str, Any], threads: int, blocks: int) -> int:
    granularity = device["register_allocation_granularity"]
    raw = device["registers_per_sm"] // (threads * blocks)
    return min(
        device["max_registers_per_thread"],
        (raw // granularity) * granularity,
    )


def residency_for_cap(
    device: dict[str, Any], threads: int, shared_bytes: int, cap: int
) -> int:
    allocated = ((cap + device["register_allocation_granularity"] - 1)
                 // device["register_allocation_granularity"]
                 * device["register_allocation_granularity"])
    return min(
        physical_block_limit(device, threads, shared_bytes),
        device["registers_per_sm"] // (threads * allocated),
    )


def adjacent_residency(
    device: dict[str, Any], threads: int, shared_bytes: int, natural_blocks: int
) -> tuple[int, int] | None:
    maximum = physical_block_limit(device, threads, shared_bytes)
    seen: set[tuple[int, int]] = set()
    candidates: list[tuple[int, int]] = []
    for requested in range(natural_blocks + 1, maximum + 1):
        cap = register_cap(device, threads, requested)
        if cap <= 0:
            continue
        residency = residency_for_cap(device, threads, shared_bytes, cap)
        if residency <= natural_blocks or residency > maximum:
            continue
        key = (residency, cap)
        if key not in seen:
            candidates.append(key)
            seen.add(key)
    return min(candidates) if candidates else None


def point_id(geometry: str, kind: str, min_blocks: int, maxreg: int) -> str:
    return f"{geometry}--{kind}-b{min_blocks}-r{maxreg}"


def make_point(
    geometry: str,
    kind: str,
    target_active_blocks: int,
    min_blocks: int,
    maxreg: int,
    parents: list[str],
) -> dict[str, Any]:
    return {
        "point_id": point_id(geometry, kind, min_blocks, maxreg),
        "geometry": geometry,
        "kind": kind,
        "target_active_blocks": target_active_blocks,
        "min_blocks": min_blocks,
        "maxreg": maxreg,
        "constraints": [
            {
                "geometry": geometry,
                "min_blocks": min_blocks,
                "maxreg": maxreg,
            }
        ],
        "parents": parents,
    }


def validate_point(device: dict[str, Any], point: Any) -> None:
    if not isinstance(point, dict):
        fail("point must be an object")
    geometry = point.get("geometry")
    if geometry not in THREADS_BY_GEOMETRY:
        fail(f"unknown geometry: {geometry!r}")
    kind = point.get("kind")
    if kind not in KINDS:
        fail(f"unknown point kind: {kind!r}")
    min_blocks = require_int(point.get("min_blocks"), "min_blocks")
    maxreg = require_int(point.get("maxreg"), "maxreg")
    target = require_int(
        point.get("target_active_blocks"), "target_active_blocks", positive=True
    )
    threads = THREADS_BY_GEOMETRY[geometry]
    maximum = physical_block_limit(device, threads, 0)
    if target > maximum:
        fail(f"impossible target_active_blocks for {geometry}: {target} > {maximum}")
    if min_blocks > maximum:
        fail(f"impossible min_blocks for {geometry}: {min_blocks} > {maximum}")
    if maxreg > device["max_registers_per_thread"]:
        fail(f"maxreg exceeds device limit: {maxreg}")
    if maxreg > 0 and maxreg % device["register_allocation_granularity"] != 0:
        fail("maxreg must be a rounded register threshold")
    expected_controls = {
        "natural": (0, 0),
        "launch": ("positive", 0),
        "maxreg": (0, "positive"),
        "combined": ("positive", "positive"),
    }[kind]
    if expected_controls[0] == "positive":
        if min_blocks <= 0:
            fail(f"{kind} point requires positive min_blocks")
    elif min_blocks != expected_controls[0]:
        fail(f"{kind} point requires min_blocks=0")
    if expected_controls[1] == "positive":
        if maxreg <= 0:
            fail(f"{kind} point requires positive maxreg")
    elif maxreg != expected_controls[1]:
        fail(f"{kind} point requires maxreg=0")
    expected_id = point_id(geometry, kind, min_blocks, maxreg)
    if point.get("point_id") != expected_id:
        fail(f"point id/control mismatch: expected {expected_id}")
    constraints = point.get("constraints")
    expected_constraint = {
        "geometry": geometry,
        "min_blocks": min_blocks,
        "maxreg": maxreg,
    }
    if constraints != [expected_constraint]:
        fail("each point must constrain exactly one geometry and exact control tuple")
    parents = point.get("parents")
    if not isinstance(parents, list) or any(not isinstance(parent, str) for parent in parents):
        fail("parents must be a list of point ids")
    if len(parents) != len(set(parents)):
        fail("duplicate point parent")
    natural_parent = point_id(geometry, "natural", 0, 0)
    if kind == "natural":
        if parents:
            fail("natural point must not have parents")
    elif kind == "launch":
        if min_blocks != target:
            fail("launch min_blocks must equal target_active_blocks")
        if parents != [natural_parent]:
            fail("launch point must have its natural point as parent")
    elif kind == "maxreg":
        expected_cap = register_cap(device, threads, target)
        if maxreg != expected_cap:
            fail(
                "maxreg must equal the rounded target residency threshold: "
                f"expected {expected_cap}"
            )
        if parents != [natural_parent]:
            fail("maxreg point must have its natural point as parent")
    else:
        expected_cap = register_cap(device, threads, target)
        if min_blocks != target or maxreg != expected_cap:
            fail("combined controls must equal the target residency thresholds")
        expected_parents = [
            point_id(geometry, "launch", target, 0),
            point_id(geometry, "maxreg", 0, expected_cap),
        ]
        if parents != expected_parents:
            fail("combined point must have its exact 1D points as parents")


def validate_points(device: dict[str, Any], value: Any) -> list[dict[str, Any]]:
    if not isinstance(value, dict) or not isinstance(value.get("points"), list):
        fail("point document must contain a points list")
    version = value.get("version")
    if isinstance(version, bool) or version != 1:
        fail("point document version must be integer 1")
    document_device = validate_device(value.get("device"))
    if document_device != device:
        fail("point document device does not match the pinned device")
    points = value["points"]
    ids: set[str] = set()
    seen: set[str] = set()
    for point in points:
        validate_point(device, point)
        if point["point_id"] in ids:
            fail(f"duplicate point id: {point['point_id']}")
        ids.add(point["point_id"])
        missing_parents = set(point["parents"]) - seen
        if missing_parents:
            fail(
                "point parents must exist earlier in the DAG: "
                f"{sorted(missing_parents)!r}"
            )
        seen.add(point["point_id"])
    return points


def validate_natural(device: dict[str, Any], value: Any) -> list[dict[str, Any]]:
    if not isinstance(value, list) or not value:
        fail("natural input must be a nonempty list")
    seen: set[str] = set()
    rows: list[dict[str, Any]] = []
    for row in value:
        if not isinstance(row, dict):
            fail("natural row must be an object")
        geometry = row.get("geometry")
        if geometry not in THREADS_BY_GEOMETRY or geometry in seen:
            fail(f"invalid or duplicate natural geometry: {geometry!r}")
        threads = require_int(row.get("threads"), "threads", positive=True)
        if threads != THREADS_BY_GEOMETRY[geometry]:
            fail(f"thread count mismatch for {geometry}")
        registers = require_int(row.get("registers"), "registers", positive=True)
        shared_bytes = require_int(row.get("shared_bytes"), "shared_bytes")
        active_blocks = require_int(row.get("active_blocks"), "active_blocks", positive=True)
        if shared_bytes < 0:
            fail("shared_bytes must be nonnegative")
        if active_blocks > physical_block_limit(device, threads, shared_bytes):
            fail(f"impossible natural active_blocks for {geometry}")
        if active_blocks > residency_for_cap(device, threads, shared_bytes, registers):
            fail(f"natural active_blocks exceed resource residency for {geometry}")
        rows.append(dict(row))
        seen.add(geometry)
    return sorted(rows, key=lambda row: row["geometry"])


def validate_results(results: Any, candidates: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    if not isinstance(results, list):
        fail("results must be a list")
    seen: set[str] = set()
    validated: list[dict[str, Any]] = []
    for row in results:
        if not isinstance(row, dict):
            fail("result row must be an object")
        candidate = candidates.get(row.get("point_id"))
        if candidate is None:
            fail(f"result does not bind a derived candidate: {row.get('point_id')!r}")
        point_id_value = row["point_id"]
        if point_id_value in seen:
            fail(f"duplicate result point id: {point_id_value}")
        seen.add(point_id_value)
        for key in (
            "geometry",
            "kind",
            "target_active_blocks",
            "min_blocks",
            "maxreg",
        ):
            if row.get(key) != candidate[key]:
                fail(f"result binding mismatch for {point_id_value}: {key}")
        outcome = row.get("outcome")
        if outcome not in ("success", "compiler_failure", "recording_failure"):
            fail(f"invalid result outcome for {point_id_value}")
        if outcome == "success":
            resources = row.get("resources")
            if not isinstance(resources, dict):
                fail(f"missing resources for successful point {point_id_value}")
            for key in RESOURCE_TUPLE_KEYS[:-1]:
                value = require_int(resources.get(key), f"resources.{key}")
                if value < 0:
                    fail(f"resources.{key} must be nonnegative")
            digest = resources.get("binary_sha256")
            if (
                not isinstance(digest, str)
                or len(digest) != 64
                or any(character not in "0123456789abcdef" for character in digest)
            ):
                fail("resources.binary_sha256 must be lowercase SHA-256")
        validated.append(dict(row))
    return validated


def derive(device: dict[str, Any], natural: list[dict[str, Any]], results: Any) -> dict[str, Any]:
    points: list[dict[str, Any]] = []
    pairs: dict[tuple[str, int], tuple[dict[str, Any], dict[str, Any]]] = {}
    for row in natural:
        geometry = row["geometry"]
        natural_id = point_id(geometry, "natural", 0, 0)
        natural_point = make_point(
            geometry, "natural", row["active_blocks"], 0, 0, []
        )
        points.append(natural_point)
        adjacent = adjacent_residency(
            device, row["threads"], row["shared_bytes"], row["active_blocks"]
        )
        if adjacent is None:
            continue
        target, cap = adjacent
        launch = make_point(geometry, "launch", target, target, 0, [natural_id])
        maxreg = make_point(geometry, "maxreg", target, 0, cap, [natural_id])
        points.extend((launch, maxreg))
        pairs[(geometry, target)] = (launch, maxreg)

    candidate_by_id = {point["point_id"]: point for point in points}
    if results is not None:
        result_rows = validate_results(results, candidate_by_id)
        result_by_id = {row["point_id"]: row for row in result_rows}
        for (geometry, target), (launch, maxreg) in pairs.items():
            launch_result = result_by_id.get(launch["point_id"])
            maxreg_result = result_by_id.get(maxreg["point_id"])
            if (
                launch_result is None
                or maxreg_result is None
                or launch_result["outcome"] != "success"
                or maxreg_result["outcome"] != "success"
            ):
                continue
            launch_tuple = tuple(
                launch_result["resources"][key] for key in RESOURCE_TUPLE_KEYS
            )
            maxreg_tuple = tuple(
                maxreg_result["resources"][key] for key in RESOURCE_TUPLE_KEYS
            )
            if launch_tuple != maxreg_tuple:
                points.append(
                    make_point(
                        geometry,
                        "combined",
                        target,
                        launch["min_blocks"],
                        maxreg["maxreg"],
                        [launch["point_id"], maxreg["point_id"]],
                    )
                )
    document = {"version": 1, "device": device, "points": points}
    validate_points(device, document)
    return document


def write_json(path: pathlib.Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    derive_parser = commands.add_parser("derive")
    derive_parser.add_argument("--device", type=pathlib.Path, required=True)
    derive_parser.add_argument("--natural", type=pathlib.Path, required=True)
    derive_parser.add_argument("--results", type=pathlib.Path)
    derive_parser.add_argument("--output", type=pathlib.Path, required=True)
    validate_parser = commands.add_parser("validate")
    validate_parser.add_argument("--device", type=pathlib.Path, required=True)
    validate_parser.add_argument("--points", type=pathlib.Path, required=True)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    device = validate_device(load_json(args.device))
    if args.command == "derive":
        natural = validate_natural(device, load_json(args.natural))
        results = load_json(args.results) if args.results is not None else None
        write_json(args.output, derive(device, natural, results))
    else:
        validate_points(device, load_json(args.points))


if __name__ == "__main__":
    main()
