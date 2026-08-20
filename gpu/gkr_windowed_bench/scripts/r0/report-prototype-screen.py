#!/usr/bin/env python3
"""Audit and normalize descriptive R0 prototype screen evidence."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import pathlib
import statistics
from collections import defaultdict
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[4]
SECTIONED_ROUND_STRIDES = (2, 4, 7, 8, 11)
SECTIONED_REGISTER_BUCKETS = {7: 96, 8: 80, 9: 72, 10: 64, 12: 56, 16: 40}
DEFAULT_SCREEN = ROOT / "target/windowed-gkr-r0-prototype-bank/screen/coordinates.json"
DEFAULT_EVIDENCE = ROOT / "target/windowed-gkr-r0-prototype-bank/screen/campaign-v3"
DEFAULT_PROTOTYPES = ROOT / "gpu/gkr_windowed_bench/artifacts/windowed_r0_prototype_manifest_v1.json"
DEFAULT_CAPACITY = ROOT / "gpu/gkr_windowed_bench/artifacts/windowed_r0_prototype_capacity_v1.json"
DEFAULT_RESOURCES = ROOT / "target/windowed-gkr-r0-prototype-bank/report/final-static/resource-table.tsv"
DEFAULT_OPCODES = ROOT / "target/windowed-gkr-r0-prototype-bank/report/final-static/opcodes.tsv"
DEFAULT_REPORT = ROOT / "target/windowed-gkr-r0-prototype-bank/report"
FORBIDDEN = {"winner", "selected", "rejected", "score", "threshold"}
PAIR_DIMENSIONS = (
    "circuit", "layer", "encoding", "inner", "outer", "geometry",
    "source_policy", "tile_capacity", "lineage",
)
THREADS_BY_GEOMETRY = {
    "cta288_pair": 288,
    "cta96_partitioned": 96,
    "cta96_x0_major": 96,
    "cta96_x1_major": 96,
    "cta96_x2_major": 96,
}
REGISTERS_PER_SM = 65_536
MAX_THREADS_PER_SM = 1_536
MAX_BLOCKS_PER_SM = 24
REGISTER_ALLOCATION_GRANULARITY = 8
SHARED_MEMORY_PER_SM = 102_400


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> Any:
    return json.loads(path.read_text())


def resource_rows(path: pathlib.Path) -> dict[str, dict[str, int]]:
    result = {}
    with path.open() as handle:
        for fields in csv.reader(handle, delimiter="\t"):
            if len(fields) >= 6:
                result[fields[0]] = {
                    "registers": int(fields[1]), "stack_bytes": int(fields[2]),
                    "static_shared_bytes": int(fields[3]), "local_bytes": int(fields[4]),
                    "constant_parameter_bytes": int(fields[5]),
                }
    return result


def opcode_rows(path: pathlib.Path) -> dict[str, dict[str, int]]:
    names = ("ldc", "ldg", "ldl", "stl", "lds", "sts", "call", "ret")
    result = {}
    with path.open() as handle:
        for fields in csv.reader(handle, delimiter="\t"):
            if len(fields) == len(names) + 1:
                result[fields[0]] = {
                    f"opcode_{name}": int(value)
                    for name, value in zip(names, fields[1:], strict=True)
                }
    return result


def measured_median(row: dict[str, Any]) -> float | None:
    values = [sample["milliseconds"] for sample in row["samples"] if not sample["warmup"]]
    return statistics.median(values) if values else None


def cell_checksum(cells: list[dict[str, Any]]) -> str:
    if len(cells) != 27:
        raise ValueError("screen cells must contain 27 values")
    payload = bytearray()
    for cell in cells:
        limbs = cell.get("limbs")
        if not isinstance(limbs, list) or len(limbs) != 4:
            raise ValueError("screen cell must contain four limbs")
        for limb in limbs:
            if type(limb) is not int or not 0 <= limb < 2**32:
                raise ValueError("invalid screen limb")
            payload += limb.to_bytes(4, "little")
    return hashlib.sha256(payload).hexdigest()


def validate_device_identity(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError("missing screen device identity")
    for field in (
        "cuda_device_index", "compute_capability_major", "compute_capability_minor",
        "cuda_driver_version", "cuda_runtime_version", "default_shared_memory_bytes",
        "opt_in_shared_memory_bytes",
    ):
        if type(value.get(field)) is not int or value[field] < 0:
            raise ValueError("invalid screen numeric device identity")
    clock = value.get("clock_policy")
    if not isinstance(clock, dict) or clock.get("uuid", "").lower() != value.get("uuid", "").lower() \
            or clock.get("name") != value.get("name") or not clock.get("raw_query"):
        raise ValueError("invalid screen clock-policy identity")
    if value["default_shared_memory_bytes"] > value["opt_in_shared_memory_bytes"]:
        raise ValueError("invalid screen shared-memory limits")
    return value


def validate_launchability_identity(value: Any, identity: dict[str, Any]) -> None:
    default = identity["default_shared_memory_bytes"]
    limit = identity["opt_in_shared_memory_bytes"]
    if not isinstance(value, dict) or len(value) != 1:
        raise ValueError("malformed screen launchability")
    if "launchable" in value:
        fact = value["launchable"]
        required = fact.get("dynamic_shared_bytes") if isinstance(fact, dict) else None
        opt_in = fact.get("opt_in") if isinstance(fact, dict) else None
        if type(required) is not int or type(opt_in) is not bool \
                or (not opt_in and required > default) \
                or (opt_in and not default < required <= limit):
            raise ValueError("screen launchability contradicts device limits")
    elif "unlaunchable_capacity" in value:
        fact = value["unlaunchable_capacity"]
        if not isinstance(fact, dict) or type(fact.get("required_bytes")) is not int \
                or fact["required_bytes"] <= limit or fact.get("device_limit_bytes") != limit:
            raise ValueError("screen capacity rejection contradicts device limits")
    else:
        raise ValueError("unknown screen launchability")


def validate_execution(binding: dict[str, Any], state: dict[str, Any], directory: pathlib.Path) -> None:
    execution = binding.get("execution")
    lock = execution.get("gpu_lock") if isinstance(execution, dict) else None
    if not isinstance(lock, dict) or lock.get("mode") not in ("none", "repository_file_lock") \
            or not isinstance(execution.get("command"), list):
        raise ValueError(f"invalid screen execution binding: {directory}")
    if lock["mode"] == "repository_file_lock":
        path = pathlib.Path(lock.get("path", ""))
        if not path.is_file() or sha256(path) != lock.get("sha256") \
                or execution["command"][:1] != [str(path)]:
            raise ValueError(f"screen lock binding mismatch: {directory}")
    elif lock.get("path") is not None or lock.get("sha256") is not None:
        raise ValueError(f"unlocked screen contains lock path: {directory}")
    driver = directory / "driver.log"
    if not driver.is_file() or state.get("driver_sha256") != sha256(driver):
        raise ValueError(f"screen driver hash mismatch: {directory}")
    text = driver.read_text(errors="replace")
    markers = (
        "[with_gpu_lock] waiting for GPU lock:",
        "[with_gpu_lock] acquired GPU lock:",
        "[with_gpu_lock] releasing GPU lock:",
    )
    if lock["mode"] == "repository_file_lock":
        if any(text.count(marker) != 1 for marker in markers) \
                or "status=0" not in next(line for line in text.splitlines() if markers[2] in line):
            raise ValueError(f"screen lock lifecycle mismatch: {directory}")
    elif any(marker in text for marker in markers):
        raise ValueError(f"unlocked screen contains lock lifecycle: {directory}")


def percent(candidate: float | None, baseline: float | None) -> float | None:
    return None if candidate is None or baseline is None else 100.0 * (candidate / baseline - 1.0)


def comparison_wording(candidate: float, baseline: float) -> dict[str, Any]:
    if any(not math.isfinite(value) or value <= 0 for value in (candidate, baseline)):
        raise ValueError("comparison durations must be finite and positive")
    delta = round((candidate / baseline - 1.0) * 100.0, 12)
    if delta < 0:
        wording = f"candidate is {abs(delta):.3f}% faster than baseline"
    elif delta > 0:
        wording = f"candidate is {delta:.3f}% slower than baseline"
    else:
        wording = "candidate is equal to baseline"
    return {"percent_positive_is_slower": delta, "wording": wording}


def sectioned_coordinate_hash(coordinate_key: str) -> int:
    value = 0xCBF29CE484222325
    for byte in coordinate_key.encode():
        value = ((value * 0x100000001B3) & ((1 << 64) - 1)) ^ byte
    return value


def sectioned_round_order(coordinate_key: str, round_index: int) -> list[int]:
    start = (sectioned_coordinate_hash(coordinate_key) + round_index) % 15
    stride = SECTIONED_ROUND_STRIDES[round_index]
    return [(start + index * stride) % 15 for index in range(15)]


def sectioned_symbol_domain(manifest: dict[str, Any], shape_bits: int) -> list[dict[str, Any]]:
    rows = [row for row in manifest["symbols"] if row.get("shape_bits") == shape_bits]
    if len(rows) != 15:
        raise ValueError("sectioned manifest shape must have exactly 15 candidates")
    counts = {geometry: sum(row["geometry"] == geometry for row in rows)
              for geometry in ("wide9", "split3", "serial3_low", "serial3_high")}
    if counts != {"wide9": 1, "split3": 7, "serial3_low": 7, "serial3_high": 0}:
        raise ValueError("sectioned manifest candidate geometry domain mismatch")
    return rows


def sectioned_register_bucket(geometry: str, min_blocks: int | None) -> int | None:
    if geometry == "wide9":
        return 72 if min_blocks == 3 else None
    return SECTIONED_REGISTER_BUCKETS.get(min_blocks)


def sectioned_bound_summaries(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, int | None], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row.get("arm_kind") == "sectioned":
            grouped[(row["geometry"], row.get("min_blocks"))].append(row)
    result = []
    for (geometry, min_blocks), group in sorted(
        grouped.items(), key=lambda item: (item[0][0], -1 if item[0][1] is None else item[0][1])
    ):
        deltas = [row["vs_generic_percent"] for row in group]
        natural_deltas = [row["vs_same_geometry_natural_percent"] for row in group]
        registers = [row["registers"] for row in group]
        instructions = [row["instructions"] for row in group]
        result.append({
            "geometry": geometry,
            "min_blocks": min_blocks,
            "coordinates": len(group),
            "theoretical_register_bucket": sectioned_register_bucket(geometry, min_blocks),
            "median_percent_positive_is_slower": statistics.median(deltas),
            "min_percent_positive_is_slower": min(deltas),
            "max_percent_positive_is_slower": max(deltas),
            "median_vs_same_geometry_natural_percent_positive_is_slower": statistics.median(natural_deltas),
            "min_vs_same_geometry_natural_percent_positive_is_slower": min(natural_deltas),
            "max_vs_same_geometry_natural_percent_positive_is_slower": max(natural_deltas),
            "faster_coordinates": sum(value < 0 for value in deltas),
            "equal_coordinates": sum(value == 0 for value in deltas),
            "slower_coordinates": sum(value > 0 for value in deltas),
            "registers_min": min(registers),
            "registers_median": statistics.median(registers),
            "registers_max": max(registers),
            "stack_positive_coordinates": sum(row["stack_bytes"] > 0 for row in group),
            "local_positive_coordinates": sum(row["local_bytes"] > 0 for row in group),
            "instructions_median": statistics.median(instructions),
            "natural_identical_coordinates": sum(row["identical_to_natural"] for row in group),
        })
    return result


def validate_sectioned_screen_group(
    rows: list[dict[str, Any]], manifest: dict[str, Any], manifest_sha256: str,
) -> None:
    if len(rows) != 16:
        raise ValueError("sectioned screen must contain exactly 15 sectioned arms plus generic")
    generic = [row for row in rows if row.get("arm_kind") == "generic"]
    sectioned = [row for row in rows if row.get("arm_kind") == "sectioned"]
    if len(generic) != 1 or len(sectioned) != 15:
        raise ValueError("sectioned screen arm-kind coverage mismatch")
    shape_values = {row.get("lowered_shape_bits") for row in rows}
    if len(shape_values) != 1 or type(next(iter(shape_values))) is not int:
        raise ValueError("sectioned screen lowered shape mismatch")
    shape_bits = next(iter(shape_values))
    domain = sectioned_symbol_domain(manifest, shape_bits)
    expected_symbols = {row["candidate_id"]: row for row in domain}
    if {row.get("observation", {}).get("candidate_id") for row in sectioned} != set(expected_symbols):
        raise ValueError("sectioned screen exact candidate coverage mismatch")
    if generic[0].get("min_blocks") is not None or generic[0].get("compiled_shape_bits") is not None:
        raise ValueError("generic reference controls must be null")
    observations = [row.get("observation", {}) for row in rows]
    input_hashes = {observation.get("input_sha256") for observation in observations}
    if None in input_hashes or len(input_hashes) != 1:
        raise ValueError("sectioned screen did not reuse one prepared input")
    setup_fields = (
        "coordinate_cpu_setup_seconds",
        "coordinate_harness_setup_seconds",
        "coordinate_execution_wall_seconds",
    )
    setup_rows = {tuple(row.get(field) for field in setup_fields) for row in rows}
    if len(setup_rows) != 1:
        raise ValueError("sectioned screen coordinate setup differs between geometries")
    if any(
        type(row.get(field)) not in (int, float)
        or not math.isfinite(row[field])
        or row[field] <= 0
        for row in rows
        for field in setup_fields
    ):
        raise ValueError("sectioned screen setup duration is invalid")
    if len({json.dumps(observation.get("device_identity"), sort_keys=True) for observation in observations}) != 1:
        raise ValueError("sectioned screen device identity drift")

    coordinate_key = f"{observations[0].get('circuit')}:{observations[0].get('layer')}"
    ordered_ids = [row["candidate_id"] for row in domain]
    pilot_positions = set()
    for row, observation in zip(rows, observations, strict=True):
        validate_device_identity(observation.get("device_identity"))
        if row.get("manifest_sha256") != manifest_sha256:
            raise ValueError("sectioned screen manifest hash drift")
        if not isinstance(row.get("executable_sha256"), str) or len(row["executable_sha256"]) != 64:
            raise ValueError("sectioned screen executable hash is invalid")
        if row["arm_kind"] == "sectioned":
            symbol = expected_symbols[observation["candidate_id"]]
            if row.get("geometry") != symbol["geometry"] \
                    or row.get("min_blocks") != symbol.get("min_blocks") \
                    or row.get("compiled_shape_bits") != shape_bits \
                    or observation.get("launch", {}).get("symbol") != symbol["symbol"]:
                raise ValueError("sectioned screen manifest binding mismatch")
        if not observation.get("passing") or observation.get("failure") is not None:
            raise ValueError("sectioned screen contains a failing observation")
        checksums = {observation.get("checksum"), observation.get("expected_checksum")}
        if None in checksums or len(checksums) != 1:
            raise ValueError("sectioned screen checksum drift")
        if cell_checksum(observation.get("cells")) != observation["checksum"]:
            raise ValueError("sectioned screen cell checksum mismatch")
        pilot = row.get("pilot_samples")
        retained = row.get("samples")
        if not isinstance(pilot, list) or not isinstance(retained, list):
            raise ValueError("sectioned screen raw samples are missing")
        if len(pilot) != 3 or len(retained) != 50 or row.get("retained_samples") != 50:
            raise ValueError("sectioned screen raw sample cardinality mismatch")
        for samples, phase in ((pilot, "pilot"), (retained, "retained")):
            flags = [sample.get("warmup") for sample in samples]
            if any(type(flag) is not bool for flag in flags):
                raise ValueError("sectioned screen warmup flag is not boolean")
            if flags != [False] * len(samples):
                raise ValueError("sectioned screen warmup sequence mismatch")
            identity = observation.get("candidate_id")
            if any(
                sample.get("configuration_id") != identity
                or sample.get("version") != 2
                or sample.get("circuit") != observation.get("circuit")
                or sample.get("layer") != observation.get("layer")
                or sample.get("log_trace") != observation.get("log_trace")
                or sample.get("seed") != observation.get("seed")
                or sample.get("phase") != phase
                or sample.get("symbol") != observation.get("launch", {}).get("symbol")
                or sample.get("min_blocks") != row.get("min_blocks")
                or sample.get("compiled_shape_bits") != row.get("compiled_shape_bits")
                or sample.get("manifest_sha256") != manifest_sha256
                or sample.get("executable_sha256") != row.get("executable_sha256")
                or sample.get("input_sha256") != observation.get("input_sha256")
                or sample.get("program_sha256") != observation.get("program_sha256")
                or sample.get("device_identity") != observation.get("device_identity")
                or type(sample.get("milliseconds")) not in (int, float)
                or not math.isfinite(sample["milliseconds"])
                or sample["milliseconds"] <= 0
                for sample in samples
            ):
                raise ValueError("sectioned screen sample identity mismatch")
        if [sample.get("sample_index") for sample in pilot] != [0, 1, 2] \
                or any(sample.get("round_index") != 0 or sample.get("chunk") != "pilot"
                       or sample.get("pass_index") != 0 for sample in pilot):
            raise ValueError("sectioned screen pilot key mismatch")
        pilot_positions.add(pilot[0].get("pass_position"))
        measured_pilot = [sample["milliseconds"] for sample in pilot]
        if statistics.median(measured_pilot) != row.get("pilot_median_ms"):
            raise ValueError("sectioned screen pilot median mismatch")
        if row["arm_kind"] == "generic":
            expected_keys = {
                (round_index, chunk, sample_index, position)
                for round_index in range(5)
                for chunk, position in (("reference_before", 0), ("reference_after", 16))
                for sample_index in range(5)
            }
        else:
            candidate_index = ordered_ids.index(observation["candidate_id"])
            expected_keys = {
                (round_index, "candidate", sample_index,
                 sectioned_round_order(coordinate_key, round_index).index(candidate_index) + 1)
                for round_index in range(5) for sample_index in range(10)
            }
        observed_keys = {
            (sample.get("round_index"), sample.get("chunk"), sample.get("sample_index"),
             sample.get("pass_position")) for sample in retained
        }
        if observed_keys != expected_keys \
                or any(sample.get("pass_index") != sample.get("round_index") for sample in retained):
            raise ValueError("sectioned screen retained key mismatch")
    if pilot_positions != set(range(16)):
        raise ValueError("sectioned screen pilot order is incomplete")


def validate_sectioned_bindings(
    bindings: dict[str, Any],
    rows: list[dict[str, Any]],
    manifest_sha256: str,
    executable_sha256: str,
    screen_root: pathlib.Path,
) -> None:
    if bindings.get("version") != 1:
        raise ValueError("sectioned bindings version mismatch")
    if bindings.get("manifest_sha256") != manifest_sha256:
        raise ValueError("sectioned bindings manifest hash mismatch")
    if bindings.get("executable_sha256") != executable_sha256:
        raise ValueError("sectioned bindings executable hash mismatch")
    binding_rows = bindings.get("screen")
    if not isinstance(binding_rows, list):
        raise ValueError("sectioned bindings screen rows are missing")

    grouped: dict[tuple[str, int], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        observation = row.get("observation", {})
        key = (observation.get("circuit"), observation.get("layer"))
        if type(key[0]) is not str or type(key[1]) is not int:
            raise ValueError("sectioned screen coordinate binding is invalid")
        grouped[key].append(row)
    indexed = {}
    for binding in binding_rows:
        key = (binding.get("circuit"), binding.get("layer"))
        if key in indexed:
            raise ValueError("duplicate sectioned screen binding")
        indexed[key] = binding
    if set(indexed) != set(grouped):
        raise ValueError("sectioned screen binding coverage mismatch")

    for (circuit, layer), group in grouped.items():
        binding = indexed[(circuit, layer)]
        stem = f"{circuit}-{layer}"
        rows_path = screen_root / f"{stem}.jsonl"
        command_path = screen_root / f"{stem}.command"
        driver_path = screen_root / f"{stem}.driver.log"
        if not all(path.is_file() for path in (rows_path, command_path, driver_path)):
            raise ValueError(f"missing sectioned screen binding files for {circuit}:{layer}")
        if binding.get("rows") != len(group) or binding.get("rows_sha256") != sha256(rows_path):
            raise ValueError(f"sectioned screen rows binding mismatch for {circuit}:{layer}")
        if binding.get("command_sha256") != sha256(command_path):
            raise ValueError(f"sectioned screen command binding mismatch for {circuit}:{layer}")
        if binding.get("driver_sha256") != sha256(driver_path):
            raise ValueError(f"sectioned screen driver binding mismatch for {circuit}:{layer}")
        raw_rows = [json.loads(line) for line in rows_path.read_text().splitlines() if line]
        if raw_rows != group:
            raise ValueError(f"sectioned screen rows differ from bound raw file for {circuit}:{layer}")

        observations = [row["observation"] for row in group]
        expected = {
            "input_sha256": observations[0].get("input_sha256"),
            "program_sha256": observations[0].get("program_sha256"),
            "checksum": observations[0].get("checksum"),
            "device_identity": observations[0].get("device_identity"),
        }
        if any(binding.get(field) != value for field, value in expected.items()):
            raise ValueError(f"sectioned screen semantic binding mismatch for {circuit}:{layer}")
        if any(
            row.get("manifest_sha256") != manifest_sha256
            or row.get("executable_sha256") != executable_sha256
            for row in group
        ):
            raise ValueError(f"sectioned screen executable/manifest row drift for {circuit}:{layer}")


def normalize_sectioned_rows(
    rows: list[dict[str, Any]],
    manifest: dict[str, Any],
    manifest_sha256: str,
    resources: dict[str, dict[str, int]],
    current_baselines: dict[tuple[str, int], float],
    historical_baselines: dict[tuple[str, int], float],
) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, int], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        observation = row.get("observation", {})
        grouped[(observation.get("circuit"), observation.get("layer"))].append(row)
    normalized = []
    for key, group in sorted(grouped.items()):
        validate_sectioned_screen_group(group, manifest, manifest_sha256)
        baseline = current_baselines.get(key)
        if baseline is None:
            raise ValueError(f"missing current dedicated baseline for {key}")
        generic_rows = [row for row in group if row["arm_kind"] == "generic"]
        generic_median = statistics.median(
            sample["milliseconds"] for sample in generic_rows[0]["samples"]
        )
        natural_medians = {}
        for natural_row in group:
            if natural_row["arm_kind"] != "sectioned":
                continue
            natural_bound = 3 if natural_row["geometry"] == "wide9" else None
            if natural_row["min_blocks"] == natural_bound:
                natural_medians[natural_row["geometry"]] = statistics.median(
                    sample["milliseconds"] for sample in natural_row["samples"]
                )
        if set(natural_medians) != {"wide9", "split3", "serial3_low"}:
            raise ValueError(f"sectioned natural geometry coverage mismatch for {key}")
        for row in group:
            observation = row["observation"]
            symbol = observation["launch"]["symbol"]
            resource = resources.get(symbol)
            if resource is None:
                raise ValueError(f"missing sectioned resource row for {symbol}")
            measured = [
                sample["milliseconds"] for sample in row["samples"] if not sample["warmup"]
            ]
            median_ms = statistics.median(measured)
            historical = historical_baselines.get(key)
            geometry_natural = (
                natural_medians[row["geometry"]]
                if row["arm_kind"] == "sectioned" else None
            )
            normalized.append({
                "version": 2,
                "circuit": key[0],
                "layer": key[1],
                "log_trace": observation["log_trace"],
                "lowered_shape_bits": row["lowered_shape_bits"],
                "compiled_shape_bits": row["compiled_shape_bits"],
                "geometry": row["geometry"],
                "min_blocks": row["min_blocks"],
                "theoretical_register_bucket": sectioned_register_bucket(
                    row["geometry"], row["min_blocks"]
                ),
                "arm_kind": row["arm_kind"],
                "candidate_id": (
                    observation["candidate_id"]
                    if row["arm_kind"] == "sectioned" else "generic/reference"
                ),
                "symbol": symbol,
                "median_ms": median_ms,
                "generic_median_ms": generic_median,
                "vs_generic_percent": round((median_ms / generic_median - 1.0) * 100.0, 12),
                "vs_generic": comparison_wording(median_ms, generic_median),
                "same_geometry_natural_median_ms": geometry_natural,
                "vs_same_geometry_natural_percent": (
                    round((median_ms / geometry_natural - 1.0) * 100.0, 12)
                    if geometry_natural is not None else None
                ),
                "vs_same_geometry_natural": (
                    comparison_wording(median_ms, geometry_natural)
                    if geometry_natural is not None else None
                ),
                "secondary_task10_median_ms": baseline,
                "secondary_versus_task10": comparison_wording(median_ms, baseline),
                "secondary_historical_prototype_median_ms": historical,
                "secondary_versus_historical_prototype": (
                    comparison_wording(median_ms, historical)
                    if historical is not None else None
                ),
                "retained_samples": row["retained_samples"],
                "pilot_median_ms": row["pilot_median_ms"],
                "input_sha256": observation["input_sha256"],
                "program_sha256": observation["program_sha256"],
                "checksum": observation["checksum"],
                "launch": observation["launch"],
                "candidate_wall_seconds": row["candidate_wall_seconds"],
                "coordinate_cpu_setup_seconds": row["coordinate_cpu_setup_seconds"],
                "coordinate_harness_setup_seconds": row["coordinate_harness_setup_seconds"],
                "coordinate_execution_wall_seconds": row["coordinate_execution_wall_seconds"],
                "registers": resource["registers"],
                "stack_bytes": resource["stack_bytes"],
                "shared_bytes": resource.get("shared_bytes", resource.get("static_shared_bytes")),
                "local_bytes": resource["local_bytes"],
                "sass_sha256": resource.get("sass_sha256"),
            })
    return normalized


def sectioned_resource_rows(path: pathlib.Path) -> dict[str, dict[str, Any]]:
    result = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        fields = line.split()
        symbol = fields[0]
        values = {}
        for field in fields[1:]:
            if ":" not in field:
                continue
            name, value = field.split(":", 1)
            if name in {"REG", "STACK", "SHARED", "LOCAL"}:
                values[name] = int(value)
            elif name == "SASS":
                values[name] = value
        if not {"REG", "STACK", "SHARED", "LOCAL"}.issubset(values):
            raise ValueError(f"malformed sectioned resource row: {line}")
        result[symbol] = {
            "registers": values["REG"],
            "stack_bytes": values["STACK"],
            "shared_bytes": values["SHARED"],
            "local_bytes": values["LOCAL"],
            "sass_sha256": values.get("SASS"),
        }
    return result


def sectioned_opcode_rows(path: pathlib.Path) -> dict[str, dict[str, int]]:
    names = ("instructions", "ldc", "ldcu", "ldg", "forbidden", "bssy", "bsync")
    result = {}
    for line in path.read_text().splitlines():
        fields = line.split("\t")
        if len(fields) != len(names) + 1:
            raise ValueError(f"malformed sectioned opcode row: {line}")
        result[fields[0]] = {
            name: int(value) for name, value in zip(names, fields[1:], strict=True)
        }
    return result


def sectioned_opcode_for_symbol(
    opcodes: dict[str, dict[str, int]], symbol: str,
) -> dict[str, int]:
    opcode = opcodes.get(symbol)
    if opcode is None:
        raise ValueError(f"missing sectioned opcode row for {symbol}")
    return opcode


def run_sectioned_report(args: argparse.Namespace) -> int:
    rows_path = pathlib.Path(args.sectioned_rows).resolve()
    manifest_path = pathlib.Path(args.sectioned_manifest).resolve()
    resources_path = pathlib.Path(args.sectioned_resources).resolve()
    opcodes_path = pathlib.Path(args.sectioned_opcodes).resolve()
    baseline_path = pathlib.Path(args.current_baseline).resolve()
    bindings_path = pathlib.Path(args.sectioned_bindings).resolve()
    executable_path = pathlib.Path(args.sectioned_executable).resolve()
    screen_root = pathlib.Path(args.sectioned_screen_root).resolve()
    for path in (
        rows_path, manifest_path, resources_path, opcodes_path, baseline_path,
        bindings_path, executable_path,
    ):
        if not path.is_file():
            raise ValueError(f"missing sectioned report input: {path}")
    if not screen_root.is_dir():
        raise ValueError(f"missing sectioned screen evidence root: {screen_root}")
    rows = [json.loads(line) for line in rows_path.read_text().splitlines() if line]
    resources = sectioned_resource_rows(resources_path)
    opcodes = sectioned_opcode_rows(opcodes_path)
    baseline_rows = load(baseline_path)
    current_baselines = {
        (row["circuit"], row["layer"]): row["median_ms"]
        for row in baseline_rows if row["geometry"] == "cta288_pair"
    }
    historical = {("add_sub_lui_auipc_mop", 0): args.historical_add_sub_ms}
    manifest = load(manifest_path)
    bindings = load(bindings_path)
    executable_sha256 = sha256(executable_path)
    manifest_sha256 = sha256(manifest_path)
    validate_sectioned_bindings(
        bindings, rows, manifest_sha256, executable_sha256, screen_root,
    )
    normalized = normalize_sectioned_rows(
        rows, manifest, manifest_sha256, resources, current_baselines, historical
    )
    symbols = {row["candidate_id"]: row for row in manifest["symbols"]}
    for row in normalized:
        if row["arm_kind"] == "sectioned":
            symbol = symbols.get(row["candidate_id"])
            if symbol is None or symbol["symbol"] != row["symbol"] \
                    or symbol["geometry"] != row["geometry"] \
                    or symbol.get("min_blocks") != row["min_blocks"]:
                raise ValueError(f"sectioned manifest binding mismatch for {row['candidate_id']}")
        opcode = sectioned_opcode_for_symbol(opcodes, row["symbol"])
        row.update(opcode)
        row["instruction_count"] = opcode["instructions"]
    by_key = {
        (row["lowered_shape_bits"], row["geometry"], row["min_blocks"]): row
        for row in normalized if row["arm_kind"] == "sectioned"
    }
    for row in normalized:
        if row["arm_kind"] == "generic":
            row["identical_to_natural"] = True
            continue
        natural_bound = 3 if row["geometry"] == "wide9" else None
        natural = by_key.get((row["lowered_shape_bits"], row["geometry"], natural_bound))
        row["identical_to_natural"] = (
            natural is not None and row.get("sass_sha256") is not None
            and row["sass_sha256"] == natural.get("sass_sha256")
        )
    summaries = sectioned_bound_summaries(normalized)
    report = pathlib.Path(args.report_root).resolve()
    report.mkdir(parents=True, exist_ok=True)
    jsonl = report / "sectioned-screen-normalized.jsonl"
    jsonl.write_text("".join(
        json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n" for row in normalized
    ))
    write_tsv(report / "sectioned-screen-normalized.tsv", normalized)
    summary_json = report / "sectioned-bound-summary.json"
    summary_json.write_text(json.dumps(summaries, sort_keys=True, separators=(",", ":")) + "\n")
    write_tsv(report / "sectioned-bound-summary.tsv", summaries)
    markdown = [
        "# Sectioned R0 production screen", "",
        "This is a five-coordinate descriptive screen, not a final kernel selection.",
        "Percentages use `(candidate / baseline - 1) × 100`; each row also spells out faster/slower.", "",
        "The in-session generic row is the primary denominator. Task 10 and the 10.454048 ms add/sub prototype are secondary cross-session context only.", "",
        "| coordinate | candidate | geometry | min blocks | register bucket | median ms | registers | stack/local/shared B | instructions | SASS SHA-256 | natural-identical | versus same-geometry natural | versus in-session generic | secondary versus Task 10 | secondary versus historical prototype |",
        "|---|---|---:|---:|---:|---:|---:|---:|---:|---|---:|---|---|---|---|",
    ]
    for row in normalized:
        historical_wording = (
            row["secondary_versus_historical_prototype"]["wording"]
            if row["secondary_versus_historical_prototype"] is not None else "n/a"
        )
        markdown.append(
            f"| {row['circuit']}:{row['layer']} | {row['candidate_id']} | {row['geometry']} | "
            f"{row['min_blocks']} | {row['theoretical_register_bucket']} | {row['median_ms']:.6f} | {row['registers']} | "
            f"{row['stack_bytes']}/{row['local_bytes']}/{row['shared_bytes']} | {row['instructions']} | "
            f"{row['sass_sha256']} | {row['identical_to_natural']} | "
            f"{row['vs_same_geometry_natural']['wording'] if row['vs_same_geometry_natural'] else 'n/a'} | "
            f"{row['vs_generic']['wording']} | {row['secondary_versus_task10']['wording']} | "
            f"{historical_wording} |"
        )
    markdown.extend([
        "", "## Geometry/bound summaries", "",
        "These aggregates retain all five coordinates and are descriptive; they do not select a universal configuration.", "",
        "| geometry | min blocks | register bucket | median vs same-geometry natural | range vs natural | median vs generic | range vs generic | faster/equal/slower vs generic | register range | stack-positive | median instructions | natural-identical |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ])
    for row in summaries:
        markdown.append(
            f"| {row['geometry']} | {row['min_blocks']} | {row['theoretical_register_bucket']} | "
            f"{row['median_vs_same_geometry_natural_percent_positive_is_slower']:.3f}% | "
            f"{row['min_vs_same_geometry_natural_percent_positive_is_slower']:.3f}%..{row['max_vs_same_geometry_natural_percent_positive_is_slower']:.3f}% | "
            f"{row['median_percent_positive_is_slower']:.3f}% | "
            f"{row['min_percent_positive_is_slower']:.3f}%..{row['max_percent_positive_is_slower']:.3f}% | "
            f"{row['faster_coordinates']}/{row['equal_coordinates']}/{row['slower_coordinates']} | "
            f"{row['registers_min']}..{row['registers_max']} | {row['stack_positive_coordinates']} | "
            f"{row['instructions_median']:.1f} | {row['natural_identical_coordinates']} |"
        )
    markdown.extend(["", "All candidates passed checksum validation; full raw samples and setup walls remain in the bound JSONL evidence.", ""])
    markdown_path = report / "sectioned-screen.md"
    markdown_path.write_text("\n".join(markdown))
    hashes = {
        "version": 1,
        "rows": len(normalized),
        "coordinates": len({(row["circuit"], row["layer"]) for row in normalized}),
        "inputs": {
            "rows_sha256": sha256(rows_path),
            "bindings_sha256": sha256(bindings_path),
            "manifest_sha256": manifest_sha256,
            "executable_sha256": executable_sha256,
            "resources_sha256": sha256(resources_path),
            "opcodes_sha256": sha256(opcodes_path),
            "current_baseline_sha256": sha256(baseline_path),
        },
        "outputs": {
            "jsonl_sha256": sha256(jsonl),
            "tsv_sha256": sha256(report / "sectioned-screen-normalized.tsv"),
            "markdown_sha256": sha256(markdown_path),
            "bound_summary_json_sha256": sha256(summary_json),
            "bound_summary_tsv_sha256": sha256(report / "sectioned-bound-summary.tsv"),
        },
    }
    (report / "sectioned-screen-hashes.json").write_text(
        json.dumps(hashes, sort_keys=True, separators=(",", ":")) + "\n"
    )
    print(f"WINDOWED_R0_SECTIONED_SCREEN_OK rows={len(normalized)} coordinates={hashes['coordinates']}")
    return 0


def _matches(row: dict[str, Any], filters: dict[str, Any]) -> bool:
    return all(row.get(key) == value for key, value in filters.items())


def _rounded(value: float) -> float:
    rounded = round(value, 12)
    return 0.0 if rounded == 0 else rounded


def paired_factor_summary(
    rows: list[dict[str, Any]], *, label: str, baseline: dict[str, Any],
    candidate: dict[str, Any], varying: tuple[str, ...],
) -> dict[str, Any]:
    key_fields = tuple(field for field in PAIR_DIMENSIONS if field not in varying)

    def indexed(filters: dict[str, Any]) -> dict[tuple[Any, ...], dict[str, Any]]:
        result = {}
        for row in rows:
            if row.get("median_ms") is None or not _matches(row, filters):
                continue
            key = tuple(row.get(field) for field in key_fields)
            if key in result:
                raise ValueError(f"duplicate controlled pair key for {label}: {key}")
            result[key] = row
        return result

    base = indexed(baseline)
    other = indexed(candidate)
    values = sorted(
        100.0 * (float(other[key]["median_ms"]) / float(base[key]["median_ms"]) - 1.0)
        for key in base.keys() & other.keys()
    )
    if not values:
        raise ValueError(f"controlled comparison has no pairs: {label}")

    def quantile(fraction: float) -> float:
        return values[round(fraction * (len(values) - 1))]

    return {
        "comparison": label,
        "pairs": len(values),
        "median_percent_positive_is_slower": _rounded(statistics.median(values)),
        "p10_percent_positive_is_slower": _rounded(quantile(0.1)),
        "p90_percent_positive_is_slower": _rounded(quantile(0.9)),
        "candidate_faster_pairs": sum(value < 0 for value in values),
        "equal_pairs": sum(value == 0 for value in values),
        "candidate_slower_pairs": sum(value > 0 for value in values),
    }


def capacity_fields(
    coordinate: dict[str, Any], encoding: str, tile_capacity: int | None,
) -> dict[str, Any]:
    encoding_rows = [row for row in coordinate["encodings"] if row["encoding"] == encoding]
    descriptor_capacity = None if tile_capacity is None else f"c{tile_capacity}"
    descriptor_rows = [
        row for row in coordinate["descriptors"]
        if row["encoding"] == encoding and row["tile_capacity"] == descriptor_capacity
    ]
    if len(encoding_rows) != 1 or len(descriptor_rows) != 1:
        raise ValueError(f"capacity join mismatch: {encoding}/{descriptor_capacity}")
    encoded = encoding_rows[0]
    descriptor = descriptor_rows[0]
    compact = coordinate["compact"] if encoding == "compact_r0_port" else None
    return {
        "semantic_records": encoded["semantic_records"],
        "represented_records": encoded["represented_records"],
        "bf_records": encoded["bf_records"],
        "e4_records": encoded["e4_records"],
        "group_headers": encoded["group_headers"],
        "logical_program_u16_words": encoded["logical_program_u16_words"],
        "source_slot_u16_words": encoded["source_slot_u16_words"],
        "logical_program_and_slots_bytes": 2 * (
            encoded["logical_program_u16_words"] + encoded["source_slot_u16_words"]
        ),
        "model_json_bytes": encoded["model_json_bytes"],
        "compact_escape_words": None if compact is None else compact["escape_words"],
        "compact_weighted_escape_source_uses": (
            None if compact is None else compact["weighted_escape_source_uses"]
        ),
        "max_dynamic_shared_bytes": descriptor["max_dynamic_shared_bytes"],
        "capacity_program_sha256": descriptor["program_sha256"],
        "capacity_tile_sha256": descriptor["tile_sha256"],
    }


def inferred_residency(
    *, registers: int, static_shared_bytes: int, dynamic_shared_bytes: int,
    geometry: str,
) -> tuple[int, float]:
    threads = THREADS_BY_GEOMETRY[geometry]
    allocated_registers = (
        (registers + REGISTER_ALLOCATION_GRANULARITY - 1)
        // REGISTER_ALLOCATION_GRANULARITY
        * REGISTER_ALLOCATION_GRANULARITY
    )
    register_limit = REGISTERS_PER_SM // (threads * allocated_registers)
    thread_limit = MAX_THREADS_PER_SM // threads
    shared_bytes = static_shared_bytes + dynamic_shared_bytes
    shared_limit = MAX_BLOCKS_PER_SM if shared_bytes == 0 else SHARED_MEMORY_PER_SM // shared_bytes
    blocks = min(MAX_BLOCKS_PER_SM, register_limit, thread_limit, shared_limit)
    return blocks, blocks * threads / MAX_THREADS_PER_SM


def ensure_no_forbidden_keys(value: Any) -> None:
    if isinstance(value, dict):
        bad = FORBIDDEN.intersection(value)
        if bad:
            raise ValueError(f"forbidden report keys: {sorted(bad)}")
        for child in value.values():
            ensure_no_forbidden_keys(child)
    elif isinstance(value, list):
        for child in value:
            ensure_no_forbidden_keys(child)


def comparison_specs() -> list[dict[str, Any]]:
    template = {"lineage": "template"}
    specs = []
    for encoding in (
        "compact_r0_port", "split_fixed_slot", "split_fixed_direct",
        "homogeneous_slot", "homogeneous_direct", "grouped_slot", "grouped_direct",
    ):
        specs.append({
            "label": f"encoding {encoding} versus current_fixed_slot (canonical ordinary)",
            "baseline": {
                **template, "encoding": "current_fixed_slot", "inner": "canonical",
                "outer": "canonical", "source_policy": "ordinary",
            },
            "candidate": {
                **template, "encoding": encoding, "inner": "canonical",
                "outer": "canonical", "source_policy": "ordinary",
            },
            "varying": ("encoding",),
        })
    for family in ("split_fixed", "homogeneous", "grouped"):
        specs.append({
            "label": f"encoding {family}_direct versus {family}_slot",
            "baseline": {**template, "encoding": f"{family}_slot"},
            "candidate": {**template, "encoding": f"{family}_direct"},
            "varying": ("encoding",),
        })
    for outer in ("u64", "u96"):
        specs.append({
            "label": f"whole-BF {outer} versus canonical outer accumulation",
            "baseline": {**template, "inner": "canonical", "outer": "canonical"},
            "candidate": {**template, "inner": "canonical", "outer": outer},
            "varying": ("outer",),
        })
    for outer in ("canonical", "u64", "u96"):
        specs.append({
            "label": f"inner-u64 versus canonical inner accumulation (outer={outer})",
            "baseline": {**template, "inner": "canonical", "outer": outer},
            "candidate": {**template, "inner": "u64", "outer": outer},
            "varying": ("inner",),
        })
    for capacity in (8, 16, 32):
        specs.append({
            "label": f"materialized cap{capacity} versus ordinary sources",
            "baseline": {**template, "source_policy": "ordinary", "tile_capacity": None},
            "candidate": {
                **template, "source_policy": "materialized", "tile_capacity": capacity,
            },
            "varying": ("source_policy", "tile_capacity"),
        })
        for geometry in ("cta288_pair", "cta96_partitioned", "cta96_x2_major"):
            specs.append({
                "label": (
                    f"materialized cap{capacity} versus ordinary sources "
                    f"(geometry={geometry})"
                ),
                "baseline": {
                    **template, "geometry": geometry, "source_policy": "ordinary",
                    "tile_capacity": None,
                },
                "candidate": {
                    **template, "geometry": geometry, "source_policy": "materialized",
                    "tile_capacity": capacity,
                },
                "varying": ("source_policy", "tile_capacity"),
            })
    for geometry in (
        "cta96_partitioned", "cta96_x0_major", "cta96_x1_major", "cta96_x2_major",
    ):
        specs.append({
            "label": f"geometry {geometry} versus cta288_pair (ordinary sources)",
            "baseline": {**template, "geometry": "cta288_pair", "source_policy": "ordinary"},
            "candidate": {**template, "geometry": geometry, "source_policy": "ordinary"},
            "varying": ("geometry",),
        })
    for capacity in (8, 16, 32):
        for geometry in ("cta96_partitioned", "cta96_x2_major"):
            specs.append({
                "label": (
                    f"geometry {geometry} versus cta288_pair "
                    f"(materialized cap{capacity})"
                ),
                "baseline": {
                    **template, "geometry": "cta288_pair", "source_policy": "materialized",
                    "tile_capacity": capacity,
                },
                "candidate": {
                    **template, "geometry": geometry, "source_policy": "materialized",
                    "tile_capacity": capacity,
                },
                "varying": ("geometry",),
            })
    return specs


def write_tsv(path: pathlib.Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError(f"cannot write empty TSV: {path}")
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=list(rows[0]), delimiter="\t", extrasaction="raise"
        )
        writer.writeheader()
        for row in rows:
            writer.writerow({
                key: json.dumps(value, sort_keys=True, separators=(",", ":"))
                if isinstance(value, (dict, list)) else value
                for key, value in row.items()
            })


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sectioned-rows")
    parser.add_argument("--sectioned-bindings")
    parser.add_argument("--sectioned-executable")
    parser.add_argument("--sectioned-screen-root")
    parser.add_argument("--sectioned-manifest")
    parser.add_argument("--sectioned-resources")
    parser.add_argument("--sectioned-opcodes")
    parser.add_argument("--current-baseline")
    parser.add_argument("--historical-add-sub-ms", type=float, default=10.454048)
    parser.add_argument("--screen", default=str(DEFAULT_SCREEN))
    parser.add_argument("--evidence-root", default=str(DEFAULT_EVIDENCE))
    parser.add_argument("--prototype-manifest", default=str(DEFAULT_PROTOTYPES))
    parser.add_argument("--capacity-artifact", default=str(DEFAULT_CAPACITY))
    parser.add_argument("--resource-table", default=str(DEFAULT_RESOURCES))
    parser.add_argument("--opcode-table", default=str(DEFAULT_OPCODES))
    parser.add_argument("--report-root", default=str(DEFAULT_REPORT))
    args = parser.parse_args()
    if args.sectioned_rows is not None:
        required = (
            args.sectioned_bindings,
            args.sectioned_executable,
            args.sectioned_screen_root,
            args.sectioned_manifest,
            args.sectioned_resources,
            args.sectioned_opcodes,
            args.current_baseline,
        )
        if any(value is None for value in required):
            parser.error("sectioned report mode requires all sectioned inputs and current baseline")
        return run_sectioned_report(args)
    screen_path = pathlib.Path(args.screen).resolve()
    evidence = pathlib.Path(args.evidence_root).resolve()
    prototype_path = pathlib.Path(args.prototype_manifest).resolve()
    resources = resource_rows(pathlib.Path(args.resource_table))
    opcodes = opcode_rows(pathlib.Path(args.opcode_table))
    capacity_path = pathlib.Path(args.capacity_artifact).resolve()
    capacity_artifact = load(capacity_path)
    capacity_coordinates = {
        (row["circuit"], row["layer"]): row
        for row in capacity_artifact["coordinates"]
    }
    report = pathlib.Path(args.report_root).resolve()
    report.mkdir(parents=True, exist_ok=True)
    screen = load(screen_path)
    prototypes = load(prototype_path)
    symbols = {row["candidate_id"]: row for row in prototypes["symbols"]}
    configurations = {row["configuration_id"]: row for row in prototypes["configurations"]}
    normalized = []
    for coordinate in screen["rows"]:
        directory = evidence / f"{coordinate['circuit']}--{coordinate['layer']}"
        bindings = directory / "bindings.json"; checkpoint = directory / "checkpoint.json"; rows_path = directory / "rows.jsonl"
        if not all(path.is_file() for path in (bindings, checkpoint, rows_path)):
            raise ValueError(f"missing screen evidence: {directory}")
        binding = load(bindings); state = load(checkpoint)
        schema_version = binding.get("version")
        if schema_version not in (1, 2) or state.get("version") != schema_version:
            raise ValueError(f"unsupported screen schema version: {directory}")
        if state.get("state") != "complete" or state.get("binding_sha256") != sha256(bindings) or state.get("rows_sha256") != sha256(rows_path):
            raise ValueError(f"screen checkpoint mismatch: {directory}")
        if binding.get("screen_sha256") != sha256(screen_path) or binding.get("prototype_manifest_sha256") != sha256(prototype_path):
            raise ValueError(f"screen binding hash mismatch: {directory}")
        raw = [json.loads(line) for line in rows_path.read_text().splitlines() if line]
        if schema_version == 2:
            controller_wall = state.get("controller_command_wall_seconds")
            if (type(controller_wall) not in (int, float) or not math.isfinite(controller_wall)
                    or controller_wall <= 0):
                raise ValueError(f"invalid controller command wall: {directory}")
            if not raw or state.get("runner_coordinate_work_seconds") != raw[0].get("coordinate_execution_wall_seconds"):
                raise ValueError(f"invalid runner work wall: {directory}")
            if state.get("device_identity") != raw[0].get("observation", {}).get("device_identity"):
                raise ValueError(f"screen checkpoint device mismatch: {directory}")
            if binding.get("device_identity") != validate_device_identity(state["device_identity"]):
                raise ValueError(f"screen binding device mismatch: {directory}")
            validate_execution(binding, state, directory)
        raw_ids = [row.get("observation", {}).get("configuration_id") for row in raw]
        if len(raw) != len(configurations) or set(raw_ids) != set(configurations) or len(raw_ids) != len(set(raw_ids)):
            raise ValueError(f"screen row cardinality mismatch: {directory}")
        if raw_ids != binding.get("configuration_ids"):
            raise ValueError(f"screen runtime configuration order mismatch: {directory}")
        for row in raw:
            observation = row["observation"]
            expected_key = (coordinate["circuit"], coordinate["layer"], coordinate["log_trace"], 0)
            observed_key = (observation.get("circuit"), observation.get("layer"), observation.get("log_trace"), observation.get("seed"))
            if observation.get("version") != schema_version or observed_key != expected_key:
                raise ValueError(f"screen row identity mismatch: {directory}")
            disposition = observation.get("launchability", {})
            if schema_version == 2:
                if validate_device_identity(observation.get("device_identity")) != state["device_identity"]:
                    raise ValueError(f"screen row device mismatch: {directory}")
                validate_launchability_identity(disposition, state["device_identity"])
            if "unlaunchable_capacity" in disposition:
                if observation.get("passing") or observation.get("failure") != "unlaunchable_capacity":
                    raise ValueError(f"invalid screen capacity row: {directory}")
                if (row.get("samples") or row.get("pilot_samples")
                        or row.get("pilot_median_ms") is not None or row.get("retained_samples") != 0):
                    raise ValueError(f"capacity row contains timing: {directory}")
                continue
            if "launchable" not in disposition or not observation.get("passing") or observation.get("failure") is not None:
                raise ValueError(f"failed launchable screen row: {directory}")
            checksum = cell_checksum(observation.get("cells"))
            checksum_values = {checksum, observation.get("checksum"), observation.get("expected_checksum")}
            if schema_version == 1:
                checksum_values.update((row.get("correctness_checksum"), row.get("post_session_checksum")))
            else:
                checksum_values.update((
                    row.get("pilot_correctness_checksum"), row.get("pilot_post_session_checksum"),
                    row.get("retained_correctness_checksum"), row.get("retained_post_session_checksum"),
                ))
            if None in checksum_values or len(checksum_values) != 1:
                raise ValueError(f"screen checksum mismatch: {directory}")
            retained = row.get("retained_samples")
            samples = row.get("samples")
            if type(retained) is not int or not 5 <= retained <= 50 or len(samples) != retained + 2:
                raise ValueError(f"screen sample cardinality mismatch: {directory}")
            if [sample.get("warmup") for sample in samples] != [True, True] + [False] * retained or any(type(sample.get("warmup")) is not bool for sample in samples):
                raise ValueError(f"screen warmup sequence mismatch: {directory}")
            if schema_version == 2:
                pilot_samples = row.get("pilot_samples")
                if (not isinstance(pilot_samples, list) or len(pilot_samples) != 5
                        or [sample.get("warmup") for sample in pilot_samples]
                        != [True, True, False, False, False]
                        or any(type(sample.get("warmup")) is not bool for sample in pilot_samples)):
                    raise ValueError(f"screen pilot sequence mismatch: {directory}")
                for wall in (
                    "candidate_wall_seconds", "coordinate_cpu_setup_seconds",
                    "coordinate_harness_setup_seconds", "reference_wall_seconds",
                    "coordinate_execution_wall_seconds",
                ):
                    value = row.get(wall)
                    if type(value) not in (int, float) or not math.isfinite(value) or value <= 0:
                        raise ValueError(f"invalid screen wall {wall}: {directory}")
                pilot_values = [sample["milliseconds"] for sample in pilot_samples if not sample["warmup"]]
                if statistics.median(pilot_values) != row.get("pilot_median_ms"):
                    raise ValueError(f"screen pilot median mismatch: {directory}")
                for phase_samples in (pilot_samples, samples):
                    expected_indices = [0, 1] + list(range(len(phase_samples) - 2))
                    if [sample.get("sample_index") for sample in phase_samples] != expected_indices:
                        raise ValueError(f"screen sample-index mismatch: {directory}")
                for phase_samples, phase, pass_index in (
                    (pilot_samples, "pilot", 0), (samples, "retained", 1)
                ):
                    position = phase_samples[0].get("pass_position")
                    if type(position) is not int or any(
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
                        raise ValueError(f"screen sample identity mismatch: {directory}")
            for sample in samples + (row.get("pilot_samples", []) if schema_version == 2 else []):
                duration = sample.get("milliseconds")
                if type(duration) not in (int, float) or not math.isfinite(duration) or duration <= 0:
                    raise ValueError(f"invalid screen duration: {directory}")
            pilot = row.get("pilot_median_ms")
            if type(pilot) not in (int, float) or not math.isfinite(pilot) or pilot <= 0:
                raise ValueError(f"invalid screen pilot: {directory}")
            expected_retained = min(50, max(5, math.ceil(100.0 / pilot)))
            if retained != expected_retained:
                raise ValueError(f"screen calibration mismatch: {directory}")
        if schema_version == 2:
            ordered = binding.get("configuration_ids")
            if not isinstance(ordered, list) or len(ordered) != len(configurations):
                raise ValueError(f"screen ordered configurations missing: {directory}")
            circuit_key = 0
            for byte in coordinate["circuit"].encode():
                circuit_key = (circuit_key * 131 + byte) & ((1 << 64) - 1)
            rotation = 0 if len(ordered) == 1 else (
                (circuit_key + coordinate["layer"]) % (len(ordered) - 1) + 1
            )
            retained_order = ordered[rotation:] + ordered[:rotation]
            observed_pilot = {
                row["observation"]["configuration_id"]: row["pilot_samples"][0]["pass_position"]
                for row in raw if row.get("pilot_samples")
            }
            observed_retained = {
                row["observation"]["configuration_id"]: row["samples"][0]["pass_position"]
                for row in raw if row.get("samples")
            }
            launchable_ids = set(observed_pilot)
            expected_pilot = {
                configuration_id: index for index, configuration_id in enumerate(ordered)
                if configuration_id in launchable_ids
            }
            expected_retained = {
                configuration_id: index for index, configuration_id in enumerate(retained_order)
                if configuration_id in launchable_ids
            }
            if observed_pilot != expected_pilot or observed_retained != expected_retained:
                raise ValueError(f"screen deterministic pass order mismatch: {directory}")
        medians = {row["observation"]["configuration_id"]: measured_median(row) for row in raw}
        for row in raw:
            observation = row["observation"]
            configuration_id = observation["configuration_id"]
            configuration = configurations[configuration_id]
            symbol = symbols[configuration["candidate_id"]]
            geometry = symbol["geometry"]
            reference_id = f"r0pb/current_fixed_slot/canonical/canonical/{geometry}/ordinary/reference"
            template_id = f"r0pb/current_fixed_slot/canonical/canonical/{geometry}/ordinary/template"
            median = medians[configuration_id]
            static = resources.get(symbol["symbol"])
            if static is None:
                raise ValueError(f"missing static resource row: {symbol['symbol']}")
            opcode = opcodes.get(symbol["symbol"])
            if opcode is None:
                raise ValueError(f"missing opcode row: {symbol['symbol']}")
            capacity_coordinate = capacity_coordinates[
                (coordinate["circuit"], coordinate["layer"])
            ]
            tile_capacity = configuration["tile_capacity"]
            capacity = capacity_fields(
                capacity_coordinate, symbol["encoding"], tile_capacity
            )
            descriptor_capacity = None if tile_capacity is None else f"c{tile_capacity}"
            descriptor_facts = [
                descriptor for descriptor in capacity_coordinate["descriptors"]
                if descriptor["encoding"] == symbol["encoding"]
                and descriptor["tile_capacity"] == descriptor_capacity
            ]
            if len(descriptor_facts) != 1:
                raise ValueError(f"descriptor fact join mismatch: {configuration_id}")
            descriptor_fact = descriptor_facts[0]
            if (
                observation["descriptor_bytes"] != descriptor_fact["payload_size"]
                or observation["program_sha256"] != capacity["capacity_program_sha256"]
                or observation["tile_sha256"] != capacity["capacity_tile_sha256"]
            ):
                raise ValueError(
                    f"screen capacity/descriptor binding mismatch: {configuration_id}"
                )
            active_blocks, occupancy = inferred_residency(
                registers=static["registers"],
                static_shared_bytes=static["static_shared_bytes"],
                dynamic_shared_bytes=capacity["max_dynamic_shared_bytes"],
                geometry=geometry,
            )
            normalized.append({
                "version": schema_version, "circuit": coordinate["circuit"], "layer": coordinate["layer"],
                "log_trace": coordinate["log_trace"], "configuration_id": configuration_id,
                "candidate_id": symbol["candidate_id"], "encoding": symbol["encoding"],
                "inner": symbol["inner"], "outer": symbol["outer"], "geometry": geometry,
                "lineage": symbol["lineage"], "source_policy": symbol["source_policy"],
                "tile_capacity": tile_capacity,
                "launchability": observation["launchability"], "median_ms": median,
                "candidate_minus_reference_percent_positive_is_slower": percent(median, medians.get(reference_id)),
                "candidate_minus_current_template_percent_positive_is_slower": percent(median, medians.get(template_id)),
                "pilot_median_ms": row["pilot_median_ms"], "retained_samples": row["retained_samples"],
                "candidate_wall_seconds": row["candidate_wall_seconds"],
                "coordinate_cpu_setup_seconds": row.get("coordinate_cpu_setup_seconds"),
                "coordinate_harness_setup_seconds": row.get("coordinate_harness_setup_seconds"),
                "reference_wall_seconds": row.get("reference_wall_seconds"),
                "coordinate_execution_wall_seconds": row.get("coordinate_execution_wall_seconds"),
                "controller_command_wall_seconds": state.get("controller_command_wall_seconds"),
                "runner_coordinate_work_seconds": state.get("runner_coordinate_work_seconds"),
                "device_identity": observation.get("device_identity"),
                "descriptor_bytes": observation["descriptor_bytes"], "program_sha256": observation["program_sha256"],
                "tile_sha256": observation["tile_sha256"], "requested_bytes": coordinate["requested_bytes"],
                "terms": coordinate["terms"], "source_uses": coordinate["source_uses"],
                "unique_sources": coordinate["unique_sources"], "max_source_reuse": coordinate["max_source_reuse"],
                "long_reuse_distance": coordinate["long_reuse_distance"], "weights": coordinate["weights"],
                "inferred_active_blocks_per_sm": active_blocks,
                "inferred_occupancy": occupancy,
                "has_static_spill_or_local_traffic": (
                    static["stack_bytes"] > 0 or static["local_bytes"] > 0
                    or opcode["opcode_ldl"] > 0 or opcode["opcode_stl"] > 0
                ),
                **capacity, **static, **opcode,
            })
    ensure_no_forbidden_keys(normalized)
    jsonl = report / "prototype-screen-normalized.jsonl"
    jsonl.write_text("".join(json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n" for row in normalized))
    write_tsv(report / "prototype-screen-normalized.tsv", normalized)

    specs = comparison_specs()
    summaries = [
        paired_factor_summary(
            normalized, label=spec["label"], baseline=spec["baseline"],
            candidate=spec["candidate"], varying=spec["varying"],
        )
        for spec in specs
    ]
    by_coordinate = []
    for coordinate in screen["rows"]:
        coordinate_rows = [
            row for row in normalized
            if row["circuit"] == coordinate["circuit"]
            and row["layer"] == coordinate["layer"]
        ]
        for spec in specs:
            try:
                summary = paired_factor_summary(
                    coordinate_rows, label=spec["label"], baseline=spec["baseline"],
                    candidate=spec["candidate"], varying=spec["varying"],
                )
            except ValueError as error:
                if "has no pairs" not in str(error):
                    raise
                continue
            by_coordinate.append({
                "circuit": coordinate["circuit"], "layer": coordinate["layer"], **summary,
            })
    ensure_no_forbidden_keys(summaries)
    ensure_no_forbidden_keys(by_coordinate)
    (report / "prototype-screen-factor-summaries.json").write_text(
        json.dumps(
            {"version": 1, "rows": summaries}, sort_keys=True, separators=(",", ":")
        ) + "\n"
    )
    write_tsv(report / "prototype-screen-factor-summaries.tsv", summaries)
    write_tsv(report / "prototype-screen-factor-by-coordinate.tsv", by_coordinate)

    pareto_columns = (
        "circuit", "layer", "configuration_id", "encoding", "inner", "outer",
        "geometry", "source_policy", "tile_capacity", "median_ms", "registers",
        "stack_bytes", "local_bytes", "max_dynamic_shared_bytes",
        "inferred_active_blocks_per_sm", "inferred_occupancy", "descriptor_bytes",
        "logical_program_and_slots_bytes", "compact_escape_words",
        "compact_weighted_escape_source_uses", "weights",
    )
    pareto_inputs = [
        {key: row[key] for key in pareto_columns}
        for row in normalized if row["median_ms"] is not None
    ]
    ensure_no_forbidden_keys(pareto_inputs)
    write_tsv(report / "prototype-screen-pareto-inputs.tsv", pareto_inputs)
    grouped: dict[tuple[str, int, str], list[float]] = defaultdict(list)
    for row in normalized:
        if row["median_ms"] is not None:
            grouped[(row["circuit"], row["layer"], row["encoding"])].append(row["median_ms"])
    markdown = [
        "# R0 prototype production screen", "",
        "Percent columns use `(candidate / exact baseline - 1) × 100`: positive is slower; negative is faster.", "",
        "This is descriptive evidence only. It contains no automatic implementation disposition.", "",
        "## Controlled paired factor effects", "",
        "Each row changes only the named factor(s). Percentages use the convention above.", "",
        "| comparison | pairs | median % | p10 % | p90 % | faster/equal/slower |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for summary in summaries:
        markdown.append(
            f"| {summary['comparison']} | {summary['pairs']} | "
            f"{summary['median_percent_positive_is_slower']:+.3f} | "
            f"{summary['p10_percent_positive_is_slower']:+.3f} | "
            f"{summary['p90_percent_positive_is_slower']:+.3f} | "
            f"{summary['candidate_faster_pairs']}/{summary['equal_pairs']}/"
            f"{summary['candidate_slower_pairs']} |"
        )
    markdown.extend([
        "", "Per-coordinate controlled effects are in `prototype-screen-factor-by-coordinate.tsv`.",
        "Launchable Pareto inputs are in `prototype-screen-pareto-inputs.tsv`.", "",
        "## Absolute encoding medians", "",
        "| circuit:layer | encoding | launchable configuration median-of-medians (ms) |", "|---|---:|---:|",
    ])
    for (circuit, layer, encoding), values in sorted(grouped.items()):
        markdown.append(f"| {circuit}:{layer} | {encoding} | {statistics.median(values):.6f} |")
    markdown.extend([
        "", f"Raw normalized rows: {len(normalized)}.",
        f"Launchable Pareto-input rows: {len(pareto_inputs)}.",
        "Whole-coordinate setup/lock wall time was not timestamped in the immutable v1 schema; "
        "`candidate_wall_seconds` is retained for every configuration and no GPU work was rerun.", "",
    ])
    (report / "prototype-screen.md").write_text("\n".join(markdown))
    output_names = (
        "prototype-screen-normalized.jsonl", "prototype-screen-normalized.tsv",
        "prototype-screen-factor-summaries.json", "prototype-screen-factor-summaries.tsv",
        "prototype-screen-factor-by-coordinate.tsv", "prototype-screen-pareto-inputs.tsv",
        "prototype-screen.md",
    )
    hashes = {
        "version": 1, "rows": len(normalized), "coordinates": len(screen["rows"]),
        "inputs": {
            "screen_sha256": sha256(screen_path),
            "prototype_manifest_sha256": sha256(prototype_path),
            "capacity_artifact_sha256": sha256(capacity_path),
            "resource_table_sha256": sha256(pathlib.Path(args.resource_table)),
            "opcode_table_sha256": sha256(pathlib.Path(args.opcode_table)),
        },
        "outputs": {name: sha256(report / name) for name in output_names},
    }
    (report / "prototype-screen-hashes.json").write_text(json.dumps(hashes, sort_keys=True, separators=(",", ":")) + "\n")
    print(f"WINDOWED_R0_PROTOTYPE_SCREEN_OK rows={len(normalized)} coordinates={len(screen['rows'])}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
