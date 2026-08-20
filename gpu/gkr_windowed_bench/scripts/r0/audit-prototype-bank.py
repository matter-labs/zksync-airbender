#!/usr/bin/env python3
"""Strict audit for R0 prototype-bank evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[4]
DEFAULT_CORPUS = ROOT / "gpu/gkr_windowed_bench/artifacts/windowed_r0_corpus_v1.json"
DEFAULT_PROTOTYPES = ROOT / "gpu/gkr_windowed_bench/artifacts/windowed_r0_prototype_manifest_v1.json"
DEFAULT_OUTPUT = ROOT / "target/windowed-gkr-r0-prototype-bank/correctness/campaign-v3"
DEFAULT_SANITIZER_COVER = ROOT / "target/windowed-gkr-r0-prototype-bank/sanitizer/cover.json"
DEFAULT_SANITIZER_OUTPUT = ROOT / "target/windowed-gkr-r0-prototype-bank/sanitizer/campaign-v3"


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> Any:
    return json.loads(path.read_text())


def cell_checksum(cells: list[dict[str, Any]]) -> str:
    payload = bytearray()
    if len(cells) != 27:
        raise ValueError("cell cardinality must be 27")
    for cell in cells:
        limbs = cell.get("limbs")
        if not isinstance(limbs, list) or len(limbs) != 4:
            raise ValueError("each cell must contain four limbs")
        for limb in limbs:
            if type(limb) is not int or not 0 <= limb < 2**32:
                raise ValueError("invalid cell limb")
            payload += limb.to_bytes(4, "little")
    return hashlib.sha256(payload).hexdigest()


def validate_device_identity(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError("missing device identity")
    integer_fields = (
        "cuda_device_index", "compute_capability_major", "compute_capability_minor",
        "cuda_driver_version", "cuda_runtime_version", "default_shared_memory_bytes",
        "opt_in_shared_memory_bytes",
    )
    if any(type(value.get(field)) is not int or value[field] < 0 for field in integer_fields):
        raise ValueError("invalid numeric device identity")
    if any(not isinstance(value.get(field), str) or not value[field] for field in (
        "uuid", "name", "cuda_toolkit_version",
    )):
        raise ValueError("invalid textual device identity")
    clock = value.get("clock_policy")
    if not isinstance(clock, dict) or clock.get("uuid", "").lower() != value["uuid"].lower() \
            or clock.get("name") != value["name"] or not clock.get("raw_query"):
        raise ValueError("invalid clock-policy identity")
    if value["default_shared_memory_bytes"] > value["opt_in_shared_memory_bytes"]:
        raise ValueError("default shared-memory limit exceeds opt-in limit")
    return value


def validate_launchability_identity(value: Any, identity: dict[str, Any]) -> None:
    if not isinstance(value, dict) or len(value) != 1:
        raise ValueError("malformed launchability")
    default = identity["default_shared_memory_bytes"]
    limit = identity["opt_in_shared_memory_bytes"]
    if "launchable" in value:
        fact = value["launchable"]
        required = fact.get("dynamic_shared_bytes") if isinstance(fact, dict) else None
        opt_in = fact.get("opt_in") if isinstance(fact, dict) else None
        if type(required) is not int or type(opt_in) is not bool or required < 0:
            raise ValueError("malformed launchable fact")
        if (not opt_in and required > default) or (opt_in and not default < required <= limit):
            raise ValueError("launchable fact contradicts device capacity")
    elif "unlaunchable_capacity" in value:
        fact = value["unlaunchable_capacity"]
        required = fact.get("required_bytes") if isinstance(fact, dict) else None
        observed_limit = fact.get("device_limit_bytes") if isinstance(fact, dict) else None
        if type(required) is not int or type(observed_limit) is not int \
                or required <= limit or observed_limit != limit:
            raise ValueError("unlaunchable fact contradicts device capacity")
    else:
        raise ValueError("unknown launchability")


def validate_execution(binding: dict[str, Any], checkpoint: dict[str, Any], directory: pathlib.Path) -> None:
    execution = binding.get("execution")
    if not isinstance(execution, dict) or not isinstance(execution.get("command"), list):
        raise ValueError(f"missing execution binding at {directory}")
    lock = execution.get("gpu_lock")
    if not isinstance(lock, dict) or lock.get("mode") not in ("none", "repository_file_lock"):
        raise ValueError(f"invalid lock binding at {directory}")
    if lock["mode"] == "repository_file_lock":
        path = pathlib.Path(lock.get("path", ""))
        if not path.is_file() or sha256(path) != lock.get("sha256") \
                or execution["command"][:1] != [str(path)]:
            raise ValueError(f"GPU-lock binding mismatch at {directory}")
    elif lock.get("path") is not None or lock.get("sha256") is not None:
        raise ValueError(f"unlocked binding contains a lock path at {directory}")
    driver = directory / "driver.log"
    if not driver.is_file() or checkpoint.get("driver_sha256") != sha256(driver):
        raise ValueError(f"driver hash mismatch at {directory}")
    text = driver.read_text(errors="replace")
    markers = (
        "[with_gpu_lock] waiting for GPU lock:",
        "[with_gpu_lock] acquired GPU lock:",
        "[with_gpu_lock] releasing GPU lock:",
    )
    if lock["mode"] == "repository_file_lock":
        if any(text.count(marker) != 1 for marker in markers) \
                or "status=0" not in next(line for line in text.splitlines() if markers[2] in line):
            raise ValueError(f"GPU-lock lifecycle mismatch at {directory}")
    elif any(marker in text for marker in markers):
        raise ValueError(f"unlocked evidence contains GPU-lock lifecycle at {directory}")


def correctness(args: argparse.Namespace) -> int:
    corpus = pathlib.Path(args.corpus_manifest).resolve()
    prototypes = pathlib.Path(args.prototype_manifest).resolve()
    output = pathlib.Path(args.output_root).resolve()
    coordinates = load(corpus).get("coordinates", [])
    configurations = load(prototypes).get("configurations", [])
    expected_configs = {row["configuration_id"] for row in configurations}
    logs = [int(value) for value in args.logs.split(",") if value]
    expected_keys = {
        (coordinate["circuit"], coordinate["layer"], log_trace, config)
        for coordinate in coordinates
        for log_trace in logs
        for config in expected_configs
    }
    observed_keys: set[tuple[str, int, int, str]] = set()
    launchable = unlaunchable = 0
    for coordinate in coordinates:
        for log_trace in logs:
            directory = output / f"log{log_trace}" / f"{coordinate['circuit']}--{coordinate['layer']}"
            bindings_path = directory / "bindings.json"
            checkpoint_path = directory / "checkpoint.json"
            rows_path = directory / "rows.jsonl"
            if not all(path.is_file() for path in (bindings_path, checkpoint_path, rows_path)):
                raise ValueError(f"missing evidence at {directory}")
            binding = load(bindings_path)
            checkpoint = load(checkpoint_path)
            schema_version = binding.get("version")
            if schema_version not in (1, 2) or binding.get("mode") != "correctness":
                raise ValueError(f"invalid binding at {directory}")
            if binding.get("coordinate") != {
                "circuit": coordinate["circuit"], "layer": coordinate["layer"]
            } or binding.get("log_trace") != log_trace:
                raise ValueError(f"binding key mismatch at {directory}")
            if set(binding.get("configuration_ids", [])) != expected_configs:
                raise ValueError(f"binding configuration mismatch at {directory}")
            bound_paths = [
                ("runner", "runner_sha256"),
                ("corpus_manifest", "corpus_manifest_sha256"),
                ("prototype_manifest", "prototype_manifest_sha256"),
            ]
            if schema_version == 2:
                bound_paths.append(("corpus", "corpus_sha256"))
            for path_key, hash_key in bound_paths:
                path = pathlib.Path(binding[path_key])
                if not path.is_file() or sha256(path) != binding[hash_key]:
                    raise ValueError(f"binding hash mismatch {path_key} at {directory}")
            expected_checkpoint = {
                "version": schema_version,
                "state": "complete",
                "binding_sha256": sha256(bindings_path),
                "rows_sha256": sha256(rows_path),
                "rows": len(expected_configs),
                "launchable": checkpoint.get("launchable"),
                "unlaunchable_capacity": checkpoint.get("unlaunchable_capacity"),
            }
            if schema_version == 2:
                expected_checkpoint.update({
                    "device_identity": checkpoint.get("device_identity"),
                    "controller_command_wall_seconds": checkpoint.get("controller_command_wall_seconds"),
                    "driver_sha256": checkpoint.get("driver_sha256"),
                })
            if checkpoint != expected_checkpoint:
                raise ValueError(f"checkpoint mismatch at {directory}")
            if schema_version == 2:
                identity = validate_device_identity(checkpoint["device_identity"])
                if binding.get("device_identity") != identity:
                    raise ValueError(f"binding device identity mismatch at {directory}")
                wall = checkpoint["controller_command_wall_seconds"]
                if type(wall) not in (int, float) or wall <= 0:
                    raise ValueError(f"invalid controller-command wall at {directory}")
                validate_execution(binding, checkpoint, directory)
            rows = [json.loads(line) for line in rows_path.read_text().splitlines() if line]
            if len(rows) != len(expected_configs):
                raise ValueError(f"row cardinality mismatch at {directory}")
            if [row.get("configuration_id") for row in rows] != binding["configuration_ids"]:
                raise ValueError(f"runtime configuration order mismatch at {directory}")
            for row in rows:
                key = (row.get("circuit"), row.get("layer"), row.get("log_trace"), row.get("configuration_id"))
                if key in observed_keys or key not in expected_keys or row.get("version") != schema_version:
                    raise ValueError(f"unexpected/duplicate key {key}")
                if (schema_version == 2
                        and validate_device_identity(row.get("device_identity")) != checkpoint["device_identity"]):
                    raise ValueError(f"device identity mismatch {key}")
                observed_keys.add(key)
                if row.get("seed") != binding.get("seed"):
                    raise ValueError(f"seed mismatch {key}")
                disposition = row.get("launchability", {})
                if schema_version == 2:
                    validate_launchability_identity(disposition, checkpoint["device_identity"])
                if "unlaunchable_capacity" in disposition:
                    unlaunchable += 1
                    if row.get("passing") or row.get("failure") != "unlaunchable_capacity":
                        raise ValueError(f"invalid capacity fact {key}")
                    if any(row.get(name) is not None for name in ("launch", "cells", "checksum")):
                        raise ValueError(f"unlaunchable row contains launch output {key}")
                elif "launchable" in disposition:
                    launchable += 1
                    if not row.get("passing") or row.get("failure") is not None:
                        raise ValueError(f"failed launchable row {key}")
                    checksum = cell_checksum(row.get("cells"))
                    if checksum != row.get("checksum") or checksum != row.get("expected_checksum"):
                        raise ValueError(f"cell/checksum mismatch {key}")
                    launch = row.get("launch")
                    if not isinstance(launch, dict) or not launch.get("symbol"):
                        raise ValueError(f"missing launch metadata {key}")
                else:
                    raise ValueError(f"unknown launchability {key}")
            if checkpoint["launchable"] + checkpoint["unlaunchable_capacity"] != len(rows):
                raise ValueError(f"checkpoint disposition counts mismatch at {directory}")
    if observed_keys != expected_keys:
        raise ValueError(f"global coverage mismatch expected={len(expected_keys)} observed={len(observed_keys)}")
    print(
        f"WINDOWED_R0_PROTOTYPE_CORRECTNESS_OK rows={len(observed_keys)} launchable={launchable} unlaunchable_capacity={unlaunchable}"
    )
    return 0


def sanitizer(args: argparse.Namespace) -> int:
    cover_path = pathlib.Path(args.cover).resolve()
    output = pathlib.Path(args.output_root).resolve()
    cover = load(cover_path)
    if cover.get("universe") != cover.get("covered"):
        raise ValueError("sanitizer cover is incomplete")
    expected = {
        (row["configuration_id"], tool): row
        for row in cover["rows"]
        for tool in row["tools"]
    }
    observed = set()
    for (configuration_id, tool), cover_row in expected.items():
        directory = output / configuration_id.replace("/", "--") / tool
        bindings_path = directory / "bindings.json"
        checkpoint_path = directory / "checkpoint.json"
        rows_path = directory / "rows.jsonl"
        sanitizer_path = directory / "sanitizer.log"
        driver_path = directory / "driver.log"
        if not all(path.is_file() for path in (bindings_path, checkpoint_path, rows_path, sanitizer_path, driver_path)):
            raise ValueError(f"missing sanitizer evidence: {directory}")
        binding = load(bindings_path)
        checkpoint = load(checkpoint_path)
        schema_version = binding.get("version")
        if schema_version not in (1, 2) or binding.get("configuration_id") != configuration_id or binding.get("tool") != tool:
            raise ValueError(f"sanitizer binding mismatch: {directory}")
        if binding.get("symbol") != cover_row["symbol"] or binding.get("candidate_id") != cover_row["candidate_id"]:
            raise ValueError(f"sanitizer symbol mismatch: {directory}")
        if sha256(pathlib.Path(binding["runner"])) != binding.get("runner_sha256"):
            raise ValueError(f"sanitizer runner hash mismatch: {directory}")
        if schema_version == 2 and sha256(pathlib.Path(binding["corpus"])) != binding.get("corpus_sha256"):
            raise ValueError(f"sanitizer corpus hash mismatch: {directory}")
        if sha256(pathlib.Path(binding["cover"])) != binding.get("cover_sha256") or binding.get("cover_sha256") != sha256(cover_path):
            raise ValueError(f"sanitizer cover hash mismatch: {directory}")
        command = binding.get("command")
        if not isinstance(command, list) or "compute-sanitizer" not in command or f"kernel_name={cover_row['symbol']}" not in command:
            raise ValueError(f"sanitizer command provenance mismatch: {directory}")
        expected_checkpoint = {
            "version": schema_version,
            "state": "complete",
            "binding_sha256": sha256(bindings_path),
            "rows_sha256": sha256(rows_path),
            "sanitizer_sha256": sha256(sanitizer_path),
        }
        if schema_version == 2:
            expected_checkpoint.update({
                "device_identity": checkpoint.get("device_identity"),
                "controller_command_wall_seconds": checkpoint.get("controller_command_wall_seconds"),
                "driver_sha256": checkpoint.get("driver_sha256"),
            })
            identity = validate_device_identity(checkpoint.get("device_identity"))
            if binding.get("device_identity") != identity:
                raise ValueError(f"sanitizer binding device mismatch: {directory}")
            if type(checkpoint.get("controller_command_wall_seconds")) not in (int, float) \
                    or checkpoint["controller_command_wall_seconds"] <= 0:
                raise ValueError(f"sanitizer wall mismatch: {directory}")
            validate_execution(binding, checkpoint, directory)
        if checkpoint != expected_checkpoint:
            raise ValueError(f"sanitizer checkpoint mismatch: {directory}")
        rows = [json.loads(line) for line in rows_path.read_text().splitlines() if line]
        if (len(rows) != 1 or rows[0].get("version") != schema_version
                or rows[0].get("configuration_id") != configuration_id or not rows[0].get("passing")):
            raise ValueError(f"sanitizer correctness row mismatch: {directory}")
        if schema_version == 2:
            if validate_device_identity(rows[0].get("device_identity")) != checkpoint["device_identity"]:
                raise ValueError(f"sanitizer device mismatch: {directory}")
            validate_launchability_identity(rows[0].get("launchability"), checkpoint["device_identity"])
        checksum = cell_checksum(rows[0].get("cells"))
        if checksum != rows[0].get("checksum") or checksum != rows[0].get("expected_checksum"):
            raise ValueError(f"sanitizer checksum mismatch: {directory}")
        summary = "ERROR SUMMARY: 0 errors" if tool == "memcheck" else "RACECHECK SUMMARY: 0 hazards displayed (0 errors, 0 warnings)"
        if sanitizer_path.read_text().count(summary) != 1:
            raise ValueError(f"sanitizer summary mismatch: {directory}")
        if schema_version == 1:
            driver = driver_path.read_text()
            if driver.count("[with_gpu_lock] acquired GPU lock:") != 1 or driver.count("[with_gpu_lock] releasing GPU lock:") != 1 or "status=0" not in driver:
                raise ValueError(f"sanitizer lock lifecycle mismatch: {directory}")
        observed.add((configuration_id, tool))
    if observed != set(expected):
        raise ValueError("sanitizer coverage mismatch")
    print(f"WINDOWED_R0_PROTOTYPE_SANITIZER_OK sessions={len(observed)} factors={len(cover['covered'])}")
    return 0


def parser() -> argparse.ArgumentParser:
    top = argparse.ArgumentParser()
    sub = top.add_subparsers(dest="command", required=True)
    audit = sub.add_parser("correctness")
    audit.add_argument("--corpus-manifest", default=str(DEFAULT_CORPUS))
    audit.add_argument("--prototype-manifest", default=str(DEFAULT_PROTOTYPES))
    audit.add_argument("--output-root", default=str(DEFAULT_OUTPUT))
    audit.add_argument("--logs", default="3,12")
    sanitizers = sub.add_parser("sanitizer")
    sanitizers.add_argument("--cover", default=str(DEFAULT_SANITIZER_COVER))
    sanitizers.add_argument("--output-root", default=str(DEFAULT_SANITIZER_OUTPUT))
    return top


if __name__ == "__main__":
    try:
        parsed = parser().parse_args()
        raise SystemExit(correctness(parsed) if parsed.command == "correctness" else sanitizer(parsed))
    except Exception as error:
        print(f"prototype audit error: {error}", file=sys.stderr)
        raise SystemExit(1)
