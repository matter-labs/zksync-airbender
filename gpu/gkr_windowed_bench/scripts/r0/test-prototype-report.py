#!/usr/bin/env python3
"""Focused behavior tests for the descriptive prototype-screen report."""

from __future__ import annotations

import importlib.util
import pathlib
import copy
import json
import tempfile


SCRIPT = pathlib.Path(__file__).with_name("report-prototype-screen.py")
SPEC = importlib.util.spec_from_file_location("prototype_screen_report", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
REPORT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REPORT)


def row(case: str, encoding: str, milliseconds: float) -> dict[str, object]:
    return {
        "circuit": case,
        "layer": 0,
        "encoding": encoding,
        "inner": "canonical",
        "outer": "canonical",
        "geometry": "cta288_pair",
        "source_policy": "ordinary",
        "tile_capacity": None,
        "lineage": "template",
        "median_ms": milliseconds,
    }


def test_controlled_pair_summary() -> None:
    rows = [
        row("a", "current_fixed_slot", 10.0),
        row("a", "split_fixed_slot", 9.0),
        row("b", "current_fixed_slot", 10.0),
        row("b", "split_fixed_slot", 10.0),
        row("c", "current_fixed_slot", 10.0),
        row("c", "split_fixed_slot", 12.0),
    ]
    summary = REPORT.paired_factor_summary(
        rows,
        label="split versus current",
        baseline={"encoding": "current_fixed_slot"},
        candidate={"encoding": "split_fixed_slot"},
        varying=("encoding",),
    )
    assert summary == {
        "comparison": "split versus current",
        "pairs": 3,
        "median_percent_positive_is_slower": 0.0,
        "p10_percent_positive_is_slower": -10.0,
        "p90_percent_positive_is_slower": 20.0,
        "candidate_faster_pairs": 1,
        "equal_pairs": 1,
        "candidate_slower_pairs": 1,
    }


def test_capacity_and_residency_join() -> None:
    coordinate = {
        "compact": {"escape_words": 7, "weighted_escape_source_uses": 19},
        "encodings": [
            {
                "encoding": "compact_r0_port",
                "semantic_records": 11,
                "represented_records": 11,
                "bf_records": 9,
                "e4_records": 2,
                "group_headers": 0,
                "logical_program_u16_words": 23,
                "source_slot_u16_words": 5,
                "model_json_bytes": 101,
            }
        ],
        "descriptors": [
            {
                "encoding": "compact_r0_port",
                "tile_capacity": "c8",
                "payload_size": 26944,
                "max_dynamic_shared_bytes": 32768,
                "program_sha256": "program",
                "tile_sha256": "tile",
            }
        ],
    }
    fields = REPORT.capacity_fields(coordinate, "compact_r0_port", 8)
    assert fields == {
        "semantic_records": 11,
        "represented_records": 11,
        "bf_records": 9,
        "e4_records": 2,
        "group_headers": 0,
        "logical_program_u16_words": 23,
        "source_slot_u16_words": 5,
        "logical_program_and_slots_bytes": 56,
        "model_json_bytes": 101,
        "compact_escape_words": 7,
        "compact_weighted_escape_source_uses": 19,
        "max_dynamic_shared_bytes": 32768,
        "capacity_program_sha256": "program",
        "capacity_tile_sha256": "tile",
    }
    blocks, occupancy = REPORT.inferred_residency(
        registers=63,
        static_shared_bytes=1024,
        dynamic_shared_bytes=32768,
        geometry="cta288_pair",
    )
    assert blocks == 3
    assert occupancy == 0.5625


def test_default_static_tables_are_bound_to_the_final_campaign() -> None:
    expected = pathlib.Path(
        "target/windowed-gkr-r0-prototype-bank/report/final-static"
    )
    assert REPORT.DEFAULT_RESOURCES.relative_to(REPORT.ROOT).parent == expected
    assert REPORT.DEFAULT_OPCODES.relative_to(REPORT.ROOT).parent == expected


def sectioned_manifest() -> dict[str, object]:
    bounds = [None, 7, 8, 9, 10, 12, 16]
    rows = [{"candidate_id": "sectioned/shape433/wide9-b3",
             "symbol": "kernel_wide9_b3", "shape_bits": 433,
             "geometry": "wide9", "min_blocks": 3}]
    for geometry in ("split3", "serial3_low"):
        for bound in bounds:
            tag = "natural" if bound is None else f"b{bound}"
            rows.append({"candidate_id": f"sectioned/shape433/{geometry}-{tag}",
                         "symbol": f"kernel_{geometry}_{tag}", "shape_bits": 433,
                         "geometry": geometry, "min_blocks": bound})
    return {"symbols": rows}


def fixture_device() -> dict[str, object]:
    return {"cuda_device_index": 0, "uuid": "GPU-fixture", "name": "fixture",
            "compute_capability_major": 10, "compute_capability_minor": 0,
            "cuda_driver_version": 12090, "cuda_runtime_version": 12080,
            "cuda_toolkit_version": "12.8", "default_shared_memory_bytes": 49152,
            "opt_in_shared_memory_bytes": 232448,
            "clock_policy": {"raw_query": "fixture", "uuid": "GPU-fixture",
                             "name": "fixture"}}


def sectioned_rows() -> tuple[list[dict[str, object]], dict[str, object], str]:
    manifest = sectioned_manifest(); manifest_sha = "m" * 64
    domain = manifest["symbols"]
    arms = [("generic", {"candidate_id": "generic/reference", "symbol": "kernel_generic",
                         "geometry": "cta288_pair", "min_blocks": None, "shape_bits": None})]
    arms += [("sectioned", symbol) for symbol in domain]
    cells = [{"limbs": [index, index + 1, index + 2, index + 3]} for index in range(27)]
    checksum = REPORT.cell_checksum(cells)
    device = fixture_device(); rows = []
    coordinate_key = "add_sub_lui_auipc_mop:0"
    for arm_position, (kind, symbol) in enumerate(arms):
        milliseconds = 10.0 + arm_position / 10
        observation = {"version": 2, "configuration_id": symbol["candidate_id"],
            "candidate_id": symbol["candidate_id"], "circuit": "add_sub_lui_auipc_mop",
            "layer": 0, "log_trace": 24, "seed": 0, "input_sha256": "i"*64,
            "program_sha256": "p"*64, "tile_sha256": None, "descriptor_bytes": 17536,
            "launchability": {"launchable": {"dynamic_shared_bytes": 0, "opt_in": False}},
            "launch": {"symbol": symbol["symbol"], "grid": [1,1,1], "block": [96,1,1]},
            "cells": cells, "checksum": checksum, "expected_checksum": checksum,
            "passing": True, "failure": None, "device_identity": device}
        common = {"version": 2, "configuration_id": symbol["candidate_id"],
            "circuit": observation["circuit"], "layer": 0, "log_trace": 24, "seed": 0,
            "symbol": symbol["symbol"], "min_blocks": symbol["min_blocks"],
            "compiled_shape_bits": symbol["shape_bits"], "manifest_sha256": manifest_sha,
            "executable_sha256": "e"*64, "input_sha256": "i"*64,
            "program_sha256": "p"*64, "device_identity": device,
            "warmup": False}
        pilot = [{**common, "phase": "pilot", "pass_index": 0,
                  "pass_position": arm_position, "round_index": 0, "chunk": "pilot",
                  "sample_index": index, "milliseconds": milliseconds + index / 100}
                 for index in range(3)]
        retained = []
        if kind == "generic":
            for round_index in range(5):
                for chunk, position in (("reference_before", 0), ("reference_after", 16)):
                    retained += [{**common, "phase": "retained", "pass_index": round_index,
                        "pass_position": position, "round_index": round_index, "chunk": chunk,
                        "sample_index": index, "milliseconds": milliseconds + index / 100}
                        for index in range(5)]
        else:
            candidate_index = domain.index(symbol)
            for round_index in range(5):
                position = REPORT.sectioned_round_order(coordinate_key, round_index).index(candidate_index)+1
                retained += [{**common, "phase": "retained", "pass_index": round_index,
                    "pass_position": position, "round_index": round_index, "chunk": "candidate",
                    "sample_index": index, "milliseconds": milliseconds + index / 100}
                    for index in range(10)]
        rows.append({"observation": observation, "arm_kind": kind,
            "lowered_shape_bits": 433, "compiled_shape_bits": symbol["shape_bits"],
            "geometry": symbol["geometry"], "min_blocks": symbol["min_blocks"],
            "manifest_sha256": manifest_sha, "executable_sha256": "e"*64,
            "pilot_median_ms": milliseconds + .01, "retained_samples": 50,
            "pilot_samples": pilot, "samples": retained, "candidate_wall_seconds": .5,
            "coordinate_cpu_setup_seconds": 10.0, "coordinate_harness_setup_seconds": 2.0,
            "coordinate_execution_wall_seconds": 14.0})
    return rows, manifest, manifest_sha


def test_sectioned_group_requires_one_shared_prepared_input_and_setup() -> None:
    rows, manifest, manifest_sha = sectioned_rows()
    REPORT.validate_sectioned_screen_group(rows, manifest, manifest_sha)

    changed_input = copy.deepcopy(rows)
    changed_input[-1]["observation"]["input_sha256"] = "different"
    try:
        REPORT.validate_sectioned_screen_group(changed_input, manifest, manifest_sha)
    except ValueError as error:
        assert "prepared input" in str(error)
    else:
        raise AssertionError("distinct prepared inputs were accepted")

    changed_setup = copy.deepcopy(rows)
    changed_setup[-1]["coordinate_cpu_setup_seconds"] = 11.0
    try:
        REPORT.validate_sectioned_screen_group(changed_setup, manifest, manifest_sha)
    except ValueError as error:
        assert "setup" in str(error)
    else:
        raise AssertionError("distinct coordinate setup was accepted")


def test_sectioned_comparison_wording_is_unambiguous() -> None:
    assert REPORT.comparison_wording(9.0, 10.0) == {
        "percent_positive_is_slower": -10.0,
        "wording": "candidate is 10.000% faster than baseline",
    }
    assert REPORT.comparison_wording(12.0, 10.0) == {
        "percent_positive_is_slower": 20.0,
        "wording": "candidate is 20.000% slower than baseline",
    }


def test_sectioned_spill_opcodes_are_descriptive() -> None:
    opcode = {
        "instructions": 123,
        "ldc": 4,
        "ldcu": 5,
        "ldg": 6,
        "forbidden": 7,
        "bssy": 8,
        "bsync": 9,
    }
    assert REPORT.sectioned_opcode_for_symbol({"spilling": opcode}, "spilling") == opcode
    try:
        REPORT.sectioned_opcode_for_symbol({}, "missing")
    except ValueError as error:
        assert "missing" in str(error)
    else:
        raise AssertionError("missing opcode row unexpectedly passed")


def test_sectioned_bound_summary_is_descriptive() -> None:
    assert REPORT.sectioned_register_bucket("wide9", 3) == 72
    assert REPORT.sectioned_register_bucket("split3", 7) == 96
    assert REPORT.sectioned_register_bucket("serial3_low", None) is None
    rows = [
        {
            "arm_kind": "sectioned", "geometry": "split3", "min_blocks": 9,
            "vs_generic_percent": -10.0, "registers": 72, "stack_bytes": 0,
            "local_bytes": 0, "instructions": 100, "identical_to_natural": False,
            "vs_same_geometry_natural_percent": -2.0,
        },
        {
            "arm_kind": "sectioned", "geometry": "split3", "min_blocks": 9,
            "vs_generic_percent": 5.0, "registers": 68, "stack_bytes": 8,
            "local_bytes": 0, "instructions": 120, "identical_to_natural": False,
            "vs_same_geometry_natural_percent": 3.0,
        },
    ]
    assert REPORT.sectioned_bound_summaries(rows) == [{
        "geometry": "split3", "min_blocks": 9, "coordinates": 2,
        "theoretical_register_bucket": 72,
        "median_percent_positive_is_slower": -2.5,
        "min_percent_positive_is_slower": -10.0,
        "max_percent_positive_is_slower": 5.0,
        "median_vs_same_geometry_natural_percent_positive_is_slower": 0.5,
        "min_vs_same_geometry_natural_percent_positive_is_slower": -2.0,
        "max_vs_same_geometry_natural_percent_positive_is_slower": 3.0,
        "faster_coordinates": 1, "equal_coordinates": 0, "slower_coordinates": 1,
        "registers_min": 68, "registers_median": 70.0, "registers_max": 72,
        "stack_positive_coordinates": 1, "local_positive_coordinates": 0,
        "instructions_median": 110.0, "natural_identical_coordinates": 0,
    }]


def test_sectioned_normalization_joins_static_and_named_baselines() -> None:
    rows, manifest, manifest_sha = sectioned_rows()
    resources = {
        row["observation"]["launch"]["symbol"]: {
            "registers": 80 + index,
            "stack_bytes": 0,
            "shared_bytes": 0,
            "local_bytes": 0,
        }
        for index, row in enumerate(rows)
    }
    normalized = REPORT.normalize_sectioned_rows(
        rows, manifest, manifest_sha,
        resources,
        {("add_sub_lui_auipc_mop", 0): 10.0},
        {("add_sub_lui_auipc_mop", 0): 8.0},
    )
    assert normalized[0]["median_ms"] == 10.02
    assert normalized[0]["registers"] == 80
    assert normalized[0]["vs_generic"] == {
        "percent_positive_is_slower": 0.0,
        "wording": "candidate is equal to baseline",
    }
    assert normalized[1]["vs_generic"] == {
        "percent_positive_is_slower": 1.24750499002,
        "wording": "candidate is 1.248% slower than baseline",
    }


def test_sectioned_tamper_matrix_fails_closed() -> None:
    rows, manifest, manifest_sha = sectioned_rows()
    mutations = []
    for mutate in (
        lambda value: value[1].__setitem__("min_blocks", 99),
        lambda value: value[1]["pilot_samples"].__setitem__(0, {**value[1]["pilot_samples"][0], "warmup": 1}),
        lambda value: value[1]["samples"].pop(),
        lambda value: value[1]["pilot_samples"].pop(),
        lambda value: value[1]["samples"][0].__setitem__("pass_position", 99),
        lambda value: value[1]["samples"].__setitem__(-1, copy.deepcopy(value[1]["samples"][0])),
        lambda value: value[1].__setitem__("executable_sha256", "x"*64),
        lambda value: value[0].__setitem__("min_blocks", 3),
        lambda value: value[1]["observation"].__setitem__("candidate_id", "split3"),
        lambda value: value.pop(),
        lambda value: value.append(copy.deepcopy(value[1])),
    ):
        changed=copy.deepcopy(rows); mutate(changed); mutations.append(changed)
    for changed in mutations:
        try: REPORT.validate_sectioned_screen_group(changed, manifest, manifest_sha)
        except (ValueError, KeyError): pass
        else: raise AssertionError("sectioned timing tamper unexpectedly passed")


def test_sectioned_bindings_bind_actual_executable_and_raw_files() -> None:
    rows, _manifest, manifest_sha = sectioned_rows()
    executable_sha = "e" * 64
    with tempfile.TemporaryDirectory() as directory:
        root = pathlib.Path(directory)
        rows_path = root / "add_sub_lui_auipc_mop-0.jsonl"
        command_path = root / "add_sub_lui_auipc_mop-0.command"
        driver_path = root / "add_sub_lui_auipc_mop-0.driver.log"
        rows_path.write_text("".join(
            json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n"
            for row in rows
        ))
        command_path.write_text("fixture command\n")
        driver_path.write_text("fixture driver\n")
        observation = rows[0]["observation"]
        bindings = {
            "version": 1,
            "manifest_sha256": manifest_sha,
            "executable_sha256": executable_sha,
            "screen": [{
                "circuit": "add_sub_lui_auipc_mop",
                "layer": 0,
                "rows": 16,
                "rows_sha256": REPORT.sha256(rows_path),
                "command_sha256": REPORT.sha256(command_path),
                "driver_sha256": REPORT.sha256(driver_path),
                "input_sha256": observation["input_sha256"],
                "program_sha256": observation["program_sha256"],
                "checksum": observation["checksum"],
                "device_identity": observation["device_identity"],
            }],
        }

        REPORT.validate_sectioned_bindings(
            bindings, rows, manifest_sha, executable_sha, root,
        )
        try:
            REPORT.validate_sectioned_bindings(
                bindings, rows, manifest_sha, "f" * 64, root,
            )
        except ValueError as error:
            assert "executable" in str(error)
        else:
            raise AssertionError("forged executable binding unexpectedly passed")

        rows_path.write_text(rows_path.read_text() + "{}\n")
        try:
            REPORT.validate_sectioned_bindings(
                bindings, rows, manifest_sha, executable_sha, root,
            )
        except ValueError as error:
            assert "rows" in str(error)
        else:
            raise AssertionError("tampered raw screen rows unexpectedly passed")


if __name__ == "__main__":
    test_controlled_pair_summary()
    test_capacity_and_residency_join()
    test_default_static_tables_are_bound_to_the_final_campaign()
    test_sectioned_group_requires_one_shared_prepared_input_and_setup()
    test_sectioned_comparison_wording_is_unambiguous()
    test_sectioned_spill_opcodes_are_descriptive()
    test_sectioned_bound_summary_is_descriptive()
    test_sectioned_normalization_joins_static_and_named_baselines()
    test_sectioned_tamper_matrix_fails_closed()
    test_sectioned_bindings_bind_actual_executable_and_raw_files()
    print("PROTOTYPE_REPORT_FIXTURES_OK")
