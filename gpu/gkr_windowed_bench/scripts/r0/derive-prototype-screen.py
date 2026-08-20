#!/usr/bin/env python3
"""Derive the deterministic, descriptive prototype production screen."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
from collections import defaultdict
from typing import Any, Callable


ROOT = pathlib.Path(__file__).resolve().parents[4]
DEFAULT_CENSUS = ROOT / "gpu/gkr_windowed_bench/artifacts/windowed_accumulator_census_v1.json"
DEFAULT_PRODUCTION = ROOT / "target/windowed-gkr-r0-corpus/task9/production-plan.jsonl"
DEFAULT_OUTPUT = ROOT / "target/windowed-gkr-r0-prototype-bank/screen/coordinates.json"


def file_sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def weight(row: dict[str, Any], profile: str) -> int | None:
    return next((entry["weight"] for entry in row["weights"] if entry["profile"] == profile), None)


def long_reuse(row: dict[str, Any]) -> int:
    return sum(
        entry["count"]
        for entry in row["locality"]["canonical"]["lru_stack_distance_histogram"]
        if entry["label"] in {"64..=127", "128+"}
    )


def derive(census: dict[str, Any], production_rows: list[dict[str, Any]]) -> dict[str, Any]:
    rows = [row for row in census["coordinates"] if row["id"]["regime"] == "R0"]
    production = {(row["circuit"], row["layer"]): row["preflight"]["requested_bytes"] for row in production_rows}
    if len(rows) != 57 or len(production) != 57:
        raise ValueError("screen derivation requires exact 57-row R0 census and production plan")
    reasons: dict[tuple[str, int], list[str]] = defaultdict(list)
    by_circuit: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_circuit[row["id"]["circuit"]].append(row)
    for circuit, circuit_rows in sorted(by_circuit.items()):
        def mass_key(row: dict[str, Any]) -> tuple[int, int, int, int]:
            uses = row["locality"]["canonical"]["source_uses"]
            current = weight(row, "current_base")
            development = weight(row, "development_recursion_proxy")
            if current is not None:
                return (2, current * uses, uses, -row["id"]["layer"])
            if development is not None:
                return (1, development * uses, uses, -row["id"]["layer"])
            return (0, uses, uses, -row["id"]["layer"])
        selected = max(circuit_rows, key=mass_key)
        reasons[(circuit, selected["id"]["layer"])].append("circuit_weighted_source_use_mass")
    metrics: list[tuple[str, Callable[[dict[str, Any]], float | int]]] = [
        ("maximum_terms", lambda row: row["population"]["terms"]),
        ("maximum_bf_atoms", lambda row: row["canonical_split"]["bf_atoms"]),
        ("maximum_e4_atoms", lambda row: row["canonical_split"]["e4_atoms"]),
        ("maximum_e4_fraction", lambda row: row["canonical_split"]["e4_atoms"] / max(1, row["population"]["terms"])),
        ("maximum_source_uses", lambda row: row["locality"]["canonical"]["source_uses"]),
        ("maximum_unique_sources", lambda row: row["locality"]["canonical"]["unique_sources"]),
        ("maximum_source_reuse", lambda row: row["locality"]["canonical"]["max_source_reuse"]),
        ("maximum_long_reuse_distance", long_reuse),
        ("maximum_group_count", lambda row: row["analysis_grouping"]["groups"]),
        ("maximum_group_members", lambda row: row["analysis_grouping"]["members"]),
        ("maximum_requested_production_bytes", lambda row: production[(row["id"]["circuit"], row["id"]["layer"])]),
    ]
    for reason, metric in metrics:
        selected = max(rows, key=lambda row: (metric(row), row["id"]["circuit"], -row["id"]["layer"]))
        reasons[(selected["id"]["circuit"], selected["id"]["layer"])].append(reason)
    census_by_key = {(row["id"]["circuit"], row["id"]["layer"]): row for row in rows}
    selected_rows = []
    for (circuit, layer), selected_reasons in sorted(reasons.items()):
        row = census_by_key[(circuit, layer)]
        selected_rows.append({
            "circuit": circuit,
            "layer": layer,
            "trace_len": row["trace_len"],
            "log_trace": row["trace_len"].bit_length() - 1,
            "reasons": sorted(selected_reasons),
            "terms": row["population"]["terms"],
            "bf_atoms": row["canonical_split"]["bf_atoms"],
            "e4_atoms": row["canonical_split"]["e4_atoms"],
            "source_uses": row["locality"]["canonical"]["source_uses"],
            "unique_sources": row["locality"]["canonical"]["unique_sources"],
            "max_source_reuse": row["locality"]["canonical"]["max_source_reuse"],
            "long_reuse_distance": long_reuse(row),
            "groups": row["analysis_grouping"]["groups"],
            "group_members": row["analysis_grouping"]["members"],
            "requested_bytes": production[(circuit, layer)],
            "weights": {entry["profile"]: entry["weight"] for entry in row["weights"]},
        })
    return {"version": 1, "rows": selected_rows}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--census", default=str(DEFAULT_CENSUS))
    parser.add_argument("--production-plan", default=str(DEFAULT_PRODUCTION))
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT))
    args = parser.parse_args()
    census_path = pathlib.Path(args.census)
    production_path = pathlib.Path(args.production_plan)
    production = [json.loads(line) for line in production_path.read_text().splitlines() if line]
    result = derive(json.loads(census_path.read_text()), production)
    result["inputs"] = {
        "census": str(census_path.resolve()), "census_sha256": file_sha256(census_path),
        "production_plan": str(production_path.resolve()), "production_plan_sha256": file_sha256(production_path),
    }
    output = pathlib.Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n")
    print(f"PROTOTYPE_SCREEN_DERIVED rows={len(result['rows'])} output={output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
