#!/usr/bin/env python3
"""Derive a deterministic factor-cover for prototype-bank sanitizers."""

from __future__ import annotations

import argparse
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[4]
DEFAULT_MANIFEST = ROOT / "gpu/gkr_windowed_bench/artifacts/windowed_r0_prototype_manifest_v1.json"
PRIOR_FAILURES = {
    "r0pb-config/r0pb/compact_r0_port/canonical/canonical/cta288_pair/materialized/template/cap8",
    "r0pb-config/r0pb/current_fixed_slot/canonical/canonical/cta288_pair/materialized/template/cap8",
}


def factors(symbol: dict[str, Any], configuration: dict[str, Any]) -> set[str]:
    result = {
        f"encoding={symbol['encoding']}",
        f"inner={symbol['inner']}",
        f"outer={symbol['outer']}",
        f"geometry={symbol['geometry']}",
        f"source_policy={symbol['source_policy']}",
    }
    capacity = configuration.get("tile_capacity")
    if capacity is not None:
        result.add(f"tile_capacity={capacity}")
    return result


def derive(manifest: dict[str, Any]) -> dict[str, Any]:
    symbols = {row["candidate_id"]: row for row in manifest["symbols"]}
    configurations = []
    for configuration in manifest["configurations"]:
        symbol = symbols[configuration["candidate_id"]]
        if symbol["lineage"] != "template":
            continue
        configurations.append((configuration, symbol, factors(symbol, configuration)))
    universe = set().union(*(entry[2] for entry in configurations))
    selected: dict[str, tuple[dict[str, Any], dict[str, Any], set[str]]] = {}
    for entry in configurations:
        if entry[0]["configuration_id"] in PRIOR_FAILURES:
            selected[entry[0]["configuration_id"]] = entry
    covered = set().union(*(entry[2] for entry in selected.values())) if selected else set()
    while covered != universe:
        choices = [entry for entry in configurations if entry[0]["configuration_id"] not in selected]
        best = min(
            choices,
            key=lambda entry: (-len(entry[2] - covered), entry[0]["configuration_id"]),
        )
        if not (best[2] - covered):
            raise ValueError(f"uncovered sanitizer factors: {sorted(universe - covered)}")
        selected[best[0]["configuration_id"]] = best
        covered |= best[2]
    rows = []
    for configuration_id, (configuration, symbol, row_factors) in sorted(selected.items()):
        rows.append(
            {
                "configuration_id": configuration_id,
                "candidate_id": symbol["candidate_id"],
                "symbol": symbol["symbol"],
                "encoding": symbol["encoding"],
                "inner": symbol["inner"],
                "outer": symbol["outer"],
                "geometry": symbol["geometry"],
                "source_policy": symbol["source_policy"],
                "tile_capacity": configuration.get("tile_capacity"),
                "factors": sorted(row_factors),
                "prior_failure": configuration_id in PRIOR_FAILURES,
                "tools": ["memcheck", "racecheck"]
                if symbol["source_policy"] == "materialized"
                else ["memcheck"],
            }
        )
    return {
        "version": 1,
        "universe": sorted(universe),
        "covered": sorted(covered),
        "rows": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--output")
    args = parser.parse_args()
    result = derive(json.loads(pathlib.Path(args.manifest).read_text()))
    text = json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n"
    if args.output:
        output = pathlib.Path(args.output)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(text)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
