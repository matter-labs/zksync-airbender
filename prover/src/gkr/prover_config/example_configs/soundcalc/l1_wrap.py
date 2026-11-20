"""Reproduce and certify the Proth120 ETH1020-0047 schedule with soundcalc 2af5e7d."""
import argparse
import json
from pathlib import Path

from soundcalc.common.fields import FieldParams

import whir_schedule_search as search


def certify(schedule, trace_log2, packed_columns, field_size):
    modulus = 7 * 2**120 + 1
    search.F = FieldParams("Proth120", modulus, 1, field_size, 120)
    search.HASH_SIZE_BITS = 200
    base = schedule["base_round"]
    internal = schedule["internal_rounds"]
    rounds = [base, *internal]
    folds = [base["fold_log2"], *(r["folding_log2"] for r in internal)]
    assert all(r["num_ood_samples"] == 1 for r in internal)
    whir = search.build(
        trace_log2 + base["physical_packing_log2"],
        folds,
        [r["num_queries"] for r in rounds],
        [r["lde_factor_log2"] for r in internal],
        [r["queries_pow_bits"] for r in rounds],
        [[r["folding_pow_bits"]] * fold for r, fold in zip(rounds, folds)],
        [r["ood_pow_bits"] for r in internal],
        packed_columns,
        base["batching_pow_bits"],
        base["lde_factor_log2"],
    )
    regime = search.JohnsonBoundRegime(search.F, explicit_m=3)
    levels = whir.get_pcs_security_levels(regime)
    assert levels and min(levels.values()) >= search.TARGET, levels
    return dict(
        field_size=field_size,
        regime=regime.identifier(),
        messages=whir.log_degrees,
        levels=levels,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trace-log2", type=int, default=22)
    parser.add_argument("--packed-columns", type=int, default=14)
    args = parser.parse_args()
    schedule = json.loads(Path(__file__).with_name("eth1020-0047.json").read_text())
    certificates = [
        certify(schedule, args.trace_log2, args.packed_columns, field_size)
        for field_size in (7 * 2**120 + 1, 2**128 / 37)
    ]
    print(json.dumps(dict(schedule=schedule, certificates=certificates), indent=2))
