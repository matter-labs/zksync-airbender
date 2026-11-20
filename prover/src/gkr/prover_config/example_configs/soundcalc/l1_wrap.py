"""Search and certify a physically packed Proth120 L1 wrap at soundcalc 2af5e7d."""
import argparse
import json

from soundcalc.common.fields import FieldParams

import whir_schedule_search as search


def certify(trace_log2, packed_columns, base_lde_log2, field_size):
    modulus = 7 * 2**120 + 1
    search.F = FieldParams("Proth120", modulus, 1, field_size, 120)
    search.UDR = search.UniqueDecodingRegime(search.F)
    search.JBR = {
        m: search.JohnsonBoundRegime(search.F, explicit_m=m)
        for m in (3, 4, 5, 8, 12, 20)
    }
    search.HASH_SIZE_BITS = 200
    search.FIELD_BITS = 122
    search.MAX_DOM = 31
    folds = [1, 5, 5, 5, 5]
    whir, regime = search.solve(
        f"Proth120 L1, trace log {trace_log2}, base LDE log {base_lde_log2}",
        trace_log2 + 3,
        folds,
        packed_columns,
        27,
        base_lde_log2=base_lde_log2,
        base_regimes=[("UDR", search.UDR)]
        + [(f"JBR m={m}", value) for m, value in search.JBR.items()],
        max_pow={"batching": 25},
    )
    # The prover stores one difficulty per oracle and uses it at every fold.
    fold_pow = [max(steps) for steps in whir.grinding_bits_folding]
    whir.grinding_bits_folding = [[bits] * fold for bits, fold in zip(fold_pow, folds)]
    levels = whir.get_pcs_security_levels(regime)
    assert min(levels.values()) >= search.TARGET
    rates = whir.log_inv_rates[:-1]
    return dict(
        field_size=field_size,
        rates=rates,
        messages=whir.log_degrees,
        folds=folds,
        queries=whir.num_queries,
        query_pow=whir.grinding_bits_queries,
        fold_pow=fold_pow,
        ood_pow=whir.grinding_bits_ood,
        batching_pow=whir.grinding_batching_phase,
        regimes=[regime.pick(2.0**-rate).identifier() for rate in rates],
        levels=levels,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trace-log2", type=int, default=22)
    parser.add_argument("--packed-columns", type=int, default=14)
    args = parser.parse_args()
    modulus = 7 * 2**120 + 1
    max_atom_denominator = 2**128 / 37
    for base_lde_log2 in (3, 4):
        for field_size in (float(modulus), max_atom_denominator):
            result = certify(args.trace_log2, args.packed_columns, base_lde_log2, field_size)
            print(json.dumps(result))
