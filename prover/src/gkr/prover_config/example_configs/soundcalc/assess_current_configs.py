"""Run soundcalc's WHIR model on airbender's GKR+WHIR prover configs.

Our WhirSchedule fixes an explicit LDE factor per intermediate oracle instead of WHIR's
"domain halves every iteration" rule, so after building soundcalc's WHIR object we overwrite its
per-iteration `log_inv_rates` with ours (the object reads that list everywhere).
"""
import math, sys
from soundcalc.common.fields import FieldParams, BABYBEAR_4
from soundcalc.pcs.whir import WHIR, WHIRConfig
from soundcalc.proxgaps.unique_decoding import UniqueDecodingRegime
from soundcalc.proxgaps.johnson_bound import JohnsonBoundRegime
from soundcalc.common.utils import get_bits_of_security_from_error

PROTH120_P = 7 * 2**120 + 1
PROTH120 = FieldParams(name="Proth120", p=PROTH120_P, field_extension_degree=1, F=float(PROTH120_P), two_adicity=120)

def field_bits(f):  # floor(log2 |E|), as prover_config::pow_bits::challenge_field_size_log2
    return int(math.floor(math.log2(f.F)))

def batch_pow(f, message_log2, base_lde_log2, batch):
    # prover_config::pow_bits::pow_bits_for_batched_proximity (security_bits = 100)
    batch_bits = (batch - 1).bit_length()
    no_pow = max(0, field_bits(f) - (message_log2 + base_lde_log2) - batch_bits)
    return max(0, 100 - no_pow)

def our_config(name, field, message_log2, base_lde, folds, queries, ldes, pows, batch):
    base_lde_log2 = base_lde.bit_length() - 1
    rates = [base_lde_log2] + [l.bit_length() - 1 for l in ldes]
    rates = rates + [rates[-1]]  # soundcalc keeps M+1 entries; the last is never used for a code
    M = len(folds)
    bpow = batch_pow(field, message_log2, base_lde_log2, batch)
    cfg = WHIRConfig(
        hash_size_bits=256, log_inv_rate=base_lde_log2, num_iterations=M, folding_factors=folds,
        field=field, log_degree=message_log2, batch_size=batch, power_batching=True,
        grinding_batching_phase=bpow, constraint_degree=3,  # soundcalc's minimum; ours is 2 (conservative)
        grinding_bits_folding=[[0] * k for k in folds], num_queries=queries,
        grinding_bits_queries=pows, num_ood_samples=[1] * (M - 1), grinding_bits_ood=[0] * (M - 1),
    )
    w = WHIR(cfg)
    std_rates = list(w.log_inv_rates)
    w.log_inv_rates = rates
    return name, w, std_rates, rates, bpow

def report(name, w, std_rates, rates, bpow):
    print(f"\n=== {name}")
    print(f"  field {w.field.name} (|F| ~ 2^{math.log2(w.field.F):.1f}), message 2^{w.log_degrees[0]}, folds {w.folding_factors}, queries {w.num_queries}, query PoW {w.grinding_bits_queries}")
    print(f"  batch {w.batch_size} polys, batching PoW {bpow}; log_inv_rates ours {rates[:-1]} (soundcalc standard model would be {std_rates[:-1]})")
    for regime in (UniqueDecodingRegime(w.field), JohnsonBoundRegime(w.field)):
        lv = w.get_pcs_security_levels(regime)
        worst = min(lv, key=lv.get)
        # per-iteration query errors (what the PoW schedule protects)
        q = [get_bits_of_security_from_error(w._epsilon_query(i, regime)) for i in range(w.num_iterations)]
        print(f"  {regime.identifier():>4}: total {min(lv.values()):3d} bits  (weakest: {worst} = {lv[worst]});  per-iteration query+PoW bits {q};  batching {lv.get('batching')}")
    # what our own PessimisticConjecture accounting claims: bits/query = log_inv_rate, 20% query surplus
    ours = [w.num_queries[i] * rates[i] / 1.2 + w.grinding_bits_queries[i] for i in range(w.num_iterations)]
    print(f"  (airbender's own 'pessimistic conjecture' accounting: per-iteration {[round(x) for x in ours]} bits)")

configs = []
# EVM production (Proth120, 2^22 trace packed x16 -> 2^26 message); 7 + 1 merged packed columns
configs.append(our_config("EVM production Proth120 2^22 (packed 2^26)", PROTH120, 26, 32,
    [2, 4, 4, 4, 4, 4], [17, 12, 8, 6, 5, 4], [1 << 7, 1 << 11, 1 << 15, 1 << 19, 1 << 23], [30, 30, 27, 25, 21, 24], 8))
# BabyBear^4 sec-100 configs (unified circuit: 38 + 66 + 10 = 114 base columns batched)
BB = {
    20: ([1, 5, 5, 4, 4], [89, 11, 7, 6, 5], [256, 8192, 32768, 524288], [26, 27, 25, 25, 21]),
    21: ([1, 5, 5, 5, 4], [89, 15, 8, 6, 5], [64, 2048, 32768, 524288], [26, 25, 27, 25, 21]),
    22: ([1, 5, 5, 5, 5], [89, 15, 8, 6, 5], [64, 2048, 32768, 524288], [26, 25, 27, 25, 21]),
    23: ([1, 5, 5, 5, 4], [89, 23, 10, 7, 5], [16, 512, 16384, 524288], [26, 24, 25, 19, 21]),
    24: ([1, 5, 5, 5, 4, 3], [89, 23, 10, 7, 5, 5], [16, 512, 16384, 524288, 524288], [26, 24, 25, 19, 21, 21]),
}
for n, (f, q, l, p) in BB.items():
    configs.append(our_config(f"BabyBear^4 sec-100 trace 2^{n} (base LDE 2)", BABYBEAR_4, n, 2, f, q, l, p, 114))
configs.append(our_config("BabyBear^4 L1-feeder 2^23 (base LDE 16, all oracles 2^27)", BABYBEAR_4, 23, 16,
    [1, 5, 5, 5, 4], [21, 17, 9, 5, 4], [32, 1024, 32768, 1048576], [29, 26, 25, 26, 21], 114))
for c in configs:
    report(*c)
