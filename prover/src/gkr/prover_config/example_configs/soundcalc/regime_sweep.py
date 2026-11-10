import math
from soundcalc.common.fields import BABYBEAR_4 as F
from soundcalc.pcs.whir import WHIR, WHIRConfig
from soundcalc.proxgaps.johnson_bound import JohnsonBoundRegime
from soundcalc.proxgaps.unique_decoding import UniqueDecodingRegime
from soundcalc.common.utils import get_bits_of_security_from_error as bits

BB = {  # trace_log2: folds, queries, intermediate LDE factors, per-round PoW   (base LDE 2, 114 batched columns)
    20: ([1, 5, 5, 4, 4], [89, 11, 7, 6, 5], [256, 8192, 32768, 524288], [26, 27, 25, 25, 21]),
    21: ([1, 5, 5, 5, 4], [89, 15, 8, 6, 5], [64, 2048, 32768, 524288], [26, 25, 27, 25, 21]),
    22: ([1, 5, 5, 5, 5], [89, 15, 8, 6, 5], [64, 2048, 32768, 524288], [26, 25, 27, 25, 21]),
    23: ([1, 5, 5, 5, 4], [89, 23, 10, 7, 5], [16, 512, 16384, 524288], [26, 24, 25, 19, 21]),
    24: ([1, 5, 5, 5, 4, 3], [89, 23, 10, 7, 5, 5], [16, 512, 16384, 524288, 524288], [26, 24, 25, 19, 21, 21]),
}
def batch_pow(n): return max(0, 100 - max(0, 123 - (n + 1) - 7))

def build(n, queries, ood):
    folds, _, ldes, pows = BB[n]
    rates = [1] + [l.bit_length() - 1 for l in ldes]
    M = len(folds)
    cfg = WHIRConfig(hash_size_bits=256, log_inv_rate=1, num_iterations=M, folding_factors=folds, field=F,
        log_degree=n, batch_size=114, power_batching=True, grinding_batching_phase=batch_pow(n), constraint_degree=3,
        grinding_bits_folding=[[0]*k for k in folds], num_queries=queries, grinding_bits_queries=pows,
        num_ood_samples=[ood]*(M-1), grinding_bits_ood=[0]*(M-1))
    w = WHIR(cfg); w.log_inv_rates = rates + [rates[-1]]; return w, rates

def needed(w, regime, pows):
    return [math.ceil((100 - pows[i]) / -math.log2(1 - w._get_delta_for_iteration(i, regime))) for i in range(w.num_iterations)]

def summ(w, regime):
    lv = w.get_pcs_security_levels(regime); k = min(lv, key=lv.get)
    g = lambda p: min(v for nme, v in lv.items() if nme.startswith(p))
    return lv[k], k, g('fold'), g('OOD'), min(g('Shift'), lv['fin']), lv['batching']

for n, (folds, queries, ldes, pows) in BB.items():
    w, rates = build(n, queries, 1)
    doms = [w.log_degrees[i] + rates[i] for i in range(len(folds))]
    print(f"\n=== BabyBear^4 sec-100, trace 2^{n}: folds {folds}, queries {queries}, PoW {pows}, log_inv_rates {rates}, oracle domains 2^{doms}, batching PoW {batch_pow(n)}")
    for label, regime in [("UDR", UniqueDecodingRegime(F))] + [(f"JBR m={m}", JohnsonBoundRegime(F, explicit_m=m)) for m in (50, 10, 3)]:
        for ood in (1, 2):
            w, _ = build(n, queries, ood)
            cur = summ(w, regime)
            nq = needed(w, regime, pows)
            w2, _ = build(n, [max(a, b) for a, b in zip(queries, nq)], ood)
            new = summ(w2, regime)
            bpq = [round(-math.log2(1 - w._get_delta_for_iteration(i, regime)), 2) for i in range(len(folds))]
            tag = f"{label:>9} ood={ood}"
            print(f"  {tag}: now total {cur[0]:3d} ({cur[1]:<14}) fold {cur[2]:3d} OOD {cur[3]:3d} shift/fin {cur[4]:3d} batch {cur[5]:3d} | bits/q {bpq} -> need {nq}: total {new[0]:3d} ({new[1]})")
