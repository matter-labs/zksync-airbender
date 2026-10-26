"""Mixed-regime 100-bit WHIR schedule search over ethereum/soundcalc, printing WhirSchedule fields.
Run: PYTHONPATH=<soundcalc clone> python3.11 whir_schedule_search.py   (python >= 3.9; soundcalc commit 2af5e7d)
The shapes under __main__ are the EthproofsSoundnessCalc entries of ../ethproofs_soundcalc.rs.
Constraints: BabyBear^4, sec 100, base LDE 2, ONE OOD sample per oracle (+ OOD PoW), folding PoW allowed
(cap FOLD_CAP per sumcheck round), query PoW <= LATER_POW after the base round (the query count is sized
against that cap, then the PoW is lowered to the smallest value that still reaches the target), base query PoW 28.
Virtual packing (fold_log2 = 0) is emulated with log_degree + 1 and k_0 = 1 (soundcalc needs k >= 1):
the batched polynomial of size 2^m is then re-committed as the first internal oracle at size 2^m,
which is exactly the virtual-packing shape; the emulated base code is 2x larger than the real one,
so the emulated base fold term is 1 bit conservative; the real batching term is recomputed directly."""
import math
from soundcalc.common.fields import BABYBEAR_4 as F
from soundcalc.pcs.whir import WHIR, WHIRConfig
from soundcalc.proxgaps.proxgaps_regime import ProximityGapsRegime
from soundcalc.proxgaps.johnson_bound import JohnsonBoundRegime
from soundcalc.proxgaps.unique_decoding import UniqueDecodingRegime
from soundcalc.common.utils import get_bits_of_security_from_error as bits

TARGET = 100; LATER_POW = 27; FOLD_CAP = 24; MAX_DOM = 27; FIELD_BITS = 123

class Mixed(ProximityGapsRegime):
    """per-iteration regime (WHIR Thm 5.2 has per-iteration delta_i / ell_i); keyed by iteration rate"""
    def __init__(self, field, by_rate): super().__init__(field); self.by_rate = by_rate
    def pick(self, r): return self.by_rate[round(-math.log2(r))]
    def identifier(self): return "mixed"
    def get_proximity_parameter(self, r, d): return self.pick(r).get_proximity_parameter(r, d)
    def get_max_list_size(self, r, d): return self.pick(r).get_max_list_size(r, d)
    def get_error_powers(self, r, d, b): return self.pick(r).get_error_powers(r, d, b)
    def get_error_linear(self, r, d): return self.pick(r).get_error_linear(r, d)
    def get_error_multilinear(self, r, d, b): return self.pick(r).get_error_multilinear(r, d, b)

UDR = UniqueDecodingRegime(F)
JBR = {m: JohnsonBoundRegime(F, explicit_m=m) for m in (3, 4, 5, 8, 12, 20)}

def batch_pow(msg_log2, n_cols):   # = prover_config::pow_bits::pow_bits_for_batched_proximity
    bbits = (n_cols - 1).bit_length()
    return max(0, TARGET - max(0, FIELD_BITS - (msg_log2 + 1) - bbits))

def build(log_degree, folds, queries, ldes, pows, fold_pows, ood_pows, n_cols, bpow):
    M = len(folds)
    cfg = WHIRConfig(hash_size_bits=256, log_inv_rate=1, num_iterations=M, folding_factors=folds, field=F,
        log_degree=log_degree, batch_size=n_cols, power_batching=True, grinding_batching_phase=bpow, constraint_degree=3,
        grinding_bits_folding=fold_pows, num_queries=queries, grinding_bits_queries=pows,
        num_ood_samples=[1]*(M-1), grinding_bits_ood=ood_pows)
    w = WHIR(cfg); rates = [1] + ldes; w.log_inv_rates = rates + [rates[-1]]; return w

def solve(label, msg_log2, folds, n_cols, base_pow, base_queries=None, virtual=False, today=None):
    log_degree = msg_log2 + (1 if virtual else 0)
    folds = ([1] + folds[1:]) if virtual else folds
    M = len(folds); bpow = batch_pow(msg_log2, n_cols)
    polys = [log_degree - sum(folds[:i+1]) for i in range(M - 1)]
    bpq0 = -math.log2(1 - UDR.get_proximity_parameter(0.5, 2 ** (log_degree - 1)))
    t0 = base_queries if base_queries else math.ceil((TARGET - base_pow) / bpq0)
    base_bits = min(TARGET, math.floor(t0 * bpq0 + base_pow))
    queries, ldes, regimes, pows, fold_pows, ood_pows, rows = [t0], [], {1: UDR}, [base_pow], [[0]], [], []
    for i, p in enumerate(polys, start=1):
        k = folds[i]; best = None
        cands = [("UDR", UDR, L) for L in range(2, MAX_DOM - p + 1)] + [(f"JBR m={m}", JBR[m], L) for m in JBR for L in range(2, MAX_DOM - p + 1)]
        for lab, reg, L in cands:
            if L in ldes: continue
            rate = 2.0 ** -L
            bpq = -math.log2(1 - reg.get_proximity_parameter(rate, 2 ** (p - 1)))
            t = math.ceil((TARGET - LATER_POW) / bpq)
            fp = []
            for s in range(1, k + 1):
                ls = reg.get_max_list_size(rate, 2 ** (p - s + 1))
                e = 3 * ls / F.F + reg.get_error_powers(rate, 2 ** (p - s), 2)
                fp.append(max(0, TARGET - bits(e)))
            if max(fp) > FOLD_CAP: continue
            ls0 = reg.get_max_list_size(rate, 2 ** p)
            op = max(0, TARGET - bits(ls0 * ls0 * ((2 ** p) / (2 * F.F))))
            if op > LATER_POW: continue
            rest = M - 1 - i
            trial = build(log_degree, folds, queries + [t] + [80] * rest, ldes + [L] + [21 + j for j in range(rest)],
                          pows + [LATER_POW] * (rest + 1), fold_pows + [fp] + [[0] * folds[i + 1 + j] for j in range(rest)],
                          ood_pows + [op] + [0] * rest, n_cols, bpow)
            regs = dict(regimes); regs[L] = reg
            for j in range(rest): regs[21 + j] = UDR
            lv = trial.get_pcs_security_levels(Mixed(F, regs))
            local = {kk: v for kk, v in lv.items() if kk.startswith(f"fold(i={i},") or kk == f"OOD(i={i})" or kk == f"Shift(i={i+1})" or (i == M - 1 and kk == 'fin')}
            if not all(v >= TARGET for v in local.values()): continue
            key = (t, max(fp) + op, -L)
            if best is None or key < best[0]: best = (key, lab, reg, L, fp, op, t, bpq)
        assert best, f"{label}: no option for oracle 2^{p}"
        _, lab, reg, L, fp, op, t, bpq = best
        # The query count was sized against the LATER_POW cap; now take the SMALLEST query PoW that
        # still lifts this oracle's query term (Shift / fin) to the target: t * bits_per_query is
        # rarely a whole number of bits short of the target, and every spare bit is wasted grinding.
        rest = M - 1 - i
        probe = build(log_degree, folds, queries + [t] + [80] * rest, ldes + [L] + [21 + j for j in range(rest)],
                      pows + [0] * (rest + 1), fold_pows + [fp] + [[0] * folds[i + 1 + j] for j in range(rest)],
                      ood_pows + [op] + [0] * rest, n_cols, bpow)
        regs = dict(regimes); regs[L] = reg
        for j in range(rest): regs[21 + j] = UDR
        lv = probe.get_pcs_security_levels(Mixed(F, regs))
        query_term = lv['fin'] if i == M - 1 else lv[f"Shift(i={i+1})"]
        qpow = max(0, TARGET - query_term)
        assert qpow <= LATER_POW, (label, i, qpow)
        queries.append(t); ldes.append(L); regimes[L] = reg; pows.append(qpow); fold_pows.append(fp); ood_pows.append(op)
        rows.append((p, L, k, lab, bpq, t, fp, op, qpow, query_term))
    w = build(log_degree, folds, queries, ldes, pows, fold_pows, ood_pows, n_cols, bpow)
    lv = w.get_pcs_security_levels(Mixed(F, regimes)); kk = min(lv, key=lv.get)
    real_batch = bits(UDR.get_error_powers(0.5, 2 ** msg_log2, n_cols)) + bpow
    print(f"\n### {label}")
    print(f"target 100; batched-polynomial ceiling {n_cols} -> batching PoW {bpow} bits (batching term {real_batch} bits, UDR, base code 2^{msg_log2} at rate 1/2)")
    print(f"soundcalc mixed total: {lv[kk]} bits (binding term {kk}){'  <-- base round kept as today: the base query term binds' if base_queries else ''}")
    bk = 'fold_log2 0 (virtual packing)' if virtual else 'fold_log2 1'
    print(f"base_round: lde_factor_log2 1, {bk}, num_queries {t0}, queries_pow_bits {base_pow}, folding_pow_bits 0, batching_pow_bits {bpow}  | regime UDR (delta 0.25, {bpq0:.3f} bits/query, ell 1) -> base query term {base_bits} bits; JBR not certifiable here (batching term 73-90 bits for any m within the PoW budget) and its delta at rate 1/2 is below UDR's")
    for j, (p, L, k, lab, bpq, t, fp, op, qpow, query_term) in enumerate(rows):
        needU = math.ceil((TARGET - LATER_POW) / -math.log2(1 - UDR.get_proximity_parameter(2.0**-L, 2**(p-1))))
        print(f"internal_round {j}: poly 2^{p}, lde_factor_log2 {L} (domain 2^{p+L}), folding_log2 {k}, num_queries {t}, queries_pow_bits {qpow} (query term {query_term} bits ungrinded), folding_pow_bits {max(fp)} (per sumcheck round {fp}), num_ood_samples 1, ood_pow_bits {op}  | regime {lab}, {bpq:.2f} bits/query; UDR here would need {needU} queries")
    if today: print(f"today: {today}")


if __name__ == "__main__":
    # The entries of `example_configs/ethproofs_soundcalc.rs`, keyed by (message size, virtual packing).
    # The committed-polynomial ceiling is the entry's `max_committed_polys`; it only sets the batching PoW.
    solve("2^23, fold_log2 1, ceiling 128 (unified_reduced_machine 106 columns, mul_div_unsigned 59)", 23, [1,5,5,5,4], 128, 28,
          today="folds [1,5,5,5,4], lde_log2 [4,9,14,19], queries [89,23,10,7,5], qPoW [26,24,25,19,21]")
    solve("2^24, fold_log2 1, ceiling 128 (add_sub, inits_and_teardowns, jump_branch, load_store x2, shift_binary: <= 68 columns)", 24, [1,5,5,5,4,3], 128, 28,
          today="folds [1,5,5,5,4,3], lde_log2 [4,9,14,19,19], queries [89,23,10,7,5,5], qPoW [26,24,25,19,21,21]")
    solve("2^22, virtual packing, ceiling 512 (bigint 260, keccak_* <= 274, blake2_g_function 121 columns; blake2_with_compression 769/4 = 194 packed)", 22, [0,6,5,5,5], 512, 28, virtual=True,
          today="virtual twin folds [0,6,5,5,5], lde_log2 [5,11,15,19], queries [89,15,8,6,5], qPoW [26,25,27,25,21]")
    solve("2^20, fold_log2 1, ceiling 1024 (blake2_with_extended_control test circuit, 769 columns)", 20, [1,5,5,4,4], 1024, 28,
          today="folds [1,5,5,4,4], lde_log2 [8,13,15,19], queries [89,11,7,6,5], qPoW [26,27,25,25,21]")
    solve("2^20, virtual packing, ceiling 1024 (blake2_with_extended_control test circuit)", 20, [0,6,5,4,4], 1024, 28, virtual=True,
          today="virtual twin folds [0,6,5,4,4], lde_log2 [7,13,15,19], queries [89,13,7,6,5], qPoW [26,27,25,25,21]")
    solve("2^23, fold_log2 1, base round kept at 89 queries / PoW 26 (what today's base round certifies)", 23, [1,5,5,5,4], 128, 26, base_queries=89)
