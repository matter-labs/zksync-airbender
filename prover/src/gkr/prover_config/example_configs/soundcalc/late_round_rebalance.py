"""Rebalance the PessimisticConjecture ladders' LATE rounds under the Johnson bound.

Run: PYTHONPATH=<soundcalc clone> python3 late_round_rebalance.py   (python >= 3.9; soundcalc commit 2af5e7d)

Under soundcalc's Johnson-bound regime (BCHKS25, explicit multiplicity m, slack eta = sqrt(rho)/(2m))
the ladders' base round (rate 1/2, 89 queries, 26 bits of query PoW) is worth 60-70 bits, but the
last oracles sit at rate 2^-19 on 2^24..2^27 domains, where the fold term
    3 * ell / |F| + (m + 1/2)^5 * n / (2 rho^1.5 |F|)        (ell ~ list size, n = domain size)
and the OOD term ell^2 * 2^poly / (2 |F|) collapse to 50-55 bits: the list size and the 1/rate factors
grow much faster than the bits a query buys (~ log2(1/rate) / 2 under the Johnson bound).

The delegation circuits (bigint, keccak x4, blake2_g_function: 2^22 traces; blake2_with_compression: a 2^20
trace packed by 2^2) all run the VIRTUAL-PACKING twin of the 2^22 ladder (`WhirSchedule::to_virtual_packing`:
round-0 fold 0, oracle 1 at half the LDE with one more fold step and the pessimistic rule's query count).
soundcalc needs k_0 >= 1, so that twin is emulated as a 2^23 message with a round-0 fold of 1, whose first
oracle is exactly the re-committed 2^22 batched polynomial; the emulated base code is 2x the real one, so the
base fold term is 1 bit conservative, and the batching term is recomputed on the real base code. The column
ceilings of those shapes (512: keccak_special5 has 274 columns; 256: blake2_with_compression 769/4 = 194
packed) set their batching PoW.

This driver keeps the base round and every fold step as they are (same polynomial sizes), and for each
later oracle searches a SMALLER LDE factor, a multiplicity and a query count such that all of the
oracle's terms (fold per sumcheck round, OOD, query/shift) reach the base round's level T, with the
query PoW of the ladder unchanged and no folding / OOD PoW (the pessimistic mode has none). The query
count also keeps the ladder's own pessimistic-conjecture accounting (t >= 1.2 * (100 - pow) / lde_log2),
so the proposed schedule is still a 100-bit ladder under the in-house rule.
"""
import math
from soundcalc.common.fields import BABYBEAR_4 as F
from soundcalc.pcs.whir import WHIR, WHIRConfig
from soundcalc.proxgaps.proxgaps_regime import ProximityGapsRegime
from soundcalc.proxgaps.johnson_bound import JohnsonBoundRegime
from soundcalc.common.utils import get_bits_of_security_from_error as bits

MAX_DOM = 27          # largest oracle domain the prover handles (2^27)
MS = (3, 4, 5, 8, 12, 20, 50)
JBR = {m: JohnsonBoundRegime(F, explicit_m=m) for m in MS}

# label: message_log2, folds, queries, intermediate LDE factors (log2), per-round query PoW, column ceiling,
# virtual packing   (base LDE 2)
# These are the ladders BEFORE the 2026-10-27 rebalance (the driver's input); the rebalanced
# ones it prints are the ladders in pessimistic_conjecture.rs since then.
SHAPES = [
    ("2^20, fold 1, 114 columns", 20, [1, 5, 5, 4, 4], [89, 11, 7, 6, 5], [8, 13, 15, 19], [26, 27, 25, 25, 21], 114, False),
    ("2^21, fold 1, 114 columns", 21, [1, 5, 5, 5, 4], [89, 15, 8, 6, 5], [6, 11, 15, 19], [26, 25, 27, 25, 21], 114, False),
    ("2^22, fold 1, 114 columns", 22, [1, 5, 5, 5, 5], [89, 15, 8, 6, 5], [6, 11, 15, 19], [26, 25, 27, 25, 21], 114, False),
    ("2^23, fold 1, 114 columns (unified_reduced_machine, mul_div_unsigned)", 23, [1, 5, 5, 5, 4], [89, 23, 10, 7, 5], [4, 9, 14, 19], [26, 24, 25, 19, 21], 114, False),
    ("2^24, fold 1, 114 columns (add_sub, inits_and_teardowns, jump_branch, load_store x2, shift_binary)", 24, [1, 5, 5, 5, 4, 3], [89, 23, 10, 7, 5, 5], [4, 9, 14, 19, 19], [26, 24, 25, 19, 21, 21], 114, False),
    # the delegation circuits: the virtual twin of the 2^22 ladder (queries [89, 18, 8, 6, 5], ldes [5, 11, 15, 19], folds [0, 6, 5, 5, 5])
    ("2^22, VIRTUAL packing, 512 columns (bigint 260, keccak x4 <= 274, blake2_g_function 121)", 22, [0, 6, 5, 5, 5], [89, 18, 8, 6, 5], [5, 11, 15, 19], [26, 25, 27, 25, 21], 512, True),
    ("2^22, VIRTUAL packing, 256 columns (blake2_with_compression: 2^20 trace packed 2^2, 769/4 = 194 columns)", 22, [0, 6, 5, 5, 5], [89, 18, 8, 6, 5], [5, 11, 15, 19], [26, 25, 27, 25, 21], 256, True),
]


class Mixed(ProximityGapsRegime):
    """per-iteration regime (WHIR Thm 5.2 has per-iteration delta_i / ell_i), keyed by the oracle's rate"""
    def __init__(self, field, by_rate): super().__init__(field); self.by_rate = by_rate
    def pick(self, r): return self.by_rate[round(-math.log2(r))]
    def identifier(self): return "mixed"
    def get_proximity_parameter(self, r, d): return self.pick(r).get_proximity_parameter(r, d)
    def get_max_list_size(self, r, d): return self.pick(r).get_max_list_size(r, d)
    def get_error_powers(self, r, d, b): return self.pick(r).get_error_powers(r, d, b)
    def get_error_linear(self, r, d): return self.pick(r).get_error_linear(r, d)
    def get_error_multilinear(self, r, d, b): return self.pick(r).get_error_multilinear(r, d, b)


def batch_pow(n, n_cols):  # = prover_config::pow_bits::pow_bits_for_batched_proximity (message 2^n, base LDE 2)
    return max(0, 100 - max(0, 123 - (n + 1) - (n_cols - 1).bit_length()))


def build(n, folds, queries, ldes, pows, n_cols, bpow):
    """`n` and `folds` are the soundcalc shape (a virtual twin is passed already emulated)"""
    M = len(folds)
    cfg = WHIRConfig(hash_size_bits=256, log_inv_rate=1, num_iterations=M, folding_factors=folds, field=F,
                     log_degree=n, batch_size=n_cols, power_batching=True, grinding_batching_phase=bpow,
                     constraint_degree=3, grinding_bits_folding=[[0] * k for k in folds], num_queries=queries,
                     grinding_bits_queries=pows, num_ood_samples=[1] * (M - 1), grinding_bits_ood=[0] * (M - 1))
    w = WHIR(cfg)
    rates = [1] + ldes
    w.log_inv_rates = rates + [rates[-1]]
    return w


def oracle_terms(lv, i, M):
    """the terms oracle i (iteration i) is responsible for: its folds, its OOD sample, its queries"""
    t = {k: v for k, v in lv.items() if k.startswith(f"fold(i={i},")}
    if i > 0:
        t[f"OOD(i={i})"] = lv[f"OOD(i={i})"]
    t["queries"] = lv["fin"] if i == M - 1 else lv[f"Shift(i={i+1})"]
    if i == 0:
        t["batching"] = lv["batching"]
    return t


def evaluate(n, folds, queries, ldes, pows, regimes, n_cols, bpow):
    w = build(n, folds, queries, ldes, pows, n_cols, bpow)
    return w, w.get_pcs_security_levels(Mixed(F, regimes))


def pessimistic_queries(L, pow_bits):  # PessimisticConjectureMode: ceil(1.2 * (100 - pow) / log2(1/rate))
    return math.ceil(1.2 * (100 - pow_bits) / L)


def bits_per_query(w, i, regime):
    return -math.log2(1 - w._get_delta_for_iteration(i, regime))


def rebalance(label, msg, folds, queries, ldes, pows, n_cols, virtual):
    bpow = batch_pow(msg, n_cols)
    # soundcalc shape: a virtual twin (round-0 fold 0) is emulated as a message one bit larger with a fold of 1
    n = msg + 1 if virtual else msg
    folds = ([1] + folds[1:]) if virtual else folds
    M = len(folds)
    polys = [n - sum(folds[:i + 1]) for i in range(M - 1)]      # committed intermediate polynomial sizes
    ev = lambda q, l, regs: evaluate(n, folds, q, l, pows, regs, n_cols, bpow)

    # ---- the base round: the best multiplicity for the rate-1/2 code sets the target ----
    best = None
    for m0 in MS:
        regs = {1: JBR[m0]}
        for L in ldes: regs.setdefault(L, JBR[m0])
        _, lv = ev(queries, ldes, regs)
        t0 = oracle_terms(lv, 0, M)
        if virtual:  # the real base code is the 2^msg message at rate 1/2 (the emulation doubles it)
            t0["batching"] = bits(JBR[m0].get_error_powers(0.5, 2 ** msg, n_cols)) + bpow
        if best is None or min(t0.values()) > best[0]:
            best = (min(t0.values()), m0, t0)
    T, m0, base_terms = best
    print(f"\n=== {label}: folds {folds if not virtual else [0] + folds[1:]}, today queries {queries}, lde_log2 {ldes}, query PoW {pows}, batching PoW {bpow}"
          + (f"  (soundcalc shape: 2^{n} message, folds {folds})" if virtual else ""))
    print(f"base round (rate 1/2, {queries[0]} queries, PoW {pows[0]}) under JBR m={m0}: " +
          ", ".join(f"{k} {v}" for k, v in base_terms.items()) + f"  -> target T = {T} bits")

    # ---- today's later oracles, each at its own best multiplicity ----
    today = []
    for i in range(1, M):
        bi = None
        for m in MS:
            # oracle i's own terms under its own multiplicity (a uniform regime: the Mixed regime is
            # keyed by rate, and today's 2^24 ladder repeats the 2^-19 rate on its last two oracles)
            regs = {L: JBR[m] for L in set([1] + ldes)}
            _, lv = ev(queries, ldes, regs)
            ti = oracle_terms(lv, i, M)
            if bi is None or min(ti.values()) > bi[0]:
                bi = (min(ti.values()), m, ti)
        today.append(bi)
        print(f"  today oracle {i}: poly 2^{polys[i-1]}, lde_log2 {ldes[i-1]} (domain 2^{polys[i-1]+ldes[i-1]}), {queries[i]} queries, PoW {pows[i]} | best m={bi[1]}: " +
              ", ".join(f"{k} {v}" for k, v in bi[2].items()) + f"  -> {bi[0]} bits")

    # ---- rebalance: smallest query count (then smallest LDE) per oracle reaching T on every term ----
    new_ldes, new_queries, regimes = [], [queries[0]], {1: JBR[m0]}
    rows, rows_frontier = [], []
    for i in range(1, M):
        p = polys[i - 1]
        k = folds[i]
        cands = []
        for L in range(2, min(ldes[i - 1], MAX_DOM - p) + 1):
            for m in MS:
                if L in regimes and regimes[L] is not JBR[m]:
                    continue  # the Mixed regime is keyed by rate: a repeated rate keeps its multiplicity
                rest = M - 1 - i
                trial_ldes = new_ldes + [L] + ldes[i:]
                regs = dict(regimes); regs[L] = JBR[m]
                for L2 in ldes[i:]: regs.setdefault(L2, JBR[m0])
                # query count: the pessimistic rule, then lifted until the JBR query term reaches T
                t = pessimistic_queries(L, pows[i])
                w = build(n, folds, new_queries + [t] + queries[i + 1:], trial_ldes, pows, n_cols, bpow)
                bpq = bits_per_query(w, i, Mixed(F, regs))
                t = max(t, math.ceil((T - pows[i]) / bpq))
                ok = None
                for _ in range(6):  # the shift term has a small list-size part: lift t a little if needed
                    _, lv = ev(new_queries + [t] + queries[i + 1:], trial_ldes, regs)
                    ti = oracle_terms(lv, i, M)
                    if min(ti.values()) >= T:
                        ok = ti; break
                    if any(v < T for kk, v in ti.items() if kk != "queries"):
                        break  # fold / OOD terms do not depend on t
                    t += 1
                if ok is None:
                    continue
                cands.append((t, L, m, ok, bpq))
        assert cands, f"{label} oracle {i}: no LDE factor <= today's reaches {T} bits"
        # the trade-off frontier of this oracle: per LDE factor, the fewest queries reaching T
        frontier = {}
        for t, L, m, _terms, _bpq in cands:
            if L not in frontier or t < frontier[L][0]:
                frontier[L] = (t, m)
        rows_frontier.append((i, p, sorted(frontier.items())))
        t, L, m, terms, bpq = min(cands, key=lambda c: (c[0], c[1]))
        new_ldes.append(L); new_queries.append(t); regimes[L] = JBR[m]
        rows.append((i, p, k, L, m, t, terms, bpq))
    w, lv = ev(new_queries, new_ldes, regimes)
    if virtual:
        lv["batching"] = bits(JBR[m0].get_error_powers(0.5, 2 ** msg, n_cols)) + bpow
    total = min(lv.values()); binding = min(lv, key=lv.get)
    print(f"  rebalanced (base round and folds unchanged, query PoW unchanged): queries {new_queries}, lde_log2 {new_ldes}; "
          f"soundcalc JBR total {total} bits (binding {binding})")
    for i, p, k, L, m, _t, terms, bpq in rows:
        print(f"    oracle {i}: poly 2^{p}, lde_log2 {L} (domain 2^{p+L}, was 2^{p+ldes[i-1]}), folding_log2 {k}, {new_queries[i]} queries (was {queries[i]}; "
              f"pessimistic rule needs {pessimistic_queries(L, pows[i])}), PoW {pows[i]} | JBR m={m}, {bpq:.2f} bits/query: " +
              ", ".join(f"{kk} {v}" for kk, v in terms.items()))
    for i, p, fr in rows_frontier:
        print(f"    frontier oracle {i} (poly 2^{p}, PoW {pows[i]}): " +
              ", ".join(f"lde 2^{L}: {t} q (m={m})" for L, (t, m) in fr))
    # cost proxies: prover LDE work ~ sum of intermediate oracle domains; verifier ~ opened leaf values
    dom_old = sum(2 ** (polys[j] + ldes[j]) for j in range(M - 1))
    dom_new = sum(2 ** (polys[j] + new_ldes[j]) for j in range(M - 1))
    vals_old = sum(queries[i] * 2 ** folds[i] for i in range(1, M))
    vals_new = sum(new_queries[i] * 2 ** folds[i] for i in range(1, M))
    print(f"  cost: intermediate oracle domains {dom_old / 2**20:.1f}M -> {dom_new / 2**20:.1f}M points "
          f"({100 * (dom_new / dom_old - 1):+.0f}%); opened intermediate leaf values {vals_old} -> {vals_new} ({100 * (vals_new / vals_old - 1):+.0f}%)")
    steps = ([0] + folds[1:]) if virtual else folds
    print(f"  WhirSchedule rows: queries {new_queries}, lde_factors {[1 << L for L in new_ldes]}, pows {pows}, steps {steps}")


if __name__ == "__main__":
    for shape in SHAPES:
        rebalance(*shape)
