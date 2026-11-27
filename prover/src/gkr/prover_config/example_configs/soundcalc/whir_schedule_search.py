"""Mixed-regime 100-bit WHIR schedule search over ethereum/soundcalc, printing WhirSchedule fields.
Run: PYTHONPATH=<soundcalc clone> python3.11 whir_schedule_search.py   (python >= 3.9; soundcalc commit 2af5e7d)
The shapes under __main__ are the EthproofsSoundnessCalc entries of ../ethproofs_soundcalc.rs.
Constraints: BabyBear^4, sec 100, configurable base LDE and regime, ONE OOD sample per oracle (+ OOD PoW).
Folding PoW is capped at FOLD_CAP per sumcheck round. Each shape may override the LATER_POW cap
for query, OOD and batching PoW and supplies its base query PoW. Later query counts are sized against
the query cap, then the PoW is lowered to the smallest value that still reaches the target.
Virtual packing (fold_log2 = 0) is emulated with log_degree + 1 and k_0 = 1 (soundcalc needs k >= 1):
the batched polynomial of size 2^m is then re-committed as the first internal oracle at size 2^m,
which is exactly the virtual-packing shape; the emulated base code is 2x larger than the real one,
so the artificial base fold is excluded and the real batching term is recomputed directly."""
import argparse
from contextlib import redirect_stdout
import json
import math
from pathlib import Path
import subprocess
import sys

if not __debug__:
    sys.exit("Soundcalc certification requires Python assertions. Run without -O or PYTHONOPTIMIZE.")

import soundcalc

soundcalc_root = Path(soundcalc.__file__).resolve().parent.parent
soundcalc_revision = "2af5e7dfc01e4aef1bc0e544a3b75c1940b1dded"
head = subprocess.run(
    ["git", "-C", str(soundcalc_root), "rev-parse", "--show-toplevel", "HEAD"],
    capture_output=True, text=True,
)
if head.returncode or head.stdout.splitlines() != [str(soundcalc_root), soundcalc_revision]:
    sys.exit(f"Soundcalc certification requires the imported checkout at 2af5e7d (found at {soundcalc_root}).")

from soundcalc.common.fields import BABYBEAR_4, FieldParams
from soundcalc.pcs.whir import WHIR, WHIRConfig
from soundcalc.proxgaps.proxgaps_regime import ProximityGapsRegime
from soundcalc.proxgaps.johnson_bound import JohnsonBoundRegime
from soundcalc.proxgaps.unique_decoding import UniqueDecodingRegime
from soundcalc.common.utils import get_bits_of_security_from_error as bits

HASH_SIZE_BITS = 256
TARGET = 100; LATER_POW = 27; FOLD_CAP = 24; MAX_DOM = 27

def baby_bear_field(field_size):
    return FieldParams(BABYBEAR_4.name, BABYBEAR_4.p, 4, field_size, BABYBEAR_4.two_adicity)

F = baby_bear_field(2**128 / 81)

class Mixed(ProximityGapsRegime):
    """per-iteration regime (WHIR Theorem 5.2 has per-iteration delta_i / ell_i); keyed by iteration rate"""
    def __init__(self, field, by_rate): super().__init__(field); self.by_rate = by_rate
    def pick(self, r): return self.by_rate[round(-math.log2(r))]
    def identifier(self): return "mixed"
    def get_proximity_parameter(self, r, d): return self.pick(r).get_proximity_parameter(r, d)
    def get_max_list_size(self, r, d): return self.pick(r).get_max_list_size(r, d)
    def get_error_powers(self, r, d, b): return self.pick(r).get_error_powers(r, d, b)
    def get_error_linear(self, r, d): return self.pick(r).get_error_linear(r, d)
    def get_error_multilinear(self, r, d, b): return self.pick(r).get_error_multilinear(r, d, b)

def batch_pow(msg_log2, n_cols, base_lde_log2, field):   # = prover_config::pow_bits::pow_bits_for_batched_proximity
    bbits = (n_cols - 1).bit_length()
    field_bits = math.floor(math.log2(field.F))
    return max(0, TARGET - max(0, field_bits - (msg_log2 + base_lde_log2) - bbits))

def build(log_degree, folds, queries, ldes, pows, fold_pows, ood_pows, n_cols, bpow, base_lde_log2=1, *, field=None):
    M = len(folds)
    cfg = WHIRConfig(hash_size_bits=HASH_SIZE_BITS, log_inv_rate=base_lde_log2, num_iterations=M, folding_factors=folds, field=F if field is None else field,
        log_degree=log_degree, batch_size=n_cols, power_batching=True, grinding_batching_phase=bpow, constraint_degree=3,
        grinding_bits_folding=fold_pows, num_queries=queries, grinding_bits_queries=pows,
        num_ood_samples=[1]*(M-1), grinding_bits_ood=ood_pows)
    w = WHIR(cfg); rates = [base_lde_log2] + ldes; w.log_inv_rates = rates + [rates[-1]]; return w

def certify_baby_bear(schedule, message_log2, columns, regimes, field=F):
    base = schedule["base_round"]
    internal = schedule["internal_rounds"]
    rounds = [base, *internal]
    virtual = base["fold_log2"] == 0
    folds = [base["fold_log2"] or 1, *(r["folding_log2"] for r in internal)]
    rates = [r["lde_factor_log2"] for r in rounds]
    assert len(regimes) == len(set(rates)) == len(rounds)
    assert all(r["num_queries"] > 0 for r in rounds)
    assert all(r["num_ood_samples"] == 1 for r in internal)
    by_rate = {
        rate: (JohnsonBoundRegime(field, explicit_m=m) if m is not None
               else UniqueDecodingRegime(field))
        for rate, m in zip(rates, regimes)
    }
    batching_pow = base["batching_pow_bits"]
    whir = build(
        message_log2 + int(virtual), folds, [r["num_queries"] for r in rounds], rates[1:],
        [r["queries_pow_bits"] for r in rounds],
        [[r["folding_pow_bits"]] * fold for r, fold in zip(rounds, folds)],
        [r["ood_pow_bits"] for r in internal], columns, batching_pow, rates[0], field=field,
    )
    levels = whir.get_pcs_security_levels(Mixed(field, by_rate))
    if virtual:
        del levels["fold(i=0,s=1)"]
        error = by_rate[rates[0]].get_error_powers(2**-rates[0], 2**message_log2, columns)
        levels["batching"] = bits(error) + batching_pow
    assert levels and min(levels.values()) >= TARGET, levels
    return levels


def solve(label, msg_log2, folds, n_cols, base_pow, virtual=False,
          base_lde_log2=1, max_pow=LATER_POW, *, field=F, search_base_regimes=False,
          first_internal_lde_log2=None):
    assert base_pow <= max_pow
    assert msg_log2 + base_lde_log2 <= MAX_DOM
    log_degree = msg_log2 + (1 if virtual else 0)
    folds = ([1] + folds[1:]) if virtual else folds
    M = len(folds)
    polys = [log_degree - sum(folds[:i+1]) for i in range(M - 1)]
    base_rate = 2.0 ** -base_lde_log2
    udr = UniqueDecodingRegime(field)
    jbr = {m: JohnsonBoundRegime(field, explicit_m=m) for m in (3, 4, 5, 8, 12, 20)}
    base_regimes = [("UDR", udr)]
    if search_base_regimes:
        base_regimes.extend((f"JBR m={m}", reg) for m, reg in jbr.items())
    best = None
    for lab, reg in base_regimes:
        bpow = (batch_pow(msg_log2, n_cols, base_lde_log2, field) if reg is udr else
                max(0, TARGET - bits(reg.get_error_powers(base_rate, 2 ** msg_log2, n_cols))))
        fp = []
        for s in range(1, folds[0] + 1):
            ls = reg.get_max_list_size(base_rate, 2 ** (log_degree - s + 1))
            e = 3 * ls / field.F + reg.get_error_powers(base_rate, 2 ** (log_degree - s), 2)
            fp.append(max(0, TARGET - bits(e)))
        if bpow > max_pow or max(fp) > FOLD_CAP: continue
        bpq = -math.log2(1 - reg.get_proximity_parameter(base_rate, 2 ** (log_degree - 1)))
        t = math.ceil((TARGET - base_pow) / bpq)
        key = (t, bpow + max(fp))
        if best is None or key < best[0]: best = (key, lab, reg, bpow, fp, bpq, t)
    assert best, f'{label}: no base regime within the PoW caps'
    _, base_lab, base_reg, bpow, base_fp, bpq0, t0 = best
    base_bits = min(TARGET, math.floor(t0 * bpq0 + base_pow))
    queries, ldes, regimes, pows, fold_pows, ood_pows, rows = [t0], [], {base_lde_log2: base_reg}, [base_pow], [base_fp], [], []
    for i, p in enumerate(polys, start=1):
        k = folds[i]; best = None
        cands = [("UDR", udr, L) for L in range(2, MAX_DOM - p + 1)] + [(f"JBR m={m}", jbr[m], L) for m in jbr for L in range(2, MAX_DOM - p + 1)]
        for lab, reg, L in cands:
            if L in regimes: continue
            if i == 1 and first_internal_lde_log2 is not None and L != first_internal_lde_log2:
                continue
            rate = 2.0 ** -L
            bpq = -math.log2(1 - reg.get_proximity_parameter(rate, 2 ** (p - 1)))
            t = math.ceil((TARGET - max_pow) / bpq)
            fp = []
            for s in range(1, k + 1):
                ls = reg.get_max_list_size(rate, 2 ** (p - s + 1))
                e = 3 * ls / field.F + reg.get_error_powers(rate, 2 ** (p - s), 2)
                fp.append(max(0, TARGET - bits(e)))
            if max(fp) > FOLD_CAP: continue
            ls0 = reg.get_max_list_size(rate, 2 ** p)
            op = max(0, TARGET - bits(ls0 * ls0 * ((2 ** p) / (2 * field.F))))
            if op > max_pow: continue
            rest = M - 1 - i
            trial = build(log_degree, folds, queries + [t] + [80] * rest, ldes + [L] + [21 + j for j in range(rest)],
                          pows + [max_pow] * (rest + 1), fold_pows + [fp] + [[0] * folds[i + 1 + j] for j in range(rest)],
                          ood_pows + [op] + [0] * rest, n_cols, bpow, base_lde_log2, field=field)
            regs = dict(regimes); regs[L] = reg
            for j in range(rest): regs[21 + j] = udr
            lv = trial.get_pcs_security_levels(Mixed(field, regs))
            local = {kk: v for kk, v in lv.items() if kk.startswith(f"fold(i={i},") or kk == f"OOD(i={i})" or kk == f"Shift(i={i+1})" or (i == M - 1 and kk == 'fin')}
            if not all(v >= TARGET for v in local.values()): continue
            key = (t, max(fp) + op, -L)
            if best is None or key < best[0]: best = (key, lab, reg, L, fp, op, t, bpq)
        assert best, f"{label}: no option for oracle 2^{p}"
        _, lab, reg, L, fp, op, t, bpq = best
        # The query count was sized against the query cap; now take the SMALLEST query PoW that
        # still lifts this oracle's query term (Shift / fin) to the target: t * bits_per_query is
        # rarely a whole number of bits short of the target, and every spare bit is wasted grinding.
        rest = M - 1 - i
        probe = build(log_degree, folds, queries + [t] + [80] * rest, ldes + [L] + [21 + j for j in range(rest)],
                      pows + [0] * (rest + 1), fold_pows + [fp] + [[0] * folds[i + 1 + j] for j in range(rest)],
                      ood_pows + [op] + [0] * rest, n_cols, bpow, base_lde_log2, field=field)
        regs = dict(regimes); regs[L] = reg
        for j in range(rest): regs[21 + j] = udr
        lv = probe.get_pcs_security_levels(Mixed(field, regs))
        query_term = lv['fin'] if i == M - 1 else lv[f"Shift(i={i+1})"]
        qpow = max(0, TARGET - query_term)
        assert qpow <= max_pow, (label, i, qpow)
        queries.append(t); ldes.append(L); regimes[L] = reg; pows.append(qpow); fold_pows.append(fp); ood_pows.append(op)
        rows.append((p, L, k, lab, bpq, t, fp, op, qpow, query_term))
    base = dict(lde_factor_log2=base_lde_log2, fold_log2=0 if virtual else folds[0],
                num_queries=t0, queries_pow_bits=base_pow, folding_pow_bits=0 if virtual else max(base_fp),
                batching_pow_bits=bpow)
    internal = [
        dict(lde_factor_log2=L, folding_log2=k, num_queries=t, queries_pow_bits=qpow,
             folding_pow_bits=max(fp), num_ood_samples=1, ood_pow_bits=op)
        for _, L, k, _, _, t, fp, op, qpow, _ in rows
    ]
    schedule = dict(base_round=base, internal_rounds=internal)
    multiplicities = {reg: m for m, reg in jbr.items()}
    ms = [multiplicities.get(reg) for reg in regimes.values()]
    lv = certify_baby_bear(schedule, msg_log2, n_cols, ms, field)
    kk = min(lv, key=lv.get)
    print(f"\n### {label}")
    print(f"target 100; batched-polynomial ceiling {n_cols} -> batching PoW {bpow} bits (batching term {lv['batching']} bits, {base_lab}, base code 2^{msg_log2} at rate 1/{2 ** base_lde_log2})")
    print(f"soundcalc minimum: {lv[kk]} bits (binding term {kk})")
    bk = 'fold_log2 0 (virtual packing)' if virtual else f'fold_log2 {folds[0]}'
    delta = base_reg.get_proximity_parameter(base_rate, 2 ** (log_degree - 1))
    ell = base_reg.get_max_list_size(base_rate, 2 ** log_degree)
    print(f"base_round: lde_factor_log2 {base_lde_log2}, {bk}, num_queries {t0}, queries_pow_bits {base_pow}, folding_pow_bits {base['folding_pow_bits']}, batching_pow_bits {bpow}  | regime {base_lab} (delta {delta:g}, {bpq0:.3f} bits/query, ell {ell:g}) -> base query term {base_bits} bits")
    analysis = []
    for j, (p, L, k, lab, bpq, t, fp, op, qpow, query_term) in enumerate(rows):
        needU = math.ceil((TARGET - max_pow) / -math.log2(1 - udr.get_proximity_parameter(2.0**-L, 2**(p-1))))
        print(f"internal_round {j}: poly 2^{p}, lde_factor_log2 {L} (domain 2^{p+L}), folding_log2 {k}, num_queries {t}, queries_pow_bits {qpow} (query term {query_term} bits ungrinded), folding_pow_bits {max(fp)} (per sumcheck round {fp}), num_ood_samples 1, ood_pow_bits {op}  | regime {lab}, {bpq:.2f} bits/query; UDR here would need {needU} queries")
        analysis.append(dict(bits_per_query=bpq, unique_decoding_queries=needU,
                             folding_pow_bits_per_step=fp))
    return dict(message_log2=msg_log2, columns=n_cols, schedule=schedule, multiplicities=ms,
                analysis=analysis, binding_term=kk, levels=lv)


def standard_schedules():
    return [
        solve("2^23, ceiling 128", 23, [1, 5, 5, 5, 4], 128, 26,
              max_pow=26, first_internal_lde_log2=3),
        solve("2^24, ceiling 128", 24, [1, 5, 5, 5, 4, 3], 128, 26,
              max_pow=26, first_internal_lde_log2=2),
        solve("2^22, virtual packing, ceiling 512", 22, [0, 6, 5, 5, 5], 512, 26,
              max_pow=26, first_internal_lde_log2=3, virtual=True),
        solve("2^20, ceiling 1024", 20, [1, 5, 5, 4, 4], 1024, 27),
        solve("2^20, virtual packing, ceiling 1024", 20, [0, 6, 5, 4, 4], 1024, 27, virtual=True),
    ]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit the schedules and certificates as JSON")
    args = parser.parse_args()
    with redirect_stdout(sys.stderr if args.json else sys.stdout):
        schedules = standard_schedules()
        schedules.append(solve("2^23, base LDE 2^3, ceiling 128, compression",
                               23, [1, 5, 5, 5, 4], 128, 25, base_lde_log2=3, max_pow=25,
                               search_base_regimes=True))
    if args.json:
        print(json.dumps(schedules, indent=2))
