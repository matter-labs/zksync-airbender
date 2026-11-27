# WHIR schedule notes — `EthproofsSoundnessCalc`, `sec_100`, 2^24 committed polynomials, two values per column per leaf (add_sub_lui_auipc_mop, inits_and_teardowns, jump_branch_slt, load_store_subword_only, load_store_word_only, shift_binary)

Certified by `ethereum/soundcalc` (commit `2af5e7d`, 2026-09-21), WHIR PCS module only (WHIR Theorem 5.2 with the BCHKS25 proximity-gap bounds): **100 bits**, binding term `fold(i=0,s=1)`; every other term is at or above the target and several Johnson-bound terms sit exactly on it, so any change of a domain, a fold or the committed-polynomial ceiling needs a re-run of `prover/src/gkr/prover_config/example_configs/soundcalc/whir_schedule_search.py`. Model inputs: BabyBear⁴ challenges with effective denominator 2^128/81, 256-bit hashes, powers batching, constraint degree 3 (soundcalc's minimum; ours is 2), our explicit per-oracle LDE factors, one OOD sample per internal oracle.

## This circuit

- committed polynomials entering WHIR: **65** (from the compiled circuit; physical packing 2^0, two values per column per base leaf), certified ceiling 128 → batching PoW 11 bits
- committed polynomial size 2^24 at the base rate 2^-1 (domain 2^25)

## Rounds

| oracle | poly | LDE | domain | fold | queries | query PoW | folding PoW (per step) | OOD PoW | regime | bits/query | UDR would need |
|---|---|---|---|---|---|---|---|---|---|---|---|
| base | 2^24 | 2^1 | 2^25 | 1 | 179 | 26 | 1 | – | unique decoding (δ = (1 − ρ)/2 = 0.250, list size 1) | 0.415 | 179 |
| 0 | 2^23 | 2^2 | 2^25 | 5 | 79 | 26 | 23 [23, 22, 21, 20, 19] | 10 | Johnson bound, m = 12 (η = √ρ/(2m) = 0.0208, δ = 1 − √ρ − η = 0.479, list size 25.0) | 0.94 | 110 |
| 1 | 2^18 | 2^8 | 2^26 | 5 | 20 | 25 | 24 [24, 23, 22, 21, 20] | 7 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0104, δ = 1 − √ρ − η = 0.927, list size 56.0) | 3.78 | 75 |
| 2 | 2^13 | 2^10 | 2^23 | 5 | 16 | 24 | 24 [24, 23, 22, 21, 20] | 4 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0052, δ = 1 − √ρ − η = 0.964, list size 112.0) | 4.78 | 75 |
| 3 | 2^8 | 2^12 | 2^20 | 4 | 13 | 25 | 24 [24, 23, 22, 21] | 1 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0026, δ = 1 − √ρ − η = 0.982, list size 224.0) | 5.78 | 75 |
| 4 | 2^4 | 2^13 | 2^17 | 3 | 12 | 25 | 23 [23, 22, 21] | 0 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0018, δ = 1 − √ρ − η = 0.987, list size 316.8) | 6.28 | 75 |

Plain-text tail: the 2^1 polynomial.

## Why

- base: unique decoding at rate 1/2 with 179 queries at 26 PoW bits; one bit of folding PoW brings the base fold to 100 bits
- oracle 0: LDE 2^2 keeps the first internal commitment at domain 2^25; m = 12 gives 0.94 bits/query within the folding PoW cap
- oracle 1: m = 3 minimises the Johnson folding term; LDE 2^8 keeps the domain at 2^26 within the folding PoW cap
- oracle 2: m = 3 minimises the Johnson folding term; LDE 2^10 keeps the domain at 2^23 within the folding PoW cap
- oracle 3: m = 3 minimises the Johnson folding term; LDE 2^12 keeps the domain at 2^20 within the folding PoW cap
- oracle 4: m = 3 minimises the Johnson folding term; LDE 2^13 keeps the domain at 2^17 within the folding PoW cap

`folding_pow_bits` is one value for every folding-challenge draw of an oracle; the analysis needs one bit less per sumcheck step (listed per step above), so the schedule grinds slightly more than the certification requires.

