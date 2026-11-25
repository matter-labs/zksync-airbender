# WHIR schedule notes — `EthproofsSoundnessCalc`, `sec_100`, 2^23 committed polynomials, two values per column per leaf (unified_reduced_machine, mul_div_unsigned)

Certified by `ethereum/soundcalc` (commit `2af5e7d`, 2026-09-21), WHIR PCS module only (WHIR Theorem 5.2 with the BCHKS25 proximity-gap bounds): **100 bits**, binding term `fold(i=0,s=1)`; every other term is at or above the target and several Johnson-bound terms sit exactly on it, so any change of a domain, a fold or the committed-polynomial ceiling needs a re-run of `prover/src/gkr/prover_config/example_configs/soundcalc/whir_schedule_search.py`. Model inputs: BabyBear⁴ challenges with effective denominator 2^128/81, 256-bit hashes, powers batching, constraint degree 3 (soundcalc's minimum; ours is 2), our explicit per-oracle LDE factors, one OOD sample per internal oracle.

## This circuit

- committed polynomials entering WHIR: **106** (from the compiled circuit; physical packing 2^0, two values per column per base leaf), certified ceiling 128 → batching PoW 10 bits
- committed polynomial size 2^23 at the base rate 2^-1 (domain 2^24)

## Rounds

| oracle | poly | LDE | domain | fold | queries | query PoW | folding PoW (per step) | OOD PoW | regime | bits/query | UDR would need |
|---|---|---|---|---|---|---|---|---|---|---|---|
| base | 2^23 | 2^1 | 2^24 | 1 | 179 | 26 | 0 | – | unique decoding (δ = (1 − ρ)/2 = 0.250, list size 1) | 0.415 | 179 |
| 0 | 2^22 | 2^3 | 2^25 | 5 | 53 | 26 | 22 [22, 21, 20, 19, 18] | 9 | Johnson bound, m = 8 (η = √ρ/(2m) = 0.0221, δ = 1 − √ρ − η = 0.624, list size 24.0) | 1.41 | 90 |
| 1 | 2^17 | 2^8 | 2^25 | 5 | 20 | 25 | 23 [23, 22, 21, 20, 19] | 6 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0104, δ = 1 − √ρ − η = 0.927, list size 56.0) | 3.78 | 75 |
| 2 | 2^12 | 2^10 | 2^22 | 5 | 16 | 24 | 23 [23, 22, 21, 20, 19] | 3 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0052, δ = 1 − √ρ − η = 0.964, list size 112.0) | 4.78 | 75 |
| 3 | 2^7 | 2^12 | 2^19 | 4 | 13 | 25 | 23 [23, 22, 21, 20] | 0 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0026, δ = 1 − √ρ − η = 0.982, list size 224.0) | 5.78 | 75 |

Plain-text tail: the 2^3 polynomial.

## Why

- base: unique decoding at rate 1/2 keeps powers batching within the PoW budget; 179 queries at 26 PoW bits reach 100 bits for the base query term
- oracle 0: LDE 2^3 keeps the largest internal commitment at domain 2^25; m = 8 gives 1.41 bits/query within the folding PoW cap
- oracle 1: m = 3 minimises the Johnson folding term; LDE 2^8 keeps the domain at 2^25 within the folding PoW cap
- oracle 2: m = 3 minimises the Johnson folding term; LDE 2^10 keeps the domain at 2^22 within the folding PoW cap
- oracle 3: m = 3 minimises the Johnson folding term; LDE 2^12 keeps the domain at 2^19 within the folding PoW cap

`folding_pow_bits` is one value for every folding-challenge draw of an oracle; the analysis needs one bit less per sumcheck step (listed per step above), so the schedule grinds slightly more than the certification requires.

