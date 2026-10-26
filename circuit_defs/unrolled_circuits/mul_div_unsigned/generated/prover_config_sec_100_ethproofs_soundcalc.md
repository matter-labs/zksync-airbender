# WHIR schedule notes — `EthproofsSoundnessCalc`, `sec_100`, 2^23 committed polynomials, two values per column per leaf (unified_reduced_machine, mul_div_unsigned)

Certified by `ethereum/soundcalc` (commit `2af5e7d`, 2026-09-21), WHIR PCS module only (WHIR Theorem 5.2 with the BCHKS25 proximity-gap bounds): **100 bits**, binding term `OOD(i=1)`; every other term is at or above the target and several Johnson-bound terms sit exactly on it, so any change of a domain, a fold or the committed-polynomial ceiling needs a re-run of `prover/src/gkr/prover_config/example_configs/soundcalc/whir_schedule_search.py`. Model inputs: BabyBear⁴ challenge field (|F| ≈ 2^123.6), 256-bit hashes, powers batching, constraint degree 3 (soundcalc's minimum; ours is 2), our explicit per-oracle LDE factors, one OOD sample per oracle. The GKR circuit layer is outside the model (105–118 bits by our own field-size accounting).

## This circuit

- committed polynomials entering WHIR: **59** (from the compiled circuit; physical packing 2^0, two values per column per base leaf), certified ceiling 128 → batching PoW 8 bits (computed for the ceiling with `pow_bits_for_batched_proximity`; batching term 102 bits under unique decoding)
- committed polynomial size 2^23 at the base rate 2^-1 (domain 2^24)

## Rounds

| oracle | poly | LDE | domain | fold | queries | query PoW | folding PoW (per step) | OOD PoW | regime | bits/query | UDR would need |
|---|---|---|---|---|---|---|---|---|---|---|---|
| base | 2^23 | 2^1 | 2^24 | 1 | 174 | 28 | 0 | – | unique decoding (δ = (1 − ρ)/2 = 0.250, list size 1) | 0.415 | 174 |
| 0 | 2^22 | 2^5 | 2^27 | 5 | 31 | 27 | 22 [22, 21, 20, 19, 18] | 8 | Johnson bound, m = 5 (η = √ρ/(2m) = 0.0177, δ = 1 − √ρ − η = 0.806, list size 31.1) | 2.36 | 77 |
| 1 | 2^17 | 2^9 | 2^26 | 5 | 18 | 24 | 24 [24, 23, 22, 21, 20] | 5 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0074, δ = 1 − √ρ − η = 0.948, list size 79.2) | 4.28 | 74 |
| 2 | 2^12 | 2^11 | 2^23 | 5 | 14 | 27 | 24 [24, 23, 22, 21, 20] | 2 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0037, δ = 1 − √ρ − η = 0.974, list size 158.4) | 5.28 | 74 |
| 3 | 2^7 | 2^13 | 2^20 | 4 | 12 | 25 | 24 [24, 23, 22, 21] | 0 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0018, δ = 1 − √ρ − η = 0.987, list size 316.8) | 6.28 | 74 |

Plain-text tail: the 2^3 polynomial.

## Why

- base: unique decoding is the only regime certifiable at rate 1/2: the Johnson-bound batching term of the committed columns is 73–90 bits for any multiplicity and cannot be lifted within any sane batching PoW, and the Johnson radius at rate 1/2 (0.28–0.48 bits/query) is below the unique-decoding one (0.415) anyway; 174 queries at 28 PoW bits put the base query term at exactly 100 bits (no folding PoW needed: the unique-decoding fold term is above 100 by itself)
- oracle 0: LDE 2^5 as in the ladder (domain 2^27); rate 2^-5 is still moderate, so m = 5 (above the floor) buys 2.36 bits/query at a 22-bit folding grind — 31 queries where unique decoding would need 77; the OOD term of this largest oracle needs 8 PoW bits with a single sample
- oracle 1: m = 3 (the theorem's floor) minimises the (m + 1/2)^5 fold term; LDE 2^9 (the ladder's) keeps the domain at 2^26 where the fold grind is 24 bits; 4.28 bits/query
- oracle 2: m = 3; LDE cut from the ladder's 2^14 to 2^11 so the 2^23 domain keeps the fold grind at 24 bits; 5.28 bits/query
- oracle 3: m = 3; LDE cut from the ladder's 2^19 to 2^13 (domain 2^20) so 24 bits of fold grind suffice; 6.28 bits/query, the OOD term needs no grind

`folding_pow_bits` is one value for every folding-challenge draw of an oracle; the analysis needs one bit less per sumcheck step (listed per step above), so the schedule grinds slightly more than the certification requires.

## Against the pessimistic-conjecture ladder

ladder: folds [1,5,5,5,4], LDE log2 [4,9,14,19], queries [89,23,10,7,5], query PoW [26,24,25,19,21], no folding / OOD PoW.

The base round cannot stay at the ladder's 89 queries / 26 PoW bits: under both accepted regimes a query into the rate-1/2 base oracle is worth at most 0.415 bits, so that base round certifies 62 bits whatever the later rounds do; 100 bits need ceil((100 − 28) / 0.415) = 174 queries at 28 PoW bits with the base LDE factor and round-0 fold unchanged. The later oracles' LDE factors are cut because the Johnson-bound fold term grows with n / ρ^1.5 and must stay within a 24-bit folding grind.
