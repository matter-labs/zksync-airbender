# WHIR schedule notes — `EthproofsSoundnessCalc`, `sec_100`, 2^22 committed polynomials, virtual packing (bigint_with_control, keccak_chi5, keccak_column_parity, keccak_special5, keccak_theta_rho, blake2_g_function unpacked; blake2_with_compression packed by 2^2)

Certified by `ethereum/soundcalc` (commit `2af5e7d`, 2026-09-21), WHIR PCS module only (WHIR Theorem 5.2 with the BCHKS25 proximity-gap bounds): **100 bits**, binding term `OOD(i=1)`; every other term is at or above the target and several Johnson-bound terms sit exactly on it, so any change of a domain, a fold or the committed-polynomial ceiling needs a re-run of `prover/src/gkr/prover_config/example_configs/soundcalc/whir_schedule_search.py`. Model inputs: BabyBear⁴ challenge field (|F| ≈ 2^123.6), 256-bit hashes, powers batching, constraint degree 3 (soundcalc's minimum; ours is 2), our explicit per-oracle LDE factors, one OOD sample per oracle. The GKR circuit layer is outside the model (105–118 bits by our own field-size accounting).

## This circuit

- committed polynomials entering WHIR: **200** (from the compiled circuit; physical packing 2^0, virtual packing: one value per column per base leaf, no round-0 sumcheck), certified ceiling 512 → batching PoW 9 bits (computed for the ceiling with `pow_bits_for_batched_proximity`; batching term 102 bits under unique decoding)
- committed polynomial size 2^22 at the base rate 2^-1 (domain 2^23)

## Rounds

| oracle | poly | LDE | domain | fold | queries | query PoW | folding PoW (per step) | OOD PoW | regime | bits/query | UDR would need |
|---|---|---|---|---|---|---|---|---|---|---|---|
| base | 2^22 | 2^1 | 2^23 | 0 | 179 | 26 | 0 | – | unique decoding (δ = (1 − ρ)/2 = 0.250, list size 1) | 0.415 | 179 |
| 0 | 2^22 | 2^3 | 2^25 | 6 | 52 | 26 | 23 [23, 22, 21, 20, 19, 18] | 8 | Johnson bound, m = 12 (η = √ρ/(2m) = 0.0147, δ = 1 − √ρ − η = 0.632, list size 35.4) | 1.44 | 88 |
| 1 | 2^16 | 2^9 | 2^25 | 5 | 18 | 24 | 23 [23, 22, 21, 20, 19] | 4 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0074, δ = 1 − √ρ − η = 0.948, list size 79.2) | 4.28 | 74 |
| 2 | 2^11 | 2^11 | 2^22 | 5 | 15 | 21 | 23 [23, 22, 21, 20, 19] | 1 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0037, δ = 1 − √ρ − η = 0.974, list size 158.4) | 5.28 | 74 |
| 3 | 2^6 | 2^13 | 2^19 | 5 | 12 | 25 | 23 [23, 22, 21, 20, 19] | 0 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0018, δ = 1 − √ρ − η = 0.987, list size 316.8) | 6.28 | 74 |

Plain-text tail: the 2^1 polynomial.

## Why

- base: unique decoding, the only regime certifiable at rate 1/2 (as for the 2^20 test shapes' 27-bit base round); 179 queries at 26 PoW bits (no round of the Ethproofs production schedules grinds more than 26) put the base query term at 100 bits (no folding PoW needed: the unique-decoding fold term is above 100 by itself)
- oracle 0: the re-committed batched polynomial at LDE 2^3, two steps below the fewest-query 2^5 (domain 2^25, folded by 6): a cheaper commit for more queries; m = 12 gives 1.44 bits/query at a 23-bit folding grind — 52 queries at 26 bits where unique decoding would need 88; its OOD term needs 8 PoW bits with a single sample
- oracle 1: m = 3 (the theorem's floor) minimises the (m + 1/2)^5 fold term; LDE 2^9 (domain 2^25), fold grind 23 bits; 4.28 bits/query
- oracle 2: m = 3; LDE 2^11 (domain 2^22), fold grind 23 bits; 5.28 bits/query, 15 queries so that 21 bits of query PoW suffice
- oracle 3: m = 3; LDE 2^13 (domain 2^19), fold grind 23 bits; 6.28 bits/query, no OOD grind

`folding_pow_bits` is one value for every folding-challenge draw of an oracle; the analysis needs one bit less per sumcheck step (listed per step above), so the schedule grinds slightly more than the certification requires.

