# WHIR schedule notes — `EthproofsSoundnessCalc`, `sec_100`, 2^24 committed polynomials, two values per column per leaf (add_sub_lui_auipc_mop, inits_and_teardowns, jump_branch_slt, load_store_subword_only, load_store_word_only, shift_binary)

Certified by `ethereum/soundcalc` (commit `2af5e7d`, 2026-09-21), WHIR PCS module only (WHIR Theorem 5.2 with the BCHKS25 proximity-gap bounds): **100 bits**, binding term `OOD(i=1)`; every other term is at or above the target and several Johnson-bound terms sit exactly on it, so any change of a domain, a fold or the committed-polynomial ceiling needs a re-run of `prover/src/gkr/prover_config/example_configs/soundcalc/whir_schedule_search.py`. Model inputs: BabyBear⁴ challenge field (|F| ≈ 2^123.6), 256-bit hashes, powers batching, constraint degree 3 (soundcalc's minimum; ours is 2), our explicit per-oracle LDE factors, one OOD sample per oracle. The GKR circuit layer is outside the model (105–118 bits by our own field-size accounting).

## This circuit

- committed polynomials entering WHIR: **56** (from the compiled circuit; physical packing 2^0, two values per column per base leaf), certified ceiling 128 → batching PoW 9 bits (computed for the ceiling with `pow_bits_for_batched_proximity`; batching term 102 bits under unique decoding)
- committed polynomial size 2^24 at the base rate 2^-1 (domain 2^25)

## Rounds

| oracle | poly | LDE | domain | fold | queries | query PoW | folding PoW (per step) | OOD PoW | regime | bits/query | UDR would need |
|---|---|---|---|---|---|---|---|---|---|---|---|
| base | 2^24 | 2^1 | 2^25 | 1 | 179 | 26 | 0 | – | unique decoding (δ = (1 − ρ)/2 = 0.250, list size 1) | 0.415 | 179 |
| 0 | 2^23 | 2^2 | 2^25 | 5 | 79 | 26 | 22 [22, 21, 20, 19, 18] | 8 | Johnson bound, m = 12 (η = √ρ/(2m) = 0.0208, δ = 1 − √ρ − η = 0.479, list size 25.0) | 0.94 | 108 |
| 1 | 2^18 | 2^8 | 2^26 | 5 | 20 | 25 | 22 [22, 21, 20, 19, 18] | 5 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0104, δ = 1 − √ρ − η = 0.927, list size 56.0) | 3.78 | 74 |
| 2 | 2^13 | 2^10 | 2^23 | 5 | 16 | 24 | 22 [22, 21, 20, 19, 18] | 2 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0052, δ = 1 − √ρ − η = 0.964, list size 112.0) | 4.78 | 74 |
| 3 | 2^8 | 2^12 | 2^20 | 4 | 13 | 25 | 22 [22, 21, 20, 19] | 0 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0026, δ = 1 − √ρ − η = 0.982, list size 224.0) | 5.78 | 74 |
| 4 | 2^4 | 2^14 | 2^18 | 3 | 11 | 26 | 23 [23, 22, 21] | 0 | Johnson bound, m = 3 (η = √ρ/(2m) = 0.0013, δ = 1 − √ρ − η = 0.991, list size 448.0) | 6.78 | 74 |

Plain-text tail: the 2^1 polynomial.

## Why

- base: unique decoding, the only regime certifiable at rate 1/2 (as for the 2^20 test shapes' 27-bit base round); 179 queries at 26 PoW bits (no round of the Ethproofs production schedules grinds more than 26) put the base query term at 100 bits (no folding PoW needed: the unique-decoding fold term is above 100 by itself)
- oracle 0: LDE 2^2, two steps below the fewest-query 2^4 (domain 2^25): a cheaper commit of this largest oracle for more queries; at rate 2^-2 m = 12 gives 0.94 bits/query at a 22-bit folding grind — 79 queries at 26 bits where unique decoding would need 108; the OOD term needs 8 PoW bits
- oracle 1: m = 3 (the theorem's floor) minimises the (m + 1/2)^5 fold term; LDE 2^8 (domain 2^26) so the fold grind is 22 bits; 3.78 bits/query
- oracle 2: m = 3; LDE 2^10 (domain 2^23), fold grind 22 bits; 4.78 bits/query
- oracle 3: m = 3; LDE 2^12 (domain 2^20), fold grind 22 bits; 5.78 bits/query, no OOD grind
- oracle 4: m = 3; LDE 2^14 (domain 2^18), fold grind 23 bits; 6.78 bits/query, no OOD grind

`folding_pow_bits` is one value for every folding-challenge draw of an oracle; the analysis needs one bit less per sumcheck step (listed per step above), so the schedule grinds slightly more than the certification requires.

