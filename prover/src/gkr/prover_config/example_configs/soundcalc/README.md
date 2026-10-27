# soundcalc drivers for the `EthproofsSoundnessCalc` schedules

The `SoundnessMode::EthproofsSoundnessCalc` entries of `../ethproofs_soundcalc.rs`
are produced by `whir_schedule_search.py`, a search over the WHIR PCS model of
[`ethereum/soundcalc`](https://github.com/ethereum/soundcalc) (commit `2af5e7d`,
2026-09-21). soundcalc is not vendored and has no package dependencies; it needs
Python ≥ 3.9 (on the Mac: `/opt/homebrew/bin/python3.11`; the system `python3`
is 3.8 and fails on `list[int]` annotations).

```bash
git clone https://github.com/ethereum/soundcalc /tmp/soundcalc && git -C /tmp/soundcalc checkout 2af5e7d
cd prover/src/gkr/prover_config/example_configs/soundcalc
PYTHONPATH=/tmp/soundcalc python3.11 whir_schedule_search.py      # the certified entries, one block per shape
PYTHONPATH=/tmp/soundcalc python3.11 assess_current_configs.py    # the pessimistic ladders under UDR / JBR
PYTHONPATH=/tmp/soundcalc python3.11 regime_sweep.py              # m / OOD-count sweep of the ladders
PYTHONPATH=/tmp/soundcalc python3.11 late_round_rebalance.py      # JBR-rebalanced late rounds of the pessimistic ladders
```

(`/usr/bin/python3` on a current macOS is 3.9 and works too.)

## What the search does

* Only soundcalc's WHIR PCS module is used (`soundcalc/pcs/whir.py`: WHIR
  Theorem 5.2 with the BCHKS25 proximity-gap bounds); soundcalc has no model
  of the GKR circuit layer. Inputs: BabyBear⁴ (`|F| ≈ 2^123.6`), 256-bit
  hashes, powers batching of the committed polynomials, constraint degree 3
  (soundcalc's minimum; ours is 2), one OOD sample per oracle.
* soundcalc assumes the domain halves every WHIR iteration; after building
  `WHIR(cfg)` every driver overwrites `w.log_inv_rates` with our explicit
  per-oracle `lde_factor_log2` list (plus a trailing copy).
* The regime is chosen per iteration through a dispatching `Mixed` regime
  (keyed by the oracle's rate): unique decoding (`UniqueDecodingRegime`) for
  the base round, Johnson bound with an explicit multiplicity
  (`JohnsonBoundRegime(F, explicit_m=m)`, slack `η = √ρ/(2m)`) afterwards.
* Per oracle the search tries every LDE factor whose domain fits 2^27 and
  every `m ∈ {3, 4, 5, 8, 12, 20}` plus unique decoding, keeps the candidates
  whose fold terms can be lifted to the target with ≤ `FOLD_CAP` (24) bits of
  folding PoW per sumcheck step and whose OOD term with ≤ `LATER_POW` (27)
  bits of OOD PoW, and picks the fewest queries (then the least grinding,
  then the best rate). Query PoW is 28 in the base round; afterwards the
  query count is sized against a 27-bit cap and the PoW is then lowered to
  the smallest grind that still lifts the round's query term to the target
  (12 queries at 6.28 bits each are 75 bits, so 25 bits of grind, not 27).
* Virtual packing (`fold_log2 = 0`) is emulated as a message one bit larger
  with a round-0 fold of 1 (soundcalc needs `k_0 ≥ 1`): the re-committed
  oracle 0 is then exactly the batched polynomial; the emulated base fold
  term is 1 bit conservative and the batching term is recomputed on the real
  base code.
* The committed-polynomial ceiling of a shape only sets the batching PoW
  (`pow_bits_for_batched_proximity` at the ceiling, batching term 102 bits).

`whir_schedule_search.py` prints each shape as `WhirSchedule` fields with the
per-step folding PoW list (our `folding_pow_bits` is one value per oracle: the
maximum), the regime and `m` per oracle, bits per query, and the query count a
unique-decoding analysis would need. Copy a new block into
`ethproofs_soundcalc.rs` as an `EthproofsSoundcalcEntry` together with the
reasons for the regime choices.

Not designed in this mode: the L1-feeder 2^23 schedule (base LDE 16) and the
EVM Proth120 2^26 packed config (`assess_current_configs.py` evaluates both;
Proth120 with 2^31 domains caps the Johnson-bound fold term near 48–57 bits, so
a 100-bit schedule there needs smaller domains and ~75 unique-decoding queries
per round).

## Rebalancing the pessimistic ladders' late rounds (`late_round_rebalance.py`)

Under the Johnson bound with a per-oracle multiplicity, the pessimistic ladders' base
round (rate 1/2, 89 queries, 26 bits of PoW) is worth 69 bits, but their last oracles
(rate 2^-19 on 2^24..2^27 domains) fall to 60-68 bits: the fold term grows with the
domain over rate^1.5 and the list size, faster than the ~log2(1/rate)/2 bits a query
buys there. The driver keeps the base round, the folds and the query PoW, and for every
later oracle picks the smallest LDE factor and the fewest queries (never below the
pessimistic rule's own count) at which all of the oracle's terms reach the base round's
level; it also prints each oracle's LDE-versus-queries frontier. The result is uniform
69-bit ladders with 2^5..2^7 smaller last oracles, one or two extra queries per late round,
22-37 % less intermediate LDE work and 5-11 % more opened leaf values. These are the
ladders in `pessimistic_conjecture.rs` since 2026-10-27; the delegation circuits' virtual
twin keeps 18 queries on its oracle 0 with one more bit of query PoW (26), which the driver
shows restores the plain ladder's level (oracle 2's 27-bit PoW is tight: 8 queries at rate
2^-11 are 42 bits, and its 2^27 domain leaves no room for a larger LDE). The SHAPES table
holds the PRE-rebalance ladders so the run reproduces the analysis.

