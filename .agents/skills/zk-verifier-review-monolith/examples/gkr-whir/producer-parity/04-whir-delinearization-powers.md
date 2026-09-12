# WHIR delinearization reused one power

## Classification

- Producer-parity history: confirmed historical WHIR random-linear-combination mismatch
- Component: GPU WHIR OOD/query contribution accumulation
- Claim-chain location: OOD and query consistency terms → equality polynomial/sumcheck claim
- Security character: historical GPU/canonical-verifier incompleteness; shared single-power logic would weaken independent-error batching
- Fixed by: [`e865551`](https://github.com/matter-labs/zksync-airbender/commit/e865551a08068caa4dc5be7e720a57198fe23622)
- Vulnerable revision: `32894e873a8412985312598d9a39ab954ebd8664`

## Protocol context

Within each WHIR round, the OOD consistency term and every sampled query term are folded into one equality-polynomial claim using a fresh delinearization challenge `x`. Canonical CPU logic assigns a distinct running power to each contribution: `x` to OOD and `x^(i+2)` to query `i`.

The powers provide position binding and probabilistic independence between error terms. The same convention must be used in the accumulated claim, equality polynomial, and verifier recomputation for both the initial base-field round and recursive extension rounds.

## Intended batch relation

```text
combined = x * OOD_term
         + x² * query_term_0
         + x³ * query_term_1
         + ...

eq_poly receives the same coefficient for the matching sampled point
```

There are `num_queries + 1` required powers per WHIR round.

## Failure

The GPU drew one `x`, uploaded a single-element device buffer, and passed that same slice to the OOD accumulation and every query accumulation. The device kernel always read element zero, so all contributions were weighted by `x`.

After the CPU implementation was corrected to running powers, GPU and canonical verifier disagreed. The first observed test failure appeared as a later WHIR Sumcheck coefficient mismatch, not at challenge generation.

## Failure flow

1. Derive the correct delinearization challenge `x`.
2. Accumulate OOD with `x` as intended.
3. Accumulate every query with `x` again instead of advancing powers.
4. Construct an equality polynomial representing `x*(OOD + Σ queries)`.
5. Canonical verification constructs `x*OOD + Σ x^(i+2)*query_i` and rejects.

If both sides reused `x`, distinct query errors could cancel in one unpositioned sum with more freedom than the theorem allows. The specific historical GPU revision, however, was caught as parity failure against the corrected CPU source of truth.

## Impact and fix

GPU proofs diverged in both initial and recursive WHIR rounds and could not pass canonical verification. The fix uploads `[x, x², ..., x^(q+1)]` per round and supplies slice `[0..1]` for OOD and `[i+1..i+2]` for query `i`.

For random linear combinations, verify coefficient generation, indexing, buffer length, device slicing, and contribution order. Drawing a fresh random scalar is insufficient if every item receives the same power.

## Regression

- Use at least three nonzero, distinguishable contributions and compare with a direct running-power computation.
- Mutate contribution order and require a different combined claim.
- Cover zero, one, and several queries in initial and recursive rounds.
- Compare CPU/GPU equality-polynomial coefficients immediately after each accumulation.
- Include exceptional `x = 0/1` cases in symbolic tests and account for their probability separately.

## Reproduction evidence

```sh
git diff 32894e873a8412985312598d9a39ab954ebd8664 e865551a08068caa4dc5be7e720a57198fe23622 -- gpu_prover/src/prover/whir_fold.rs
```
