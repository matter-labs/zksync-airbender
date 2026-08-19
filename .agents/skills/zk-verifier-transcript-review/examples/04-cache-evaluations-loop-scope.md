# Cached evaluations were absorbed in the wrong scope

## Classification

- Confirmed historical prover/verifier transcript-parity bug
- Component: GKR sumcheck layer transition
- Fixed by: [`c9d8620`](https://github.com/matter-labs/zksync-airbender/commit/c9d8620d2f549781be154c6813264330b63b8a94)
- Vulnerable revision: `e0b57de405ba1e66dbc8da572e9ac73a8d266726`

## Failure

Extra evaluations needed to justify cached relations were committed while iterating cache relations. Their transcript multiplicity and placement consequently depended on loop structure rather than the canonical layer message.

## Impact and fix

Equivalent claims could advance the transcript differently, and later batching challenges could omit or duplicate cache-dependent values. The fix collects the evaluations in deterministic map order and commits one flattened layer message after collection.

## Regression

Construct layers with zero, one, and several cache relations and compare the exact transcript event trace against the verifier.

```sh
git diff e0b57de405ba1e66dbc8da572e9ac73a8d266726 c9d8620d2f549781be154c6813264330b63b8a94 -- prover/src/gkr/prover/sumcheck_loop/mod.rs
```
