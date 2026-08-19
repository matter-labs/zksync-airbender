# WHIR batching zeroed every power but the first

## Classification

- Confirmed historical PCS batching soundness bug
- Fixed by: [`c9d8620`](https://github.com/matter-labs/zksync-airbender/commit/c9d8620d2f549781be154c6813264330b63b8a94)
- Vulnerable revision: `e0b57de405ba1e66dbc8da572e9ac73a8d266726`

## Failure

After materializing powers of the WHIR batching challenge for all base oracles, code overwrote `challenge_powers[1..]` with zero. The batched polynomial and claim therefore retained only the first committed polynomial.

## Impact and fix

Openings for witness and setup columns after the first term were not represented in the WHIR reduction. The fix removes the zero fill and uses the full power sequence. A batching verifier must prove every item has a nonzero, position-bound coefficient.

## Regression

Mutate each base oracle/claim independently and require the batched polynomial and final verification to change.

```sh
git diff e0b57de405ba1e66dbc8da572e9ac73a8d266726 c9d8620d2f549781be154c6813264330b63b8a94 -- prover/src/gkr/whir/mod.rs
```
