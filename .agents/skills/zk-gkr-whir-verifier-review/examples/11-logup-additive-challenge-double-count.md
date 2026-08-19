# Unbalanced LogUp kernel added gamma twice

## Classification

- Confirmed historical protocol-specific Sumcheck gate bug
- Fixed by: [`a1ae551`](https://github.com/matter-labs/zksync-airbender/commit/a1ae551a9ccfa8f6860d4aec845a16030d02364c)
- Vulnerable revision: `06c4fc94cbc71d5132afe24c9f77695756595670`

## Failure

The quadratic-only evaluation of an unbalanced rational lookup took a base input `d` that already represented the shifted denominator and added `lookup_additive_challenge` again before multiplying numerator and denominator outputs.

## Impact and fix

The Sumcheck polynomial encoded `d + gamma` where the intended LogUp relation used `d`; it no longer matched the forward gate or final claim. The fix removes the redundant parameter and multiplies directly by `d`.

## Regression

Compare full and quadratic-only kernel evaluations at several gamma values, including zero, using direct rational-pair algebra.

```sh
git diff 06c4fc94cbc71d5132afe24c9f77695756595670 a1ae551a9ccfa8f6860d4aec845a16030d02364c -- prover/src/gkr/sumcheck/evaluation_kernels/kernel_impls/lookup_rational_with_unbalanced_base.rs
```
