# WHIR delinearization reused one power

## Classification

- Confirmed historical WHIR random-linear-combination bug
- Fixed by: [`e865551`](https://github.com/matter-labs/zksync-airbender/commit/e865551a08068caa4dc5be7e720a57198fe23622)
- Vulnerable revision: `32894e873a8412985312598d9a39ab954ebd8664`

## Failure

GPU WHIR multiplied the OOD contribution and every query contribution by the same challenge `x`. The protocol required running powers: `x` for OOD and `x^(i+2)` for query `i`.

## Impact and fix

The supposedly independent error terms collapsed into a weaker linear combination and no longer matched the canonical verifier. The fix uploads and indexes all required powers separately in base and recursive rounds.

## Regression

Use at least three nonzero contributions and compare the eq-polynomial accumulator to a direct running-power calculation.

```sh
git diff 32894e873a8412985312598d9a39ab954ebd8664 e865551a08068caa4dc5be7e720a57198fe23622 -- gpu_prover/src/prover/whir_fold.rs
```
