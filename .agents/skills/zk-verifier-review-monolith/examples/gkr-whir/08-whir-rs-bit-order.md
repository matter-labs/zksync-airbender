# Multilinear coefficients were built in the wrong bit order

## Classification

- Confirmed historical MLE-to-Reed-Solomon ordering bug
- Fixed by: [`619c6ab`](https://github.com/matter-labs/zksync-airbender/commit/619c6ab4f291f7df2d400edd0389a16c4452dae3)
- Vulnerable revision: `db36e5d771862d22a4538ee9699cfb9b4d8f0451`

## Failure

Stage 1 converted hypercube evaluations into multilinear coefficients without first bit-reversing enumeration into the convention expected by the transform and WHIR domain layout.

## Impact and fix

The committed RS codeword represented a variable permutation of the claimed MLE, so folds and openings disagreed even with correct field arithmetic. The fix bit-reverses each input before coefficient conversion.

## Regression

Use a nonsymmetric MLE whose variables have distinct weights and compare all Boolean evaluations and one random-point evaluation before and after RS encoding.

```sh
git diff db36e5d771862d22a4538ee9699cfb9b4d8f0451 619c6ab4f291f7df2d400edd0389a16c4452dae3 -- prover/src/gkr/prover/stages/stage1.rs
```
