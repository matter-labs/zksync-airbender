# MaxQuadratic reused terms and polluted the quadratic coefficient

## Classification

- Confirmed historical Sumcheck polynomial-construction bug
- Fixed by: [`a514b2d`](https://github.com/matter-labs/zksync-airbender/commit/a514b2d3bf4a19a8725baa721ce8f7f32a7259f1)
- Vulnerable revision: `d04ee655d3bb20e43786f7316416714ea0f032cb`

## Failure

`MaxQuadratic` initialized one `contribution` outside the inner `(b, coeff)` loop, so independent quadratic monomials compounded on one another. Its first-round quadratic-coefficient accumulator also started from the gate's constant offset even though constants have zero quadratic coefficient.

## Impact and fix

The prover sent a univariate polynomial different from the batched gate polynomial, causing invalid Sumcheck claims or honest-proof failure. The fix resets each monomial contribution from `input[a]` and initializes the quadratic coefficient to zero.

## Regression

Compare optimized coefficients against direct evaluation/interpolation for several terms sharing `a`, nonzero constants, and asymmetric cross terms.

```sh
git diff d04ee655d3bb20e43786f7316416714ea0f032cb a514b2d3bf4a19a8725baa721ce8f7f32a7259f1 -- prover/src/gkr/sumcheck/evaluation_kernels/kernel_impls/max_quadratic_rel.rs
```
