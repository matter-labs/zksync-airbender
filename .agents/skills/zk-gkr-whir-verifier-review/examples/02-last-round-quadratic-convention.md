# Batched sumcheck used the wrong last-round convention

## Classification

- Confirmed historical Sumcheck implementation regression
- Fixed by: [`42e910a`](https://github.com/matter-labs/zksync-airbender/commit/42e910ad2e3ee507706ae8a2e8290a6bd540b55a)
- Vulnerable revision: `ad95db69bdfb98ce3e511bdf3c5948cde931da6d`

## Failure

A merge kept a dedicated explicit-form final-round arm inside a loop whose surrounding convention expected quadratic-only stratification and deferred interpolation. The final coefficients were consequently encoded under mixed conventions.

## Impact and fix

The Sumcheck final claim no longer matched the pointwise gate evaluation. The fix restores one convention end to end. Treat last-round shortcuts as a protocol variant and verify sender, parser, interpolation, and final-claim formulas together.

## Regression

Run micro-Sumchecks with linear, quadratic, mixed-field, and zero-quadratic gates; compare final coefficients and claims to a naive prover.

```sh
git diff ad95db69bdfb98ce3e511bdf3c5948cde931da6d 42e910ad2e3ee507706ae8a2e8290a6bd540b55a -- prover/src/gkr/prover/sumcheck_loop/batch_evaluation.rs
```
