# Sparse delegation quotient scaled the address itself

## Classification

- Confirmed historical quotient-generation bug
- Fixed by: [`9b955b6`](https://github.com/matter-labs/zksync-airbender/commit/9b955b649cfbd1ef04305ec15af344dc5a41354f)
- Vulnerable revision: `6327a202048659bd8afac3b65cf65bb7e2ed9fc3`

## Failure

For variable-dependent sparse delegation addresses, generated verifier code loaded `variable_offset` into `t` but multiplied `address_low` by the coefficient and then added unscaled `t`. The intended expression was `address_low + coeff * variable_offset`.

## Impact and fix

The verifier's RAM tuple differed from the prover/circuit for nontrivial coefficients, invalidating honest proofs and risking acceptance against the wrong quotient relation if all generated paths shared the error. The fix scales the offset before addition.

## Regression

Use coefficient values other than 0 and 1 and compare generated quotient evaluation with a direct sparse-address calculation.

```sh
git diff 6327a202048659bd8afac3b65cf65bb7e2ed9fc3 9b955b649cfbd1ef04305ec15af344dc5a41354f -- verifier_generator/src/inlining_generator/grand_product_accumulators.rs
```
