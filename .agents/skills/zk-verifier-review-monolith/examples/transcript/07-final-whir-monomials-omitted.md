# Final WHIR monomials were not absorbed

## Classification

- Confirmed historical final-round transcript and proof-serialization bug
- Component: final WHIR round
- Fixed by: [`cb3787d`](https://github.com/matter-labs/zksync-airbender/commit/cb3787df94900baed4b675b472c30b78c56d9b2e)
- Vulnerable revision: `1b2f74fb8b2b2828954dd37f32cc2d69cf8734dc`

## Failure

The GPU final round neither absorbed the revealed monomial coefficients before final query PoW nor copied them into `proof.final_monomials` for verifier evaluation.

## Impact and fix

The final challenge was independent of the polynomial representation it was meant to test, and the serialized proof lacked the value needed to close the claim. The fix copies coefficients to host, absorbs them, then stores them before scheduling PoW.

## Regression

Require nonempty final monomials, byte-exact CPU/GPU transcript parity, and challenge changes under a one-coefficient mutation.

```sh
git diff 1b2f74fb8b2b2828954dd37f32cc2d69cf8734dc cb3787df94900baed4b675b472c30b78c56d9b2e -- gpu_prover/src/prover/whir_fold.rs
```
