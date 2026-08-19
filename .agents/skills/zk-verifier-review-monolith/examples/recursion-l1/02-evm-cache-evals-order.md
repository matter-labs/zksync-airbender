# EVM batching challenge preceded cache-dependency evaluations

## Classification

- Confirmed historical L1 Fiat-Shamir ordering bug
- Fixed by: [`4b0d431`](https://github.com/matter-labs/zksync-airbender/commit/4b0d43104b7a82b5b9bec7fc37a6d6bea0c94cb8)
- Vulnerable revision: `585e7c9384f83e2d6b98023d8aa5bdd001686faa`

## Failure

For cache-bearing GKR layers, generated Yul absorbed the ordinary final-step claims, drew `next_alpha`, and only then absorbed extra cache-dependency evaluations. It also used two Keccak calls where the prover defined one `seed || final_step || extras` message.

## Impact and fix

The L1 batching challenge did not bind all prover-provided evaluations and did not match the canonical proof transcript. The generator now copies both ranges contiguously, hashes once, then draws.

## Regression

Compare Rust and EVM event traces and seeds for every cache-bearing layer; mutate an extra evaluation and require `next_alpha` to change.

```sh
git diff 585e7c9384f83e2d6b98023d8aa5bdd001686faa 4b0d43104b7a82b5b9bec7fc37a6d6bea0c94cb8 -- verifier_evm/src/generator/circuit_yul.rs
```
