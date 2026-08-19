# EVM WHIR calldata ignored the configured round schedule

## Classification

- Confirmed historical EVM proof/config implementation gap
- Fixed by: [`1f8cb3c`](https://github.com/matter-labs/zksync-airbender/commit/1f8cb3cd53b45f67a1c83543b07d7c859b233120)
- Vulnerable revision: `7c8b23bf58d0c99e250f82f588fcda65bb254d8b`

## Failure

The WHIR calldata flattener ignored circuit/config arguments and templates embedded one round schedule, domain geometry, and query count. A proof produced under another valid schedule could be serialized or verified under stale constants.

## Impact and fix

The on-chain verifier's accepted language could drift from the Rust verifier and proving key. The fix derives a `WhirGenConfig`, validates schedule lengths and bounds, generates the per-round switch, and flattens calldata with the same folds/queries.

## Regression

Generate at least two schedules and require artifact fingerprints, calldata lengths, round switches, and Rust/EVM acceptance to agree.

```sh
git diff 7c8b23bf58d0c99e250f82f588fcda65bb254d8b 1f8cb3cd53b45f67a1c83543b07d7c859b233120 -- verifier_evm/src/flatten.rs verifier_evm/src/generator/whir.rs verifier_evm/src/templates/whir.sol
```
