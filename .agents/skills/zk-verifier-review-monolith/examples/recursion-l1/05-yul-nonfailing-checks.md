# Yul sumcheck failures were stored but never rejected

## Classification

- Confirmed historical fail-open EVM verifier bug
- Fixed by: [`4f8d993`](https://github.com/matter-labs/zksync-airbender/commit/4f8d993a7c3fbea5e52d4b4ef5cb1e3ad1a316e4)
- Vulnerable revision: `16a5cebf46a3ffa378a4dc893a302d33a359d9d7`

## Failure

Round and point consistency failures were computed as `dummy_check` and written to `GKR_CIRCUIT_CACHE_PTR`; no control-flow edge inspected the value or reverted. The contract continued even when `claim != g(0)+g(1)` or the final gate batch mismatched.

## Impact and fix

Core Sumcheck verification was observational rather than enforcing, so arbitrary invalid rounds could pass this acceptance boundary. The fix replaces dummy stores with immediate nonzero reverts and regenerates the full point checks.

## Regression

Corrupt every round coefficient and every final point claim one at a time and require revert at the corresponding layer.

```sh
git diff 16a5cebf46a3ffa378a4dc893a302d33a359d9d7 4f8d993a7c3fbea5e52d4b4ef5cb1e3ad1a316e4 -- verifier_evm/circuit.yul verifier_evm/gkr.sol
```
