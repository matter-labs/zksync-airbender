# Unified machine-state challenge was not compared

## Classification

- Confirmed historical global-state soundness bug
- Fixed by: [`8ef06cf`](https://github.com/matter-labs/zksync-airbender/commit/8ef06cf8dc63b04e4b309b501d54bb571e86a1a9), PR [#225](https://github.com/matter-labs/zksync-airbender/pull/225)
- Vulnerable revision: `c16b75d2df36af2608fb971c3a75af83cd1c997d`

## Failure

The full-statement verifier compared memory challenges but omitted equality between the externally expected machine-state permutation challenge and the challenge reported by the unified proof.

## Impact and fix

The machine-state product could be accumulated under randomness unrelated to the public/global state contribution. The fix adds the missing equality. Model each argument's challenge family separately; equality for RAM does not imply equality for PC/register state.

## Regression

Forge only `machine_state_permutation_argument` in a proof output and require rejection before accumulator closure.

```sh
git diff c16b75d2df36af2608fb971c3a75af83cd1c997d 8ef06cf8dc63b04e4b309b501d54bb571e86a1a9 -- full_statement_verifier/src/unified_circuit_statement.rs
```
