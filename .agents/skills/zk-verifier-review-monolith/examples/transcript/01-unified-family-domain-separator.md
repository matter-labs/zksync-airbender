# Unified circuit family was not transcript-bound

## Classification

- Confirmed historical Fiat-Shamir statement-binding bug
- Component: unified full-statement verifier
- Fixed by: [`7bfd63b`](https://github.com/matter-labs/zksync-airbender/commit/7bfd63b42fc56b5b44c0c24200e930259d4eb95b)
- Vulnerable revision: `745cfa076989dbd1e430c422be9803c2bdb8c2d2`

## Failure

The verifier entered the unified-circuit proof loop without first absorbing `REDUCED_MACHINE_CIRCUIT_FAMILY_IDX`. Challenges therefore bound the proof bytes but not the circuit-family interpretation under which those bytes were verified.

## Impact and fix

A proof stream could be replayed across statement modes whenever their layouts happened to parse compatibly. The fix absorbs a padded family identifier before any per-circuit proof data. Audit every verifier entrypoint for circuit, version, security-mode, and program/setup domain separation before its first squeeze.

## Regression

Hold proof bytes constant, mutate only the family/mode, and require the initial transcript seed and verification result to change.

```sh
git diff 745cfa076989dbd1e430c422be9803c2bdb8c2d2 7bfd63b42fc56b5b44c0c24200e930259d4eb95b -- full_statement_verifier/src/unified_circuit_statement.rs
```
