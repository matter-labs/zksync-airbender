# Unified circuit sequence used a dead legacy field

## Classification

- Confirmed historical multi-chunk verification bug
- Fixed by: [`85c4925`](https://github.com/matter-labs/zksync-airbender/commit/85c492522717063abc7191f8fb603ca728412e55)
- Vulnerable revision: `728c6a2edc7d2e271b77627d5a9a5361e09c30de`

## Failure

The full-statement verifier required `current.circuit_sequence == loop_index`, but the unified proof format retained that field only as an unused legacy value fixed to zero.

## Impact and fix

Every unified campaign with more than one chunk failed on honest proofs. The fix checks the actual format invariant (`0`) instead of pretending the dead field establishes order. Chunk coverage must come from live, constrained counters or the aggregate protocol—not stale public-output fields.

## Regression

Verify two or more unified chunks and separately prove that reordering is handled by the global state/memory relation.

```sh
git diff 728c6a2edc7d2e271b77627d5a9a5361e09c30de 85c492522717063abc7191f8fb603ca728412e55 -- full_statement_verifier/src/unified_circuit_statement.rs
```
