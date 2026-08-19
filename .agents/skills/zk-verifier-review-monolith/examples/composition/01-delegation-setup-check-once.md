# Delegation setup was checked only once

## Classification

- Confirmed historical full-statement soundness bug
- Fixed by: [`32edde7`](https://github.com/matter-labs/zksync-airbender/commit/32edde78af91101ebcb79c611c95016549895129), PR [#21](https://github.com/matter-labs/zksync-airbender/pull/21)
- Vulnerable revision: `7d80b89795ca86155290265f100c329f689ed27b`

## Failure

The verifier populated expected delegation setup caps internally but compared a proof's setup only for `circuit_sequence == 0`. Later chunks could supply a different setup while still contributing to the same global delegation and memory accumulators.

## Impact and fix

The global statement could aggregate proofs for different circuits under one delegation type. The fix compares every delegation proof's setup cap with the expected cap. Never infer immutable verifier identity from a prior proof unless the current proof is cryptographically linked to that identity.

## Regression

Mutate only a non-first chunk's setup cap and require rejection.

```sh
git diff 7d80b89795ca86155290265f100c329f689ed27b 32edde78af91101ebcb79c611c95016549895129 -- full_statement_verifier/src/lib.rs
```
