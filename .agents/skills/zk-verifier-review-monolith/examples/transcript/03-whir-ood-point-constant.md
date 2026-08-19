# WHIR OOD point was the constant 42

## Classification

- Confirmed historical challenge-generation bug
- Component: WHIR recursive fold
- Fixed by: [`0f645ed`](https://github.com/matter-labs/zksync-airbender/commit/0f645ed91310d57f9f640d1e7d98996cc329f9c1)
- Vulnerable revision: `92b45715b6311d58710fd16baf7aab8510b32914`

## Failure

The OOD evaluation point was constructed as field element `42` instead of being squeezed from the transcript after the relevant polynomial commitment.

## Impact and fix

A fixed evaluation point removes the unpredictable verifier choice required by the reduction and permits a prover to tailor polynomial discrepancies to that point. The fix draws one extension-field element from the rolling seed. Search for constants, test hooks, or prover-supplied values at every conceptual verifier-randomness site.

## Regression

Vary an earlier commitment and assert that the OOD point changes; assert the prover and verifier derive it without reading it from the proof.

```sh
git diff 92b45715b6311d58710fd16baf7aab8510b32914 0f645ed91310d57f9f640d1e7d98996cc329f9c1 -- prover/src/gkr/whir/mod.rs
```
