# WHIR OOD point was the constant 42

## Classification

- Confirmed historical challenge-generation bug
- Component: WHIR recursive fold implementation
- Security character: loss of verifier unpredictability at an out-of-domain reduction point
- Historical location: prover-side proof construction; verifier impact must be checked at every implementation that reconstructs the same round
- Fixed by: [`0f645ed`](https://github.com/matter-labs/zksync-airbender/commit/0f645ed91310d57f9f640d1e7d98996cc329f9c1)
- Vulnerable revision: `92b45715b6311d58710fd16baf7aab8510b32914`

## Protocol context

After committing the next WHIR oracle, the protocol evaluates the current folded polynomial at an out-of-domain point. The claimed OOD value is later mixed into the query/delinearization relation. Soundness relies on the prover fixing the polynomial commitment before learning the evaluation point.

In the noninteractive protocol, that point must be reconstructed from the rolling Fiat-Shamir seed. Merely choosing a field element outside the evaluation domain is not enough: it must also be unpredictable at commitment time.

## Intended transcript relation

```text
absorb(next WHIR oracle cap)
ood_point <- squeeze_extension_field(seed)
ood_value <- prover evaluates committed polynomial at ood_point
absorb(ood_value)
derive query PoW/indexes and delinearization challenge
```

The exact subsequent absorption of `ood_value` evolved in later fixes, but the causal edge `oracle commitment -> random OOD point` is already mandatory here.

## Failure

One recursive-fold path constructed the OOD evaluation point as the base-field element `42` instead of squeezing an extension-field element from the transcript. The preceding oracle could therefore be chosen with full knowledge of the evaluation point.

This was not a harmless prover optimization. A polynomial discrepancy can be engineered to vanish at a fixed point, so equality at `42` does not provide the random evaluation guarantee used by the reduction. The fact that another path in the same module already drew transcript randomness made this especially easy to miss during review.

## Adversarial flow

1. Choose a false polynomial relation whose difference contains the factor `(X - 42)`.
2. Commit to that polynomial while already knowing the verifier will evaluate at `42`.
3. Supply the matching OOD value at the fixed point.
4. Carry the zero discrepancy into the later delinearized/query relation.

Whether this becomes acceptance in a particular historical binary depends on whether its verifier mirrored the constant, independently derived a point, or treated this path as incomplete. From the argument's perspective, any accepting implementation using the constant has lost the OOD soundness factor; a verifier deriving the correct random point instead produces prover/verifier incompleteness.

## Impact and fix

The constant removed the unpredictable verifier challenge required by the OOD reduction and allowed commitments to be tailored to the checked point. The fix draws exactly one extension-field element from the current rolling seed after the oracle commitment.

Review conceptual randomness sites rather than searching only for transcript APIs. Constants, test hooks, deterministic indices, proof-supplied “challenges,” and default values can all silently occupy a role that the proof requires to be sampled after a commitment.

## Regression

- Hold protocol parameters fixed, vary the preceding oracle cap, and require the OOD point to change.
- Record prover and verifier transcript events and require both to derive the point at the same event index without reading it from the proof.
- Add a negative test using a discrepancy divisible by `(X - 42)`; it must not systematically evade the OOD check.
- Exercise every recursive/final-round branch, not only the first WHIR path.

## Reproduction evidence

```sh
git diff 92b45715b6311d58710fd16baf7aab8510b32914 0f645ed91310d57f9f640d1e7d98996cc329f9c1 -- prover/src/gkr/whir/mod.rs
```
