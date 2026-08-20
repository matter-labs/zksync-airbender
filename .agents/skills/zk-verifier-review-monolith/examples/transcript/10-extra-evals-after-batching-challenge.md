# Cache-dependency evaluations followed the batching challenge

## Classification

- Confirmed historical Fiat-Shamir ordering bug
- Component: GKR layer-claim batching with cache dependencies
- Security character: dependent randomness was drawn before the complete prover message; producer/verifier consequence depends on which implementations shared the order
- Fixed by: [`4e3142e`](https://github.com/matter-labs/zksync-airbender/commit/4e3142ead72767b21139bcaa2f2acb1da6944739)
- Vulnerable revision: `bf9bd04f2ac916eb8e65603cdba72f563b98351f`

## Protocol context

At the end of a sumcheck layer, the prover reveals the evaluations that become claims for the next layer. Cache relations can introduce additional dependency evaluations not present among the ordinary `new_claims`. All of these prover-controlled values are inputs to the next layer's batched claim.

The next batching coefficient must be sampled only after the complete vector is fixed. Otherwise the prover can choose the late evaluations as functions of the random coefficient used to combine them.

## Intended transcript relation

```text
ordinary_claims <- derive in canonical address order
extra_claims <- collect all cache dependencies in canonical order
complete_message = ordinary_claims || extra_claims
absorb(complete_message once)
next_batching_challenge <- squeeze(seed)
construct next-layer batched claim using that challenge
```

One absorb of the concatenation is the protocol event. Two separately framed absorbs need not produce the same seed for a fixed-block transcript construction.

## Failure

The prover absorbed `new_claims` and immediately drew `next_batching_challenge`. Only afterwards did it discover and absorb extra prover-provided evaluations required by the cache relations. The coefficient used to combine the next layer was therefore independent of part of the message it was meant to batch.

This is more serious than a mere CPU/GPU serialization mismatch. If an accepting verifier follows the same order, a malicious prover learns the coefficient before fixing every input to the compressed relation. If the verifier follows the corrected order, the vulnerable producer instead emits an honestly invalid proof. The audit must establish both schedule parity and the schedule required by the soundness argument.

## Adversarial flow

1. Commit the ordinary next-layer claims.
2. Learn `next_batching_challenge`.
3. Choose one or more cache-dependency evaluations after seeing that coefficient.
4. Use the remaining degrees of freedom to make the randomized batched equality hold while an individual dependency claim is false.
5. Absorb the chosen extras only after they can no longer influence the coefficient.

The exact algebraic forgery depends on the cache relation and number of free claims, but the causal violation is enough to invalidate the intended batching proof: verification-relevant prover values were not fixed before dependent randomness.

## Impact and fix

The challenge failed to bind the full next-layer claim vector. The fix creates one transcript input initialized with ordinary claims, extends it with all canonical extra evaluations, absorbs the completed vector, and only then draws the batching challenge.

The immediately following historical repair moved this event outside the optional cache branch. Together the commits show why transcript fixes must be reviewed as complete state-machine transitions, not isolated line movements.

## Regression

- Build a layer whose only new dependency is introduced by a cache relation and assert that value appears before the first dependent squeeze.
- Mutate any extra evaluation and require `next_batching_challenge` to change.
- Compare the exact framing of `ordinary || extras`; do not accept two absorbs as automatically equivalent to one.
- Differential-test no-cache, one-cache, overlapping-cache, and several-cache layers.
- Add a negative algebraic test with inconsistent individual cache claims that could cancel only after challenge observation.

## Reproduction evidence

```sh
git diff bf9bd04f2ac916eb8e65603cdba72f563b98351f 4e3142ead72767b21139bcaa2f2acb1da6944739 -- prover/src/gkr/prover/sumcheck_loop/mod.rs
```
