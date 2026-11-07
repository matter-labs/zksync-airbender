# Generated GKR verifier drew the batching challenge before cache-dependency evaluations

## Classification

- Confirmed historical Fiat-Shamir ordering bug
- Component: generated `mem_subword_only/sec_100` GKR verifier, main layer 2
- Verifier anchor: `verifier/src/generated/mem_subword_only/sec_100/gkr.rs` layer-2 handoff
- Security character: confirmed verifier component soundness failure
- Generator fixed by: [`3edc1b9a`](https://github.com/matter-labs/zksync-airbender/commit/3edc1b9a2374760be4d6aca7beaf9d4ffae4ad87), PR #365
- Fixed by: [`1eae11e`](https://github.com/matter-labs/zksync-airbender/commit/1eae11eaf06bd47f67045ae849bed7fb42aa37c2), PR #368
- Vulnerable revision: `3edc1b9a2374760be4d6aca7beaf9d4ffae4ad87`

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

The same-revision generated `mem_subword_only/sec_100` verifier committed 16
ordinary evaluations and immediately drew `next_batching`. Only afterward did
it read and absorb four extra prover-controlled cache dependencies. It merged
all 20 values into `state.prev_claims`, assigned the already-known challenge to
`state.batching_challenge`, and used that pair to compute layer 1's initial
claim. The coefficient was therefore independent of four values it was meant
to batch.

This is a verifier acceptance bug, not merely a producer serialization
mismatch. The values were eventually checked by cache relations, but those
checks did not make the already-sampled batching coefficient depend on them.

## Bounded accepting flow

The affected generated layer supplies four late values
`X = (x0, x1, x2, x3)`. One already-bound vector-lookup cache value constrains
them by one equation of the form:

```text
C = x0 + beta*x1 + beta^2*x2 + beta^8*x3
```

The next layer uses the already-revealed batching challenge `alpha` to retain
only one randomized combination:

```text
B = x0 + alpha*x1 + alpha^2*x2 + alpha^3*x3
```

After observing `alpha`, choose a nonzero delta vector satisfying both
homogeneous equations:

```text
delta0 + beta*delta1 + beta^2*delta2 + beta^8*delta3 = 0
delta0 + alpha*delta1 + alpha^2*delta2 + alpha^3*delta3 = 0
```

There are at most two linear constraints on four extension-field unknowns, so
a nonzero solution exists. Replacing `X` with `X + delta` preserves the cache
check and the single next-layer batched claim while making individual
evaluations false. Layer 2's final-step check covered only the 16 ordinary
values; layer 1 consumes only the batched scalar, so no later individual check
removes this freedom. Absorbing `X + delta` afterward merely determines later
challenges and cannot retroactively make `alpha` depend on it.

## Impact and fix

The verifier accepted a false local GKR layer handoff: individual evaluations
could differ from their polynomials while all checked compressed relations
remained unchanged. The review did not establish an end-to-end false public
machine statement, so the claim is component soundness rather than a broader
system exploit.

The generator repair in `3edc1b9a` splits each affected layer handoff into a
pre-draw phase and a post-draw fold. The pre-draw phase appends all extra cache
evaluations to the ordinary evaluation buffer, absorbs the complete logical
message once, and only then samples `next_batching`. The post-draw phase merely
merges/folds the already-bound claims. Commit `1eae11ea` regenerated the actual
Rust verifier artifacts with that ordering; reviewing only the generator would
have missed that the artifacts checked in by `3edc1b9a` were still stale.

## Regression

- Build a layer whose only new dependency is introduced by a cache relation and assert that value appears before the first dependent squeeze.
- Mutate any extra evaluation and require `next_batching_challenge` to change.
- Compare the exact framing of `ordinary || extras`; do not accept two absorbs as automatically equivalent to one.
- Differential-test no-cache, one-cache, overlapping-cache, and several-cache layers.
- Add a negative algebraic test with inconsistent individual cache claims that could cancel only after challenge observation.

## Reproduction evidence

```sh
git diff 10651d7a1d29e3010e126bc7a78a971ae45d7595 3edc1b9a2374760be4d6aca7beaf9d4ffae4ad87 -- verifier_generator/src/gkr/mod.rs
git diff 3edc1b9a2374760be4d6aca7beaf9d4ffae4ad87 1eae11eaf06bd47f67045ae849bed7fb42aa37c2 -- verifier/src/generated/mem_subword_only/sec_100/gkr.rs
```
