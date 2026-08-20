# Batching challenge lived inside an optional cache branch

## Classification

- Confirmed historical optional-path challenge bug
- Component: GKR sumcheck layer transition
- Security character: missing canonical transition on cache-free layers; primarily producer correctness/parity in the historical location
- Fixed by: [`2df0dea`](https://github.com/matter-labs/zksync-airbender/commit/2df0dea2b68bd6ab6070484277feb9d16435c934)
- Vulnerable revision: `9050461d9830eb83405b683ae526e635bc91d3a5`

## Protocol context

Every nonterminal GKR layer produces claims for the next layer and needs a fresh coefficient to batch those claims. Cache relations only add optional fields to that layer message; they do not determine whether the protocol transition exists.

This distinction is easy to lose when transcript code is written next to optional claim discovery. The protocol round is unconditional even when the optional payload is empty.

## Intended transcript relation

```text
transcript_inputs = ordinary new claims
if cache relations exist:
    transcript_inputs += canonical extra evaluations
absorb(transcript_inputs exactly once)
next_batching_challenge <- squeeze(seed exactly once)
```

The branch controls only construction of `extras`, never the absorb-and-draw boundary.

## Failure

After the prior ordering repair, the combined absorb and `next_batching_challenge` draw remained nested inside `if let Some(cache_relations)`. A layer without cache relations skipped the entire canonical transition even though it still had ordinary `new_claims` and still needed next-layer batching randomness.

Depending on surrounding control flow, this can leave the challenge absent/uninitialized, reuse stale state, or cause prover/verifier transcript drift. More generally, it makes the transcript language depend on an implementation optimization rather than on the proof protocol.

## Failure flow

1. Finish a valid layer that has ordinary output claims but no cache metadata.
2. Initialize the transcript input with those claims.
3. Skip the optional branch, thereby absorbing nothing and drawing no next challenge.
4. Continue toward a next layer whose batched claim conceptually requires fresh randomness.
5. Diverge from a verifier that performs the protocol transition, or incorrectly reuse/omit randomness if another path supplies a default.

The historical diff is in prover code, so the directly established outcome is broken proof construction/parity. A verifier implementation with the same conditionality would require separate analysis for challenge reuse or unbound next-layer claims.

## Impact and fix

Cache-free layers did not follow the same layer-transition transcript as cached layers. The fix moves the single combined absorption and challenge draw after the optional block. Every layer now performs the transition exactly once; the optional branch merely appends extra values.

Audit early returns, empty collections, feature flags, zero-width layers, and `Option` branches around every transcript event. The absence of an optional prover field rarely means the surrounding protocol round disappears.

## Regression

- Compare event traces for otherwise equivalent layers with zero and one cache relation; both must contain one layer-message absorb and one batching squeeze.
- Assert the no-cache transcript still binds all ordinary `new_claims`.
- Count event multiplicity: exactly once for empty, singleton, and multi-cache cases.
- Poison or remove any default batching coefficient so skipped initialization fails loudly in tests.
- Compare the seed entering the next layer across prover and every verifier implementation.

## Reproduction evidence

```sh
git diff 9050461d9830eb83405b683ae526e635bc91d3a5 2df0dea2b68bd6ab6070484277feb9d16435c934 -- prover/src/gkr/prover/sumcheck_loop/mod.rs
```
