# Cached evaluations were absorbed in the wrong scope

## Classification

- Confirmed historical prover/verifier transcript-parity bug
- Component: GKR sumcheck layer transition with cached relations
- Security character: noncanonical message framing and honest-proof rejection; no standalone false-acceptance path was established by this prover-side bug
- Fixed by: [`c9d8620`](https://github.com/matter-labs/zksync-airbender/commit/c9d8620d2f549781be154c6813264330b63b8a94)
- Vulnerable revision: `e0b57de405ba1e66dbc8da572e9ac73a8d266726`

## Protocol context

At a GKR layer boundary, ordinary output claims and any extra evaluations required by cached relations form one prover message. Only after that complete message is fixed may the next batching challenge be derived. The cache relations are implementation structure; they must not change the transcript grammar for the same logical layer message.

The extra values were accumulated in a deterministic map, but deterministic iteration alone does not solve message framing. The transcript must absorb the final flattened set once, at the protocol boundary shared with the verifier.

## Intended transcript relation

```text
evaluate all cache relations
collect unique extra dependency evaluations in canonical key order
layer_message = ordinary new claims || extra evaluations
absorb(layer_message exactly once)
next_batching_challenge <- squeeze(seed)
```

This example concerns the scope and multiplicity of absorption. Later historical examples cover the separate bugs in what belongs in `layer_message` and whether the transition happens when there are no cache relations.

## Failure

Extra evaluations needed to justify cached relations were committed while iterating the cache relations. As the map grew, absorption occurred according to loop iterations rather than once according to the logical layer message. Depending on the number and dependency overlap of cache relations, earlier values could appear in multiple transcript events and event placement differed from the verifier's canonical transition.

The values themselves could be correct and ordered, yet the rolling seed still diverged because Fiat-Shamir commits to a byte/event sequence, not an unordered mathematical set.

## Failure flow

1. Process the first cached relation and insert its dependency evaluation.
2. Absorb the current map contents inside the loop.
3. Process a second cached relation, possibly inserting another dependency.
4. Absorb the enlarged map again, duplicating the first value in the transcript history.
5. Draw a later batching or folding challenge from a seed the verifier does not reconstruct.

Zero, one, and several cache relations therefore exercised different transcript grammars. Tests using only one relation would not expose repeated-prefix absorption.

## Impact and fix

The bug caused transcript drift and honest-proof rejection once a layer used the affected cache shape. It also made the protocol message depend on internal loop decomposition, a dangerous property even when prover and verifier happen to share code.

The fix completes cache discovery first, iterates the deterministic `BTreeMap` once, and commits one flattened collection after the loop. That establishes a stable layer-level message boundary. Subsequent fixes then combined this collection with ordinary claims before the batching challenge and made the transition unconditional.

## Audit lesson

For every transcript call inside a loop, ask whether the protocol specifies one message per iteration or one message for the completed collection. Canonical sorting does not prevent duplicated prefixes, skipped empty collections, or challenge draws placed between partial messages.

## Regression

- Construct equivalent layers with zero, one, and several cache relations and compare an event-by-event transcript trace to the verifier.
- Use overlapping dependencies and assert each unique extra evaluation is absorbed once.
- Reorder cache-relation discovery while preserving the final map and require an identical seed.
- Assert the next challenge occurs only after the complete layer message.

## Reproduction evidence

```sh
git diff e0b57de405ba1e66dbc8da572e9ac73a8d266726 c9d8620d2f549781be154c6813264330b63b8a94 -- prover/src/gkr/prover/sumcheck_loop/mod.rs
```
