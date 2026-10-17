# Memory-tuple cache claims were not bound to their base columns

## Classification

- Confirmed historical proof-system soundness bug
- Component: generated verifier checks for GKR circuit cache relations
- Bug class: cached relation omitted from verifier generation
- Fixed by: [`7eca15a`](https://github.com/matter-labs/zksync-airbender/commit/7eca15a5a3781e7b6143d1873f8a4c86ad80b527), PR [#334](https://github.com/matter-labs/zksync-airbender/pull/334)
- Vulnerable revision for reproduction: `7f0f5f63e0575daa8f01f1c1f21ade6906e65bc8`

## Intended relation

A `MemoryTuple` cache is the random linearization of the committed address, timestamp, value, and access metadata used by the memory permutation argument. At every GKR opening point, its claimed evaluation must equal the same expression recomputed from the corresponding base-column claims and the externally derived memory challenges.

## Vulnerable relation

`generate_cache_relation_checks` explicitly matched `NoFieldGKRCacheRelation::MemoryTuple(_)` and emitted no check. The GKR proof could be internally consistent with a prover-supplied cache claim without establishing that the cache was derived from the committed memory columns.

## Security impact

The memory grand product then authenticated a detached cache polynomial rather than the circuit's actual address/timestamp/value tuples. Local circuit constraints and the global RAM product could each verify while referring to different memory events, defeating the intended memory binding.

## Fix

Verifier generation now collects every `MemoryTuple` relation, reconstructs its challenged tuple expression from base-column claims, and compares the result with the cached claim. It returns `GkrPermutationCacheRelationFailed` on mismatch and fails closed for an address variant whose reconstruction is not implemented.

## Audit lesson

Every compiler cache is a new proof obligation. Enumerate the cache-relation variants on both prover and verifier paths and demand a total correspondence; an empty match arm is not harmless just because the cached polynomial participates in later sumchecks.

## Regression test

- Unit-test verifier generation so every `MemoryTuple` variant emits a comparison against all declared dependencies.
- For a valid proof fixture, independently recompute the tuple evaluation from opened base columns and assert equality with the cache claim.
- Add a fail-closed test for unsupported address encodings and a structural test that no cache-relation enum variant maps to an empty verifier block.

## Reproduction evidence

```sh
git diff 7f0f5f63e0575daa8f01f1c1f21ade6906e65bc8 7eca15a5a3781e7b6143d1873f8a4c86ad80b527 -- \
  verifier_generator/src/gkr/mod.rs
```
