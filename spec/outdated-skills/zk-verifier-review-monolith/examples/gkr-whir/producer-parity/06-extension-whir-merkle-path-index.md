# Extension WHIR path used the raw folded index

## Classification

- Producer-parity history: confirmed historical GPU WHIR extension-opening construction bug
- Component: GPU intermediate/extension oracle queries
- Claim-chain location: folded query index → bit-reversed combined-tree leaf/path
- Security character: GPU/canonical-verifier incompleteness
- Fixed by: [`a07715f`](https://github.com/matter-labs/zksync-airbender/commit/a07715f105917ff9247e5d06049c3d41bceeef2f)
- Vulnerable revision: `f2ce204b366b42175286cbc72077719a620c8307`

## Protocol context

Intermediate WHIR oracles contain extension-field values packed into one combined Merkle tree. Their logical row order bit-reverses the coset component. Unlike the base-oracle GPU layout, there is not a separate per-coset tree: values and authentication paths must both address the same combined `tree_index`.

```text
coset_index    = raw_index mod lde_factor
internal_index = floor(raw_index / lde_factor)
tree_index     = bitreverse(coset_index) * packed_leaf_count + internal_index
```

This index also becomes the proof query's positional label.

## Intended authentication relation

```text
leaf  = combined_tree.get_leaf(tree_index)
path  = combined_tree.get_path(tree_index)
proof_query.index = tree_index
Merkle verifier authenticates leaf/path at tree_index under the round cap
```

The raw folded index remains useful only to derive the tree index and evaluation-domain point.

## Failure

GPU value retrieval used the correct bit-reversed `logical_row_index`, but Merkle path retrieval used the raw folded query index. A prior migration had already changed the proof's recorded index to CPU-style tree space, leaving three index consumers on two conventions.

The value was a committed leaf, and the path was a valid path, but they generally did not belong together. This demonstrates why independently correct components do not imply a valid opening tuple.

## Failure flow

1. Draw a raw query whose coset bit reversal changes its position.
2. Fetch the extension value at `tree_index`.
3. Fetch the authentication path at `raw_index`.
4. Record `tree_index` in the query object.
5. Canonical Merkle verification combines the value with a sibling path from another position and rejects.

If a verifier were to trust the raw proof index or repeat this split, the authenticated value could be disconnected from the evaluation point used in the WHIR fold. The historical fix itself is a producer parity repair.

## Impact and fix

Extension-oracle openings failed at nontrivial cosets after CPU layout correction. The fix computes `tree_index` once and uses a single host/device index buffer for value lookup, path lookup, and recorded query index in both direct and callback-driven query paths.

Prefer one strongly named index value per physical space and eliminate redundant buffers. Duplicate derivations invite partial migrations where one consumer remains stale.

## Regression

- Choose queries for which `raw_index != tree_index` and assert both value and path use tree space.
- Verify `hash(leaf, path, tree_index)` against the cap and reject under `raw_index`.
- Cover initial, recursive, and final intermediate oracles.
- Test multiple packing widths and LDE factors.
- Compare asynchronous and synchronous decode paths, which historically stored index fields separately.

## Reproduction evidence

```sh
git diff f2ce204b366b42175286cbc72077719a620c8307 a07715f105917ff9247e5d06049c3d41bceeef2f -- gpu_prover/src/prover/whir.rs
```
