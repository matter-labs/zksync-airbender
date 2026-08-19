# Extension WHIR path used the raw folded index

## Classification

- Confirmed historical WHIR extension-oracle authentication bug
- Fixed by: [`a07715f`](https://github.com/matter-labs/zksync-airbender/commit/a07715f105917ff9247e5d06049c3d41bceeef2f)
- Vulnerable revision: `f2ce204b366b42175286cbc72077719a620c8307`

## Failure

Extension query values used `tree_index = bitreverse(coset) * packed_leaf_count + internal`, while Merkle path retrieval still used the raw folded query index.

## Impact and fix

The opening value and authentication path addressed different tree positions. The fix uses one tree index for values, paths, and the proof's recorded index and deletes redundant path-index buffers.

## Regression

At nontrivial cosets, assert `hash(value, path, recorded_index) == cap` and reject the same path under the raw folded index.

```sh
git diff f2ce204b366b42175286cbc72077719a620c8307 a07715f105917ff9247e5d06049c3d41bceeef2f -- gpu_prover/src/prover/whir.rs
```
