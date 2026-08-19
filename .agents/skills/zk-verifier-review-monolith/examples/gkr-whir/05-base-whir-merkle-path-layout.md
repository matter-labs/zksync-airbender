# Base-field WHIR path used the wrong coset layout

## Classification

- Confirmed historical WHIR query-authentication bug
- Fixed by: [`f2ce204`](https://github.com/matter-labs/zksync-airbender/commit/f2ce204b366b42175286cbc72077719a620c8307)
- Vulnerable revision: `2961e73dfc92af87268006a1ea739e93d608653f`

## Failure

Base-field query values came from the LDE coset and internal position expected by CPU layout, but GPU Merkle paths decomposed the raw query index using the old coset-tree convention. Value and path could refer to different leaves after the CPU switched to tree-space indices.

## Impact and fix

Honest GPU openings failed authentication, and a verifier mirroring the same mistake could authenticate the wrong position. The fix derives both value and path from the same bit-reversed coset bucket and internal leaf index.

## Regression

For every coset/internal boundary, recompute the leaf index independently and verify value, stored index, and path against one root.

```sh
git diff 2961e73dfc92af87268006a1ea739e93d608653f f2ce204b366b42175286cbc72077719a620c8307 -- gpu_prover/src/prover/whir_fold.rs
```
