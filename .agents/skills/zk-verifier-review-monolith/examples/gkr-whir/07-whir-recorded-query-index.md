# WHIR proof recorded raw rather than tree-space query indices

## Classification

- Confirmed historical WHIR proof-format bug
- Fixed by: [`2961e73`](https://github.com/matter-labs/zksync-airbender/commit/2961e73dfc92af87268006a1ea739e93d608653f)
- Vulnerable revision: `cb3787df94900baed4b675b472c30b78c56d9b2e`

## Failure

After the canonical prover changed query records to Merkle-tree-space indices, GPU fill helpers continued storing the raw folded index for both base and extension queries, including empty-column paths.

## Impact and fix

The verifier interpreted a valid leaf/path under a different position. The fix records the bit-reversed coset tree index everywhere. Proof fields that duplicate derived indices must be recomputed or checked, never trusted as labels.

## Regression

Recompute every recorded index from the transcript query bits and oracle geometry; mutate the proof's index while keeping values and path fixed and require rejection.

```sh
git diff cb3787df94900baed4b675b472c30b78c56d9b2e 2961e73dfc92af87268006a1ea739e93d608653f -- gpu_prover/src/prover/whir.rs gpu_prover/src/prover/whir_fold.rs
```
