# Proof-slab parsing dropped final WHIR fields

## Classification

- Confirmed historical GKR-to-WHIR proof-serialization bug
- Fixed by: [`7fe3e70`](https://github.com/matter-labs/zksync-airbender/commit/7fe3e70c8819d99af15666bb952c73a5f32d01f4)
- Vulnerable revision: `fee74f8bf75415472412cd2e52d2230361586d68`

## Failure

After a rebase, slab parsing hardcoded `final_monomials_len = 0` and retained raw folded indices, overwriting final monomials and tree-space query indices already computed by ordered host callbacks.

## Impact and fix

The serialized proof lost data required for final polynomial evaluation and Merkle verification. The fix bridges both fields from the authoritative host-side proof. Every alternate serializer must preserve all semantically checked fields, including derived indices.

## Regression

Round-trip a proof through each storage path and compare semantic structures, not just slab byte lengths.

```sh
git diff fee74f8bf75415472412cd2e52d2230361586d68 7fe3e70c8819d99af15666bb952c73a5f32d01f4 -- gpu_prover/src/prover/proof.rs
```
