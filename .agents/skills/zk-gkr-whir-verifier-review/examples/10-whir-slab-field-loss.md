# Proof-slab parsing dropped final WHIR fields

## Classification

- Confirmed historical GKR-to-WHIR proof-serialization bug
- Component: GPU slab-parsed proof assembly versus host-callback proof state
- Claim-chain location: terminal polynomial and query authentication data → serialized verifier input
- Security character: honest proof corruption; alternate serializers can become verifier bypasses if omitted fields receive permissive defaults
- Fixed by: [`7fe3e70`](https://github.com/matter-labs/zksync-airbender/commit/7fe3e70c8819d99af15666bb952c73a5f32d01f4)
- Vulnerable revision: `fee74f8bf75415472412cd2e52d2230361586d68`

## Protocol context

GPU proof construction had two storage paths. Device kernels wrote a compact proof slab, while ordered host callbacks populated fields that depended on asynchronous readback or corrected index derivation. Final assembly parsed the slab into a proof object and separately obtained the authoritative host-side WHIR proof.

The semantic proof includes more than the slab's bulk arrays. The terminal monomial coefficients close the final WHIR polynomial claim, and every intermediate query's tree-space index identifies the authenticated leaf.

## Intended serialization contract

```text
final proof = slab-owned fields
            + host-callback final_monomials
            + host-callback base query structures
            + host-callback intermediate query structures/indices

deserialize(serialize(proof)) preserves every verifier-consumed semantic field
```

There must be one documented authority for each field when representations overlap.

## Failure

After a rebase, slab parsing hardcoded `final_monomials_len = 0`, yielding an empty terminal polynomial. It also copied raw folded query indices from the slab over tree-space indices already computed by host callbacks. Final assembly preserved host-side base queries but failed to bridge these two additional fields.

The proof object therefore looked structurally complete while losing exactly the fields needed for terminal evaluation and intermediate Merkle positioning.

## Failure flow

1. GPU/host callbacks correctly compute final monomials and bit-reversed tree indices.
2. Device slab contains no final monomials and stale raw indices.
3. Final assembly parses the slab after callbacks finish.
4. Parsed defaults/stale fields overwrite or omit authoritative host values.
5. Serialize the corrupted proof to the canonical verifier.
6. Reject at terminal polynomial evaluation or query authentication.

This historical path is completeness failure. A verifier that interprets missing monomials as zero or ignores an index would create a separate fail-open bug, so parser defaults must be audited on both sides.

## Impact and fix

Valid GPU computation was destroyed at the final storage handoff, breaking proofs after the algebra itself had succeeded. The fix copies `final_monomials` and the entire `intermediate_whir_oracles` structure from the host proof into the slab-parsed proof, following the existing base-query override pattern.

Serializer audits need a field-by-field semantic inventory, including values recomputable from challenges. Byte-length equality or successful deserialization is not enough.

## Regression

- Round-trip a proof through direct-host, slab, and wire formats and compare semantic structures.
- Require nonempty terminal monomials of the configured length.
- Choose queries where raw and tree indices differ.
- Mutate or omit each bridged field and require canonical verifier rejection.
- Assert each proof field has exactly one authoritative producer or an explicit equality check between producers.

## Reproduction evidence

```sh
git diff fee74f8bf75415472412cd2e52d2230361586d68 7fe3e70c8819d99af15666bb952c73a5f32d01f4 -- gpu_prover/src/prover/proof.rs
```
