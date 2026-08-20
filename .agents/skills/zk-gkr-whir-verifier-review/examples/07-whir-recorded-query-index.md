# WHIR proof recorded raw rather than tree-space query indices

## Classification

- Confirmed historical WHIR proof-format/index-provenance bug
- Component: GPU base and extension query serialization
- Claim-chain location: transcript query bits → derived tree position → serialized opening
- Security character: GPU proof parity failure; trusting the proof-supplied label would create positional malleability
- Fixed by: [`2961e73`](https://github.com/matter-labs/zksync-airbender/commit/2961e73dfc92af87268006a1ea739e93d608653f)
- Vulnerable revision: `cb3787df94900baed4b675b472c30b78c56d9b2e`

## Protocol context

WHIR query positions originate from transcript-derived bits. The oracle layout then deterministically maps each folded-domain query to a Merkle-tree-space index. The proof structure duplicated that derived index alongside the values and path for CPU/GPU serialization parity.

Such a field is not fresh prover input. A verifier must either recompute it and use the result or compare the supplied copy exactly. Treating it as an authoritative label lets the prover choose which committed position a transcript query opens.

## Intended index derivation

```text
raw_index      <- transcript query bits
coset          = raw_index mod num_cosets
internal       = floor(raw_index / num_cosets)
tree_index     = bitreverse(coset, log_num_cosets) * coset_tree_size + internal
proof.index    = tree_index                  # redundant serialization copy
verifier_index = recompute(raw_index, geometry)
assert proof.index == verifier_index         # if the field is retained
```

The empty-column path follows the same positional convention even though it has no leaf payload.

## Failure

After canonical CPU queries switched `BaseFieldQuery.index` and `ExtensionFieldQuery.index` to tree space, GPU fill helpers continued writing the raw folded index. The stale assignment existed in populated base queries, zero-column base short-circuits, and extension queries.

Other query fields were being migrated separately, so a proof could contain correct values/path but an inconsistent positional label. The first parity assertion failed before later path-layout repairs.

## Failure flow

1. Derive raw index `i` from the Fiat-Shamir query stream.
2. Compute/fetch an opening using the oracle's bit-reversed tree geometry.
3. Serialize `i` rather than the resulting `tree_index` in `query.index`.
4. Canonical verifier/CPU comparison interprets that field in tree space.
5. Reject or authenticate under the wrong position if the field is trusted.

The direct historical outcome was GPU/CPU incompatibility. The security lesson is stronger: every proof field derivable from challenges and parameters needs an explicit provenance check.

## Impact and fix

GPU proofs used a stale query format across base, extension, and empty-column paths. The fix threads `coset_tree_size` and `log_lde_factor` where needed, computes the bit-reversed tree index, and stores it uniformly.

Derived proof labels should generally be removed from the wire. If retained for compact verification or tooling, verify them before they influence Merkle or algebraic checks.

## Regression

- Recompute every serialized index from transcript query bits and exact oracle geometry.
- Mutate only `proof.index` while preserving value/path and require rejection.
- Exercise queries where raw and tree indices coincide and differ, so accidental equality does not hide the bug.
- Cover zero-column commitments as well as populated base and extension oracles.
- Round-trip CPU/GPU proof structures and compare semantic indices, not only byte lengths.

## Reproduction evidence

```sh
git diff cb3787df94900baed4b675b472c30b78c56d9b2e 2961e73dfc92af87268006a1ea739e93d608653f -- gpu_prover/src/prover/whir.rs gpu_prover/src/prover/whir_fold.rs
```
