# Base-field WHIR path used the wrong coset layout

## Classification

- Producer-parity history: confirmed historical GPU WHIR opening-construction bug
- Component: GPU base-oracle query value/path extraction
- Claim-chain location: transcript query index → LDE coset leaf → Merkle cap authentication
- Security character: honest GPU proof rejection after a CPU layout migration
- Fixed by: [`f2ce204`](https://github.com/matter-labs/zksync-airbender/commit/f2ce204b366b42175286cbc72077719a620c8307)
- Vulnerable revision: `2961e73dfc92af87268006a1ea739e93d608653f`

## Protocol context

The base WHIR oracle is physically represented as one tree over buckets of LDE cosets. CPU tree construction stores coset buckets in bit-reversed order, while the GPU keeps a separate tree per original LDE coset. A folded query index must therefore be translated consistently for three objects: leaf values, Merkle path, and the tree-space index recorded in the proof.

For raw folded index `i` and LDE factor `L`:

```text
coset_index      = i mod L
internal_index   = floor(i / L)
coset_dest       = bitreverse(coset_index, log2 L)
tree_index       = coset_dest * coset_tree_size + internal_index
```

GPU per-coset tree `coset_index` corresponds to CPU combined-tree bucket `coset_dest`; both use `internal_index` inside that bucket.

## Intended authentication relation

```text
value = gpu_coset_tree[coset_index].leaf(internal_index)
path  = gpu_coset_tree[coset_index].path(internal_index)
recorded_index = tree_index
verify_merkle(cap, value, path, recorded_index) == true
```

The transcript-derived raw query is not itself necessarily the index into the committed tree.

## Failure

After CPU queries changed to record and authenticate `tree_index`, GPU value lookup and path lookup still used different decompositions. Values followed the LDE coset/internal convention, but path retrieval retained the old raw-index/coset-tree convention involving `index % coset_tree_size` and a separately bit-reversed path coset.

The selected value and authentication path could therefore refer to different leaves. The recorded index had already been migrated, so parity first failed at the path comparison.

## Failure flow

1. Draw raw folded index `i` in a nontrivial coset.
2. Read the expected leaf value from GPU tree `coset_index` at `internal_index`.
3. Read a Merkle path from a different per-coset tree or internal slot using the stale decomposition.
4. Record CPU-style `tree_index` in the proof.
5. Canonical verification hashes the provided leaf/path at `tree_index` and rejects.

If an accepting verifier instead applied the stale mapping to the algebraic query while authenticating another position, a prover could answer with a committed value unrelated to the requested codeword location. Historical evidence here establishes GPU/CPU mismatch; verifier reachability must be shown separately.

## Impact and fix

Honest GPU base-oracle openings failed once the CPU/tree-index convention changed. The fix computes one `internal_index = query_index / lde_factor`, uses the original LDE `coset_index` to select both GPU value and path buffers, and records the corresponding bit-reversed combined-tree index.

Merkle review must start from physical leaf layout. Reusing variable names such as `index`, `row`, or `coset` across raw-domain, bucket, leaf, and tree spaces is a recurring source of authenticated-wrong-position bugs.

## Regression

- Enumerate first/last internal positions of every coset and boundaries around `L` and `coset_tree_size`.
- Independently recompute raw, coset, internal, destination, and tree indices.
- Require value, path, and recorded index to verify under one cap.
- Reject the same value/path under the raw folded index and under adjacent cosets.
- Differential-test CPU combined-tree and GPU per-coset layouts for multiple LDE factors and leaf packing widths.

## Reproduction evidence

```sh
git diff 2961e73dfc92af87268006a1ea739e93d608653f f2ce204b366b42175286cbc72077719a620c8307 -- gpu_prover/src/prover/whir_fold.rs
```
