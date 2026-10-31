# Commitment geometry and backend limits

GPU admission checks the requested configuration against the existing field,
representation and kernel requirements. Presets choose defaults; membership in a
preset or a previously tested tuple is not a capability condition. Memory-policy
validity and arena capacity are checked separately. See
[memory policies](../execution_prover/docs/memory_policies.md).

For a base commitment, `m` is the message log, `ell` is the LDE log, `k` is the
physical column-packing log and `f` is the base fold log. Physical packing and
base folding are independent. Recursive notation uses `t` for the coefficient
log, `v` for the leaf-value log and `r = t - v` for the residue log.

## Base commitments and ownership

This table describes geometry-backed, naturally labeled base commitments. Legacy
holders retain their separate routing; it is not substituted for these paths.

| Requirement | Mechanism | Source |
| --- | --- | --- |
| Base message `13 <= m <= 24` | The natural-to-bitrev initial-eight pass needs `N/8192` blocks; the generated family ends at 24. | [NTT transform validation](../ntt/src/ntt/mod.rs), [base geometry](../trace/src/trace/holder/mod.rs) |
| `m + ell <= 27`, also within the live twiddle capacity | BabyBear root order and context tables must cover the evaluation domain. | [base geometry](../trace/src/trace/holder/mod.rs) |
| Base fold `f` is 0 or 1 | These are the generated base reader/batching paths. | [recursive schedule admission](../whir/src/lib.rs), [separate producer](../trace/src/trace/memory.rs) |
| Cap at least LDE; Partial-tree depth at least five | Each coset needs an integral cap share. Equality is valid: the five-level reduction roots are already the cap and need no upper-node launch. | [holder layout](../trace/src/trace/holder/mod.rs), [Merkle trees](../hash/src/blake2s/merkle.rs) |
| Memory-only production uses the separate producer | A merged proof needs the concatenating memory/witness producer. Configuration, artifact, cap, program and cached request identities must agree before work. | [merged commitment](../circuit_prover/src/proof/merged_commitment.rs), [setup host](../execution_prover/src/precomputations/setup_host.rs) |
| Destructive transforms require exclusive raw backing | Logical readers and merged aliases must finish before raw is consumed. InPlace commitment restores every raw value, including padded zeros, before logical readers resume. | [openings](../trace/src/trace/holder/openings.rs) |

InPlace and retained monomials share the base-transform range `13..=24`.
At m13..19, raw-to-monomials uses the existing compact Mobius passes; forward
cosets use initial-eight plus last-K stages, `K = m - 8`. The inverse explicitly
uses compact K+8 DIF, including at m13 where the ordinary Forward selector may
choose DIT. Its final-eight pass normalizes and removes the coset shift once.
Raw restoration uses the existing addition-stage kernel: m launches per nonempty
column, each with `N/512` blocks of 256 threads and no shared memory. It adds no
full-column scratch allocation. The m20..24 routes retain their existing wiring.
See [InPlace](../ntt/src/ntt/in_place.rs),
[retained monomials](../ntt/src/ntt/retained_monomials.rs) and
[hypercube transforms](../ntt/src/ntt/hypercube.rs).

Recomputed queries accept None or Partial trees; the existing gather does not
read Full-tree storage. The direct retained commitment entry requires None
cosets and Partial trees. Opening and commitment checks enforce these lifecycle
requirements before cap/workspace allocation or taking the raw owner. A smaller
message does not relax ownership or change coefficient labeling.

Physical claim merging supports `k=1..=5`; k0 bypasses that kernel. Each packed
group must stay within one warp for its XOR-shuffle reduction. At k6 a group
spans two warps and needs a cross-warp exchange that the kernel does not provide.
See [packed merge](../gkr/src/packed_merge.rs) and its
[native implementation](../gkr/native/ops/packed_merge.cu).

## Recursive commitments

Field/context bounds and the five-level Partial-tree requirement apply before
route selection. A fused selection miss falls through to the existing retained
route; a fast-path limit is not a global rejection.

| Route or operation | Current requirement | Mechanism/source |
| --- | --- | --- |
| Fused Subwarp | `r <= 4`, `v <= 8`, and `max(coefficient staging, hash scratch) <= 48 KiB` | No dynamic shared-memory opt-in is configured. The `16 * 2^t` coefficient term implies `t <= 11`. [fused selection](../whir/src/fused_commit.rs) |
| Fused Block | `5 <= r <= 8`, `V >= 4`, and the reader's `v <= 8` | One block has `2^r` residue threads, bounded by 256; the existing block transform processes four E4 slots per tile. [fused selection](../whir/src/fused_commit.rs) |
| Recomputed in-domain leaves | `v <= 8` and field/context domain bounds | The reader has 256 value slots and computes an unsigned `8 - v`; rows use a strided loop. [in-domain wrapper](../whir/src/in_domain.rs) |
| Retained hashing/gather | `r >= 5`, `v <= 13` | A coset needs the 32-leaf boundary. Four BF limb columns times `2^v` must fit CUDA grid Y (65535); v14 needs 65536 columns. [admission](../whir/src/lib.rs), [gather](../hash/src/blake2s/gather.rs) |
| Retained forward transform | Generated dispatch through `r <= 24`; current staging further requires `r <= 20` | A complete coset must fit the fixed 32 MiB / `2^20`-digest staging buffer before hashing. [oracle commitment](../whir/src/oracle_commit.rs) |

The r21..24 retained limit is a fixed-staging implementation limit. A follow-up
could size staging as `max(2^20, per_coset_leaves).min(total_leaves)` and account
for that allocation in preflight. It would use 64–512 MiB at r21..24 and needs a
CPU-oracle boundary case at r21 (message log at least 22), with measured resource
cost. This wiring and its heavier validation are not part of the current path.

## Schedule and protocol constraints

The base query subgroup is strictly below BabyBear two-adicity, and recursive
LDE choices must preserve the historical-term subgroup containment condition.
The schedule validator checks these actual dimensions rather than a fixed
message size, fold ladder, LDE or cap tuple.

The GPU validates Naive and Windowed same-size schedule grammar but executes its
compiled windows. It does not construct a different Naive GPU scheduler. F13
compares fresh Naive CPU proof bytes with two queued GPU proofs; the same-pin
Windowed control has identical main/DR launch dispatch.

The DR fused prefix is a selector: chains of at least seven rounds use seven;
shorter positive chains use zero pairs and the existing tower from round zero.
Zero-layer chains remain rejected because their transcript/handoff path is not
implemented. Backward folding-step, claim-point and tail-capacity checks still
apply. Execution workers request explicit output log 4; preflight binds this to
the config. Other output logs are available through the direct circuit-prover
API. See [proof preflight](../circuit_prover/src/proof/mod.rs) and
[forward DR](../gkr/src/forward/dimension_reducing.rs).

Multiple OOD samples and folding/OOD PoW remain rejected on this head: their
additional transcript, nonce-layout or grind steps are not wired here. These are
protocol implementation constraints, independent of memory-policy selection.
See [schedule admission](../whir/src/lib.rs) and
[proof inputs](../gkr/src/proof_layout/build_inputs.rs).

Allocation failure describes the actual workload, policy, arena and pending
jobs. A paired-proof non-fit is not a single-proof capability limit. Default
selection and tuning may prefer cheaper policies, but do not restrict callable
combinations. Primitive/holder parity establishes small-domain correctness;
full-circuit proof coverage is recorded separately in the stage evidence.
