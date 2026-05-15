use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;

use super::EXT4_DEGREE;
use crate::ops::blake2s::Digest;
use crate::primitives::context::{DeviceAllocation, HostAllocation};
use crate::primitives::field::{BF, E4};
use crate::prover::pow::PowAndQueryIndexesState;
use crate::prover::proof::layout::ProofLayout;
use crate::prover::whir::GpuWhirScheduledExtensionQuery;

/// D2D-copy the device-resident unified base-layer Merkle cap into the slab's
/// `whir.{setup,memory,witness}.cap` range. The unified cap is already in the
/// canonical bit-reversed coset order (`stage1_pos = 0..lde_factor`) that the
/// slab and the verifier-side proof object expect, so this is a single
/// contiguous D2D — no per-coset H2Ds, no host pointer tables, no gather
/// kernel. `None` slab is a no-op (test paths).
pub(super) fn copy_base_layer_cap_to_slab(
    unified_device_cap: &DeviceAllocation<Digest>,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    kind: crate::prover::proof::layout::WhirBaseLayerKind,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()> {
    let Some(slab) = proof_slab else {
        return Ok(());
    };
    // SAFETY: `ProofLayout` computes a live, non-overlapping mutable region for
    // this cap kind inside the slab allocation.
    let (dst_ptr, dst_len_u32) =
        unsafe { proof_layout.whir_base_cap_device_mut(slab.as_ptr() as *mut u8, kind) };
    if dst_len_u32 == 0 {
        return Ok(());
    }
    let digest_u32_words = crate::prover::proof::layout::DIGEST_U32_WORDS;
    assert_eq!(
        unified_device_cap.len() * digest_u32_words,
        dst_len_u32,
        "unified cap size must match slab whir base cap range",
    );
    // SAFETY: `Digest = [u32; DIGEST_U32_WORDS]` is transparent over `[u32]`;
    // reinterpreting the device allocation as a `DeviceSlice<u32>` is
    // layout-safe.
    let src_u32 = unsafe { unified_device_cap.transmute::<u32>() };
    // SAFETY: `dst_ptr` points at a 16-byte-aligned, live, disjoint region
    // inside the slab allocation.
    let dst = unsafe { era_cudart::slice::DeviceSlice::from_raw_parts_mut(dst_ptr, dst_len_u32) };
    memory_copy_async(dst, src_u32, stream)
}

/// Phase 3: H2D-copy one intermediate WHIR query's pinned host data into
/// the slab's `whir.intermediate[round].query_{indices,leaves,paths}`
/// sub-ranges at `query_idx`. `query_index_host` must be the single-element
/// pinned buffer already scheduled for the folded query lookup. Leaf values
/// copy directly from the query's pinned host allocation; merkle paths are
/// flattened into a temporary pinned `[u32]` staging buffer via a scheduled
/// host callback before the H2D. `None` slab is a no-op (test paths).
pub(super) fn copy_intermediate_query_to_slab(
    query_index_host: &HostAllocation<[u32]>,
    query: &mut GpuWhirScheduledExtensionQuery,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    round: usize,
    query_idx: usize,
    stream: &era_cudart::stream::CudaStream,
    context: &crate::primitives::context::ProverContext,
) -> CudaResult<()> {
    let Some(slab) = proof_slab else {
        return Ok(());
    };
    let digest_u32_words = crate::prover::proof::layout::DIGEST_U32_WORDS;

    // Index (single u32 at `query_idx` in `all_indexes_accessor`).
    // SAFETY: `ProofLayout` computes a live, non-overlapping mutable region for
    // the query-index array of this round.
    let (idx_ptr, idx_total_len) = unsafe {
        proof_layout.whir_intermediate_query_indices_device_mut(slab.as_ptr() as *mut u8, round)
    };
    if idx_total_len == 0 {
        return Ok(());
    }
    assert!(query_idx < idx_total_len);
    // SAFETY: single-slot write inside the slab index array.
    let idx_dst =
        unsafe { era_cudart::slice::DeviceSlice::from_raw_parts_mut(idx_ptr.add(query_idx), 1) };
    memory_copy_async(idx_dst, query_index_host, stream)?;

    // Leaves: `values_per_leaf * EXT4_DEGREE` `BF` → `values_per_leaf` `E4`
    // slots (byte-equivalent). Write as `BF` into the slab, treating the
    // E4 slot as a `[BF; 4]` array.
    // SAFETY: `ProofLayout` computes a live, non-overlapping mutable region for
    // the query leaves of this round.
    let (leaves_ptr_e4, leaves_total_e4) = unsafe {
        proof_layout.whir_intermediate_query_leaves_device_mut(slab.as_ptr() as *mut u8, round)
    };
    let leaf_values_len_e4 = leaves_total_e4 / idx_total_len;
    let leaves_src_len_bf = leaf_values_len_e4 * EXT4_DEGREE;
    assert_eq!(query.leafs_host().len(), leaves_src_len_bf);
    // SAFETY: slab `E4` slot at `query_idx` offset has `leaf_values_len_e4 * 4`
    // BFs worth of storage.
    let leaves_dst = unsafe {
        era_cudart::slice::DeviceSlice::from_raw_parts_mut(
            leaves_ptr_e4.add(query_idx * leaf_values_len_e4) as *mut BF,
            leaves_src_len_bf,
        )
    };
    memory_copy_async(leaves_dst, query.leafs_host(), stream)?;

    // Paths: flat Digest → `[u32]` reinterpret, `path_len` digests per query.
    // SAFETY: `ProofLayout` computes a live, non-overlapping mutable region for
    // the query merkle paths of this round.
    let (paths_ptr, paths_total_u32) = unsafe {
        proof_layout.whir_intermediate_query_paths_device_mut(slab.as_ptr() as *mut u8, round)
    };
    let paths_len_digests_per_query = paths_total_u32 / (idx_total_len * digest_u32_words);
    assert_eq!(query.merkle_paths_host().len(), paths_len_digests_per_query);
    // SAFETY: this pinned host staging buffer is written by the callback below
    // before the subsequent H2D reads from it.
    let mut paths_src_u32 = unsafe {
        context.alloc_host_uninit_slice::<u32>(paths_len_digests_per_query * digest_u32_words)
    };
    let paths_src_u32_accessor = paths_src_u32.get_mut_accessor();
    let paths_accessor = query.merkle_paths_accessor();
    query.callbacks_mut().schedule(
        // SAFETY: the callback is the sole writer of `paths_src_u32`, and it
        // runs before the H2D copy queued below.
        move || unsafe {
            let paths_src_digests = paths_accessor.get();
            let paths_src_u32 = paths_src_u32_accessor.get_mut();
            for (src, dst_words) in paths_src_digests
                .iter()
                .zip(paths_src_u32.chunks_exact_mut(digest_u32_words))
            {
                dst_words.copy_from_slice(src);
            }
        },
        stream,
    )?;
    // SAFETY: `paths_ptr` names the start of this round's path subrange and the
    // computed offset stays within that range for `query_idx`.
    let paths_dst = unsafe {
        era_cudart::slice::DeviceSlice::from_raw_parts_mut(
            paths_ptr.add(query_idx * paths_len_digests_per_query * digest_u32_words),
            paths_src_u32.len(),
        )
    };
    memory_copy_async(paths_dst, &paths_src_u32, stream)?;

    Ok(())
}

/// D2D-copy the intermediate WHIR oracle's unified device cap into the slab's
/// `whir.intermediate[round].cap` range. Intermediate WHIR oracles are built
/// with `log_lde_factor = 0`, so the unified cap is the single per-coset cap.
/// `None` slab is a no-op (test paths).
pub(super) fn copy_intermediate_cap_to_slab(
    unified_device_cap: &DeviceAllocation<Digest>,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    round: usize,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()> {
    let Some(slab) = proof_slab else {
        return Ok(());
    };
    // SAFETY: `ProofLayout` computes a live, non-overlapping mutable region for
    // this intermediate cap inside the slab allocation.
    let (dst_ptr, dst_len_u32) =
        unsafe { proof_layout.whir_intermediate_cap_device_mut(slab.as_ptr() as *mut u8, round) };
    if dst_len_u32 == 0 {
        return Ok(());
    }
    let digest_u32_words = crate::prover::proof::layout::DIGEST_U32_WORDS;
    assert_eq!(
        unified_device_cap.len() * digest_u32_words,
        dst_len_u32,
        "intermediate unified cap size must match slab whir intermediate cap range",
    );
    // SAFETY: `Digest = [u32; DIGEST_U32_WORDS]` is transparent over `[u32]`.
    let src_u32 = unsafe { unified_device_cap.transmute::<u32>() };
    // SAFETY: `dst_ptr` points at a 16-byte-aligned, live, disjoint region
    // inside the slab allocation.
    let dst = unsafe { era_cudart::slice::DeviceSlice::from_raw_parts_mut(dst_ptr, dst_len_u32) };
    memory_copy_async(dst, src_u32, stream)
}

/// Phase 3: H2D-copy the single-element `ood_value_host` pinned host buffer
/// into the slab's `whir.ood_samples[ood_idx]` offset. Scheduled on the same
/// stream as the preceding host callback that populates `ood_value_host`, so
/// stream ordering guarantees the H2D reads the post-callback value.
/// Transitional — the existing host callback write to
/// `shared_state.proof.ood_samples[..]` remains until Phase 4 sources
/// `ood_samples` from the slab via the terminal D2H. `None` slab is a no-op
/// (test paths).
pub(super) fn copy_ood_sample_to_slab(
    ood_value_host: &HostAllocation<[E4]>,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    ood_idx: usize,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()> {
    let Some(slab) = proof_slab else {
        return Ok(());
    };
    // SAFETY: `ProofLayout` computes a live, non-overlapping mutable region for
    // the OOD-sample array inside the slab allocation.
    let (dst_ptr, dst_len) =
        unsafe { proof_layout.whir_ood_samples_device_mut(slab.as_ptr() as *mut u8) };
    assert!(
        ood_idx < dst_len,
        "ood_idx {ood_idx} out of slab ood_samples range (len {dst_len})",
    );
    // SAFETY: `dst_ptr + ood_idx` is a 16-byte-aligned offset inside the live
    // `slab`; slots are disjoint by construction.
    let dst =
        unsafe { era_cudart::slice::DeviceSlice::from_raw_parts_mut(dst_ptr.add(ood_idx), 1) };
    memory_copy_async(dst, ood_value_host, stream)?;
    Ok(())
}

/// Phase 3: D2D-copy the single-element `d_nonce` device buffer into the slab's
/// `whir.pow_nonces[pow_round_idx]` offset. Transitional — the existing D2H
/// into `nonce_host` + callback path is left in place until Phase 4 parse
/// sources `pow_nonces` from the slab via the terminal D2H. `None` slab is a
/// no-op (test paths).
pub(super) fn copy_pow_nonce_to_slab(
    pow_round_state: &PowAndQueryIndexesState,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    pow_round_idx: usize,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()> {
    let Some(slab) = proof_slab else {
        return Ok(());
    };
    // SAFETY: `ProofLayout` computes a live, non-overlapping mutable region for
    // the PoW-nonce array inside the slab allocation.
    let (dst_ptr, dst_len) =
        unsafe { proof_layout.whir_pow_nonces_device_mut(slab.as_ptr() as *mut u8) };
    assert!(
        pow_round_idx < dst_len,
        "pow_round_idx {pow_round_idx} out of slab pow_nonces range (len {dst_len})",
    );
    // SAFETY: `dst_ptr + pow_round_idx` is a 16-byte-aligned offset inside the
    // live `slab` allocation; slots are disjoint by construction and the
    // single-u64 write does not race any other scheduled work.
    let dst = unsafe {
        era_cudart::slice::DeviceSlice::from_raw_parts_mut(dst_ptr.add(pow_round_idx), 1)
    };
    memory_copy_async(dst, &pow_round_state.d_nonce[..1], stream)?;
    Ok(())
}
