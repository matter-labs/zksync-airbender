use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;

use super::EXT4_DEGREE;
use crate::ops::blake2s::Digest;
use crate::primitives::context::{DeviceAllocation, HostAllocation};
use crate::primitives::field::{BF, E4};
use crate::prover::pow::PowAndQueryIndexesKeepalives;
use crate::prover::proof::layout::ProofLayout;

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
/// sub-ranges at `query_idx`. `leafs_accessor` points at
/// `values_per_leaf * EXT4_DEGREE` `BF` values whose byte layout matches
/// the `values_per_leaf` `E4` slab slots (`E4 = #[repr(C, align(16))]
/// { c0: BF, c1: BF, c0: BF, c1: BF }` via `Ext2`, equivalent to
/// `[BF; 4]`). `merkle_paths_accessor` points at `path_len` `Digest`s,
/// reinterpreted as flat `[u32]` for the slab. `None` slab is a no-op
/// (test paths).
pub(super) fn copy_intermediate_query_to_slab(
    all_indexes_accessor: crate::primitives::context::UnsafeAccessor<[u32]>,
    leafs_accessor: crate::primitives::context::UnsafeAccessor<[BF]>,
    paths_accessor: crate::primitives::context::UnsafeAccessor<[Digest]>,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    round: usize,
    query_idx: usize,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()> {
    let Some(slab) = proof_slab else {
        return Ok(());
    };
    let digest_u32_words = crate::prover::proof::layout::DIGEST_U32_WORDS;

    // Index (single u32 at `query_idx` in `all_indexes_accessor`).
    let (idx_ptr, idx_total_len) = unsafe {
        proof_layout.whir_intermediate_query_indices_device_mut(slab.as_ptr() as *mut u8, round)
    };
    if idx_total_len == 0 {
        return Ok(());
    }
    assert!(query_idx < idx_total_len);
    let idx_src = unsafe { all_indexes_accessor.get() };
    // SAFETY: single-slot write inside the slab index array.
    let idx_dst =
        unsafe { era_cudart::slice::DeviceSlice::from_raw_parts_mut(idx_ptr.add(query_idx), 1) };
    memory_copy_async(idx_dst, &idx_src[query_idx..query_idx + 1], stream)?;

    // Leaves: `values_per_leaf * EXT4_DEGREE` `BF` → `values_per_leaf` `E4`
    // slots (byte-equivalent). Write as `BF` into the slab, treating the
    // E4 slot as a `[BF; 4]` array.
    let (leaves_ptr_e4, leaves_total_e4) = unsafe {
        proof_layout.whir_intermediate_query_leaves_device_mut(slab.as_ptr() as *mut u8, round)
    };
    let leaf_values_len_e4 = leaves_total_e4 / idx_total_len;
    let leaves_src_bf = unsafe { leafs_accessor.get() };
    assert_eq!(leaves_src_bf.len(), leaf_values_len_e4 * EXT4_DEGREE);
    // SAFETY: slab `E4` slot at `query_idx` offset has `leaf_values_len_e4 * 4`
    // BFs worth of storage.
    let leaves_dst = unsafe {
        era_cudart::slice::DeviceSlice::from_raw_parts_mut(
            leaves_ptr_e4.add(query_idx * leaf_values_len_e4) as *mut BF,
            leaves_src_bf.len(),
        )
    };
    memory_copy_async(leaves_dst, leaves_src_bf, stream)?;

    // Paths: flat Digest → `[u32]` reinterpret, `path_len` digests per query.
    let (paths_ptr, paths_total_u32) = unsafe {
        proof_layout.whir_intermediate_query_paths_device_mut(slab.as_ptr() as *mut u8, round)
    };
    let paths_len_digests_per_query = paths_total_u32 / (idx_total_len * digest_u32_words);
    let paths_src_digests = unsafe { paths_accessor.get() };
    assert_eq!(paths_src_digests.len(), paths_len_digests_per_query);
    let paths_src_u32 = unsafe {
        std::slice::from_raw_parts(
            paths_src_digests.as_ptr() as *const u32,
            paths_src_digests.len() * digest_u32_words,
        )
    };
    let paths_dst = unsafe {
        era_cudart::slice::DeviceSlice::from_raw_parts_mut(
            paths_ptr.add(query_idx * paths_len_digests_per_query * digest_u32_words),
            paths_src_u32.len(),
        )
    };
    memory_copy_async(paths_dst, paths_src_u32, stream)?;

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
    pow_keepalives: &PowAndQueryIndexesKeepalives,
    proof_slab: Option<&DeviceAllocation<E4>>,
    proof_layout: &ProofLayout,
    pow_round_idx: usize,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()> {
    let Some(slab) = proof_slab else {
        return Ok(());
    };
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
    memory_copy_async(dst, &pow_keepalives.d_nonce[..1], stream)?;
    Ok(())
}
