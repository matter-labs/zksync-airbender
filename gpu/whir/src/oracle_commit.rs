use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunk, DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl,
};
use gpu_core::primitives::field::BF;
use gpu_hash::blake2s::{gather_tree_caps_inline, Digest, STATE_SIZE};
use gpu_ntt::ntt::{lde_with_coset_range, MAX_LOG_N_FOR_SINGLE_KERNEL_LDE};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::{TraceHolder, TreesHolder, PARTIAL_TREE_REDUCTION_LAYERS};

const PARTIAL_TREE_STAGING_BYTES: usize = 32 << 20;
const PARTIAL_TREE_STAGING_DIGESTS: usize =
    PARTIAL_TREE_STAGING_BYTES / core::mem::size_of::<Digest>();

#[derive(Default)]
struct PartialTreeBatch {
    leaves_len: usize,
    first_tile_coset_base: usize,
    staged_tile_leaves: usize,
    tiles_count: usize,
    tile_coset_stride: usize,
}

fn flush_partial_tree_batch(
    batch: &mut PartialTreeBatch,
    staging: &DeviceSlice<Digest>,
    boundary_roots: &mut DeviceSlice<Digest>,
    log_packed_leaf_count: u32,
    log_lde_factor: u32,
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()> {
    if batch.leaves_len == 0 {
        return Ok(());
    }
    let staged = &staging[..batch.leaves_len];
    crate::kernels::reduce_staged_whir_subtrees_natural_tiles(
        staged,
        boundary_roots,
        log_packed_leaf_count,
        log_lde_factor,
        batch.first_tile_coset_base as u32,
        batch.staged_tile_leaves as u32,
        batch.tiles_count as u32,
        batch.tile_coset_stride as u32,
        stream,
    )?;
    *batch = PartialTreeBatch::default();
    Ok(())
}

/// Schedules the recursive WHIR oracle's natural multi-coset LDE, leaf
/// commitment, tree construction, and cap gather. The holder uses the WHIR
/// shape (`log_lde_factor = log_rows_per_leaf = 0`); the actual LDE and leaf
/// widths are explicit protocol inputs.
pub(crate) fn schedule_recursive_oracle_commit(
    trace_holder: &mut TraceHolder<BF>,
    inputs_matrix: &DeviceMatrixChunk<BF>,
    cap_dst_u32: &mut DeviceSlice<u32>,
    log_trace_len: u32,
    natural_log_lde_factor: u32,
    log_values_per_leaf: u32,
    src_cols_per_coset: usize,
    fused_coefficients: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(
        trace_holder.log_lde_factor, 0,
        "recursive WHIR commit requires TraceHolder log_lde_factor = 0",
    );
    assert_eq!(
        trace_holder.log_rows_per_leaf, 0,
        "recursive WHIR commit requires TraceHolder log_rows_per_leaf = 0",
    );
    let log_tree_cap_size = trace_holder.log_tree_cap_size;
    let cap_size = 1usize << log_tree_cap_size;
    assert_eq!(
        cap_dst_u32.len(),
        cap_size * STATE_SIZE,
        "recursive WHIR cap destination has the wrong length",
    );

    let lde_factor = 1usize << natural_log_lde_factor;
    let trace_len = 1usize << log_trace_len;
    let evals_total_len = lde_factor * trace_len * src_cols_per_coset;
    let total_leaf_count_log2 = (log_trace_len - log_values_per_leaf) + natural_log_lde_factor;
    let total_leaf_count = 1usize << total_leaf_count_log2;
    let cap_words = (cap_size * STATE_SIZE) as u32;
    let stream = context.get_exec_stream();

    if fused_coefficients {
        let TreesHolder::Partial(backing) = &mut trace_holder.trees else {
            unreachable!("fused WHIR commits require a partial tree")
        };
        let roots_count = total_leaf_count >> PARTIAL_TREE_REDUCTION_LAYERS;
        assert_eq!(backing.len(), roots_count << 1);
        let (roots, nodes) = backing.split_at_mut(roots_count);
        crate::fused_commit::commit(
            gpu_core::primitives::device_structures::DeviceMatrixChunkImpl::slice(inputs_matrix),
            roots,
            log_trace_len,
            natural_log_lde_factor,
            log_values_per_leaf,
            context.ntt_device_context().whir_leaf_transform_params(),
            stream,
        )?;
        let upper_layers =
            total_leaf_count_log2 - PARTIAL_TREE_REDUCTION_LAYERS - log_tree_cap_size;
        gpu_hash::blake2s::build_merkle_tree_nodes(roots, nodes, upper_layers, stream)?;
        let cap_offset_digests = backing.len() - (cap_size << 1);
        let cap_base =
            unsafe { (backing.as_ptr() as *const u32).add(cap_offset_digests * STATE_SIZE) };
        return gather_tree_caps_inline(
            cap_base,
            cap_words,
            (backing.len() * STATE_SIZE) as u32,
            0,
            cap_dst_u32,
            stream,
        );
    }

    let (ntt_output, trees) = trace_holder.get_uninit_cosets_and_tree_mut();
    assert_eq!(ntt_output.len(), evals_total_len);

    let TreesHolder::Partial(backing) = trees else {
        unreachable!("recursive WHIR commitments require a partial tree")
    };
    let boundary_roots_count = total_leaf_count >> PARTIAL_TREE_REDUCTION_LAYERS;
    assert_eq!(backing.len(), boundary_roots_count << 1);
    let (boundary_roots, upper_nodes) = backing.split_at_mut(boundary_roots_count);
    schedule_residue_leaves(
        inputs_matrix,
        ntt_output,
        boundary_roots,
        log_trace_len,
        natural_log_lde_factor,
        log_values_per_leaf,
        src_cols_per_coset,
        context,
    )?;
    let upper_layers = total_leaf_count_log2 - PARTIAL_TREE_REDUCTION_LAYERS - log_tree_cap_size;
    gpu_hash::blake2s::build_merkle_tree_nodes(boundary_roots, upper_nodes, upper_layers, stream)?;
    let cap_offset = backing.len() - (cap_size << 1);
    let cap_base = unsafe { (backing.as_ptr() as *const u32).add(cap_offset * STATE_SIZE) };
    gather_tree_caps_inline(
        cap_base,
        cap_words,
        (backing.len() * STATE_SIZE) as u32,
        0,
        cap_dst_u32,
        stream,
    )
}

/// Retain the residue-polynomial LDE and hash its coefficient leaves on exec.
fn schedule_residue_leaves(
    inputs_matrix: &DeviceMatrixChunk<BF>,
    ntt_output: &mut DeviceSlice<BF>,
    boundary_roots: &mut DeviceSlice<Digest>,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    src_cols_per_coset: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let trace_len = 1usize << log_trace_len;
    let log_ntt_len = log_trace_len - log_values_per_leaf;
    let packed_leaf_count = 1usize << log_ntt_len;
    let total_cosets = 1usize << log_lde_factor;
    let total_leaf_count = packed_leaf_count * total_cosets;
    assert!(log_ntt_len >= PARTIAL_TREE_REDUCTION_LAYERS);
    assert_eq!(
        boundary_roots.len(),
        total_leaf_count >> PARTIAL_TREE_REDUCTION_LAYERS
    );
    let ntt_cols_per_coset = src_cols_per_coset << log_values_per_leaf;
    assert_eq!(
        gpu_core::primitives::device_structures::DeviceMatrixChunkImpl::rows(inputs_matrix),
        packed_leaf_count
    );
    assert_eq!(
        gpu_core::primitives::device_structures::DeviceMatrixChunkImpl::cols(inputs_matrix),
        ntt_cols_per_coset
    );

    let stream = context.get_exec_stream();
    let properties = context.get_device_properties();
    let ntt_ctx = context.ntt_device_context();
    let tiled_lde = log_ntt_len as usize > MAX_LOG_N_FOR_SINGLE_KERNEL_LDE;
    let single_coset_bytes = src_cols_per_coset * trace_len * size_of::<BF>();
    // DIT computes the full LDE before hashing. Larger transforms hash each
    // tile immediately, budgeting half of L2 for its coset data.
    let cosets_in_tile_chunk = if tiled_lde {
        let fit = ((properties.l2_cache_size_bytes >> 1) / single_coset_bytes).max(1);
        let rounded = if fit.is_power_of_two() {
            fit
        } else {
            fit.next_power_of_two() >> 1
        };
        rounded.min(total_cosets)
    } else {
        total_cosets
    };
    assert_eq!(total_cosets % cosets_in_tile_chunk, 0);
    let mut d_scratch = if log_ntt_len <= 13 {
        Some(context.alloc::<BF>(packed_leaf_count, AllocationPlacement::BestFit)?)
    } else {
        None
    };
    let staging_capacity = PARTIAL_TREE_STAGING_DIGESTS.min(total_leaf_count);
    let mut staging = context.alloc::<Digest>(staging_capacity, AllocationPlacement::BestFit)?;
    let mut batch = PartialTreeBatch::default();
    let mut output = DeviceMatrixMut::new(ntt_output, trace_len);
    if !tiled_lde {
        lde_with_coset_range(
            inputs_matrix,
            output.slice_mut(),
            log_ntt_len as usize,
            log_lde_factor as usize,
            total_cosets,
            0,
            ntt_cols_per_coset,
            ntt_ctx,
            d_scratch.as_mut().map(|s| &mut s[..]),
            stream,
            properties,
        )?;
    }
    for coset_base in (0..total_cosets).step_by(cosets_in_tile_chunk) {
        let offset = src_cols_per_coset * trace_len * coset_base;
        if tiled_lde {
            lde_with_coset_range(
                inputs_matrix,
                &mut output.slice_mut()[offset..],
                log_ntt_len as usize,
                log_lde_factor as usize,
                cosets_in_tile_chunk,
                coset_base,
                ntt_cols_per_coset,
                ntt_ctx,
                d_scratch.as_mut().map(|s| &mut s[..]),
                stream,
                properties,
            )?;
        }
        let max_cosets_per_stage = staging_capacity / packed_leaf_count;
        assert!(max_cosets_per_stage >= 1);
        let mut cosets_staged = 0;
        while cosets_staged < cosets_in_tile_chunk {
            let sub_cosets = max_cosets_per_stage.min(cosets_in_tile_chunk - cosets_staged);
            let tile_leaves = sub_cosets * packed_leaf_count;
            let tile_coset_base = coset_base + cosets_staged;
            let shape_matches = batch.leaves_len == 0
                || (batch.staged_tile_leaves == tile_leaves
                    && batch.leaves_len + tile_leaves <= staging_capacity
                    && (batch.tiles_count == 1
                        || tile_coset_base
                            == batch.first_tile_coset_base
                                + batch.tiles_count * batch.tile_coset_stride));
            if !shape_matches {
                flush_partial_tree_batch(
                    &mut batch,
                    &staging,
                    boundary_roots,
                    log_ntt_len,
                    log_lde_factor,
                    stream,
                )?;
            }
            if batch.leaves_len == 0 {
                batch.first_tile_coset_base = tile_coset_base;
                batch.staged_tile_leaves = tile_leaves;
            } else if batch.tiles_count == 1 {
                batch.tile_coset_stride = tile_coset_base - batch.first_tile_coset_base;
            }
            let stage_offset = batch.leaves_len;
            let source_offset = offset + cosets_staged * src_cols_per_coset * trace_len;
            gpu_hash::blake2s::hash_leaves_from_ntt_multi_coset_to_staging(
                &output.slice()[source_offset..],
                &mut staging[stage_offset..stage_offset + tile_leaves],
                log_values_per_leaf,
                src_cols_per_coset as u32,
                log_lde_factor,
                tile_coset_base as u32,
                sub_cosets,
                packed_leaf_count,
                trace_len as u32,
                stream,
            )?;
            batch.leaves_len += tile_leaves;
            batch.tiles_count += 1;
            cosets_staged += sub_cosets;
            if batch.leaves_len == staging_capacity {
                flush_partial_tree_batch(
                    &mut batch,
                    &staging,
                    boundary_roots,
                    log_ntt_len,
                    log_lde_factor,
                    stream,
                )?;
            }
        }
    }
    flush_partial_tree_batch(
        &mut batch,
        &staging,
        boundary_roots,
        log_ntt_len,
        log_lde_factor,
        stream,
    )
}
