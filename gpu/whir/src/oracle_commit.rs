use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStreamWaitEventFlags;

use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunk, DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl,
};
use gpu_core::primitives::field::BF;
use gpu_hash::blake2s::{gather_tree_caps_inline, Digest, STATE_SIZE};
use gpu_ntt::ntt::{lde_with_coset_range, MAX_LOG_N_FOR_SINGLE_KERNEL_LDE};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::{TraceHolder, TreesHolder, PARTIAL_TREE_REDUCTION_LAYERS};

enum LeafCommitTarget<'a> {
    FullTree(&'a mut DeviceSlice<Digest>),
    PartialTree(&'a mut DeviceSlice<Digest>),
}

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
    flat_root_base: usize,
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
    if batch.staged_tile_leaves == 0 {
        let roots_count = batch.leaves_len >> PARTIAL_TREE_REDUCTION_LAYERS;
        let roots = &mut boundary_roots[batch.flat_root_base..batch.flat_root_base + roots_count];
        crate::kernels::reduce_staged_whir_subtrees_flat(staged, roots, stream)?;
    } else {
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
    }
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
    transform_leaves_to_multilinear_coeffs: bool,
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
    let full_tree_len = total_leaf_count << 1;
    let cap_words = (cap_size * STATE_SIZE) as u32;
    let stream = context.get_exec_stream();

    let (ntt_output, trees) = trace_holder.get_uninit_cosets_and_tree_mut();
    assert_eq!(ntt_output.len(), evals_total_len);

    match trees {
        TreesHolder::Full(backing) => {
            commit_trace_from_ntt_single_tree(
                inputs_matrix,
                ntt_output,
                backing,
                log_trace_len,
                natural_log_lde_factor,
                log_values_per_leaf,
                log_tree_cap_size,
                src_cols_per_coset,
                transform_leaves_to_multilinear_coeffs,
                context,
            )?;
        }
        TreesHolder::Partial(backing) => {
            let boundary_roots_count = total_leaf_count >> PARTIAL_TREE_REDUCTION_LAYERS;
            assert_eq!(backing.len(), boundary_roots_count << 1);
            let (boundary_roots, upper_nodes) = backing.split_at_mut(boundary_roots_count);
            commit_trace_from_ntt_partial_tree(
                inputs_matrix,
                ntt_output,
                boundary_roots,
                log_trace_len,
                natural_log_lde_factor,
                log_values_per_leaf,
                src_cols_per_coset,
                transform_leaves_to_multilinear_coeffs,
                context,
            )?;
            let bottom_layers_count =
                total_leaf_count_log2 + 1 - PARTIAL_TREE_REDUCTION_LAYERS - log_tree_cap_size;
            assert!(bottom_layers_count >= 1);
            gpu_hash::blake2s::build_merkle_tree_nodes(
                boundary_roots,
                upper_nodes,
                bottom_layers_count - 1,
                stream,
            )?;
        }
        TreesHolder::None => {
            panic!("recursive WHIR commit does not support TreesCacheMode::CacheNone",)
        }
    }

    match &*trees {
        TreesHolder::Full(backing) => {
            let cap_offset_digests = full_tree_len - (1usize << (log_tree_cap_size + 1));
            let cap_offset_words = cap_offset_digests * STATE_SIZE;
            let stride_words = (full_tree_len * STATE_SIZE) as u32;
            let base_words = backing.as_ptr() as *const u32;
            let cap_base = unsafe { base_words.add(cap_offset_words) };
            gather_tree_caps_inline(cap_base, cap_words, stride_words, 0, cap_dst_u32, stream)?;
        }
        TreesHolder::Partial(backing) => {
            let tree_bottom_len = full_tree_len >> PARTIAL_TREE_REDUCTION_LAYERS;
            let cap_offset_digests = tree_bottom_len - (1usize << (log_tree_cap_size + 1));
            let cap_offset_words = cap_offset_digests * STATE_SIZE;
            let stride_words = (tree_bottom_len * STATE_SIZE) as u32;
            let base_words = backing.as_ptr() as *const u32;
            let cap_base = unsafe { base_words.add(cap_offset_words) };
            gather_tree_caps_inline(cap_base, cap_words, stride_words, 0, cap_dst_u32, stream)?;
        }
        TreesHolder::None => unreachable!(),
    }

    Ok(())
}

/// Builds a single flat Merkle tree across every natural LDE coset.
/// Coefficient leaves are transformed into shared memory and hashed without
/// overwriting the natural evaluation backing.
fn commit_trace_from_ntt_single_tree(
    inputs_matrix: &DeviceMatrixChunk<BF>,
    ntt_output: &mut DeviceSlice<BF>,
    trees_backing: &mut DeviceSlice<Digest>,
    log_trace_len: u32,
    natural_log_lde_factor: u32,
    log_values_per_leaf: u32,
    log_tree_cap_size: u32,
    src_cols_per_coset: usize,
    transform_leaves_to_multilinear_coeffs: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    let packed_leaf_count = 1usize << (log_trace_len - log_values_per_leaf);
    let total_leaf_count = packed_leaf_count
        .checked_mul(1 << natural_log_lde_factor)
        .expect("total_leaf_count overflow");
    assert_eq!(trees_backing.len(), total_leaf_count << 1);
    let total_leaf_count_log2 = (log_trace_len - log_values_per_leaf) + natural_log_lde_factor;
    assert!(log_tree_cap_size <= total_leaf_count_log2);
    let layers_count = total_leaf_count_log2 + 1 - log_tree_cap_size;
    let (leaves, nodes) = trees_backing.split_at_mut(total_leaf_count);

    schedule_trace_leaves_from_ntt(
        inputs_matrix,
        ntt_output,
        LeafCommitTarget::FullTree(leaves),
        log_trace_len,
        natural_log_lde_factor,
        log_values_per_leaf,
        src_cols_per_coset,
        transform_leaves_to_multilinear_coeffs,
        context,
    )?;
    gpu_hash::blake2s::build_merkle_tree_nodes(
        leaves,
        nodes,
        layers_count - 1,
        context.get_exec_stream(),
    )
}

fn commit_trace_from_ntt_partial_tree(
    inputs_matrix: &DeviceMatrixChunk<BF>,
    ntt_output: &mut DeviceSlice<BF>,
    boundary_roots: &mut DeviceSlice<Digest>,
    log_trace_len: u32,
    natural_log_lde_factor: u32,
    log_values_per_leaf: u32,
    src_cols_per_coset: usize,
    transform_leaves_to_multilinear_coeffs: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    assert_eq!(
        PARTIAL_TREE_REDUCTION_LAYERS,
        gpu_core::primitives::utils::WARP_SIZE.trailing_zeros(),
    );
    let total_leaf_count =
        1usize << ((log_trace_len - log_values_per_leaf) + natural_log_lde_factor);
    assert_eq!(
        boundary_roots.len(),
        total_leaf_count >> PARTIAL_TREE_REDUCTION_LAYERS
    );
    schedule_trace_leaves_from_ntt(
        inputs_matrix,
        ntt_output,
        LeafCommitTarget::PartialTree(boundary_roots),
        log_trace_len,
        natural_log_lde_factor,
        log_values_per_leaf,
        src_cols_per_coset,
        transform_leaves_to_multilinear_coeffs,
        context,
    )
}

fn schedule_trace_leaves_from_ntt(
    inputs_matrix: &DeviceMatrixChunk<BF>,
    ntt_output: &mut DeviceSlice<BF>,
    mut target: LeafCommitTarget<'_>,
    log_trace_len: u32,
    natural_log_lde_factor: u32,
    log_values_per_leaf: u32,
    src_cols_per_coset: usize,
    transform_leaves_to_multilinear_coeffs: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(natural_log_lde_factor >= 1);
    assert!(log_trace_len >= log_values_per_leaf);
    let trace_len = 1 << log_trace_len;
    let packed_leaf_count = 1usize << (log_trace_len - log_values_per_leaf);
    let total_leaf_count = packed_leaf_count
        .checked_mul(1 << natural_log_lde_factor)
        .expect("total_leaf_count overflow");
    match &target {
        LeafCommitTarget::FullTree(leaves) => assert_eq!(leaves.len(), total_leaf_count),
        LeafCommitTarget::PartialTree(roots) => assert_eq!(
            roots.len(),
            total_leaf_count >> PARTIAL_TREE_REDUCTION_LAYERS
        ),
    }

    let device_properties = context.get_device_properties();
    let ntt_ctx = context.ntt_device_context();
    // Recursive WHIR folds to a small trace (trace_len_log2 <= 13), the DIT
    // forward-NTT range, which needs a pooled d-table scratch (len >= N).
    let mut d_scratch = if log_trace_len <= 13 {
        Some(context.alloc::<BF>(trace_len, AllocationPlacement::BestFit)?)
    } else {
        None
    };

    let include_lde_in_l2_persistence_chain =
        log_trace_len as usize > MAX_LOG_N_FOR_SINGLE_KERNEL_LDE;
    let total_cosets = 1 << natural_log_lde_factor;
    // The L2 fractions and power-of-two tile rounding are empirically tuned.
    let l2_bytes_with_safety_margin = if include_lde_in_l2_persistence_chain {
        device_properties.l2_cache_size_bytes >> 1
    } else {
        device_properties.l2_cache_size_bytes >> 2
    };
    let single_bf_col_bytes = std::mem::size_of::<BF>() << log_trace_len;
    let single_coset_bytes = src_cols_per_coset * single_bf_col_bytes;

    let half_l2_bytes_with_safety_margin = l2_bytes_with_safety_margin >> 1;
    let (mut cosets_in_tile_chunk, mut num_streams) =
        if single_coset_bytes > half_l2_bytes_with_safety_margin {
            (1, 1)
        } else {
            let nearest = half_l2_bytes_with_safety_margin / single_coset_bytes;
            if nearest.is_power_of_two() {
                (nearest, 2)
            } else {
                (nearest.next_power_of_two() >> 1, 2)
            }
        };

    if total_cosets > cosets_in_tile_chunk {
        assert_eq!(total_cosets % cosets_in_tile_chunk, 0);
    }

    let is_last_production_whir_stage = (log_trace_len - log_values_per_leaf) == 1;
    if (!include_lde_in_l2_persistence_chain && !transform_leaves_to_multilinear_coeffs)
        || is_last_production_whir_stage
    {
        num_streams = 1;
        cosets_in_tile_chunk = total_cosets;
    }

    let helpers_for_base = |coset_index_base: usize| {
        let mut helpers = Vec::with_capacity(2);
        for i in 0..num_streams {
            let stream_coset_base = coset_index_base + i * cosets_in_tile_chunk;
            if stream_coset_base < total_cosets {
                let cosets_in_tile =
                    std::cmp::min(cosets_in_tile_chunk, total_cosets - stream_coset_base);
                let offset = src_cols_per_coset * trace_len * stream_coset_base;
                helpers.push((stream_coset_base, cosets_in_tile, offset));
            }
        }
        helpers
    };
    let is_partial = matches!(&target, LeafCommitTarget::PartialTree(_));
    let use_flat_partial =
        is_partial && packed_leaf_count < (1usize << PARTIAL_TREE_REDUCTION_LAYERS);
    let staging_capacity = std::cmp::min(PARTIAL_TREE_STAGING_DIGESTS, total_leaf_count);
    let mut flat_leaves_per_stream = [0usize; 2];
    if use_flat_partial {
        for coset_index_base in (0..total_cosets).step_by(num_streams * cosets_in_tile_chunk) {
            for (i, &(_, cosets_in_tile, _)) in
                helpers_for_base(coset_index_base).iter().enumerate()
            {
                flat_leaves_per_stream[i] += cosets_in_tile * packed_leaf_count;
            }
        }
        assert_eq!(
            flat_leaves_per_stream[..num_streams].iter().sum::<usize>(),
            total_leaf_count
        );
        for &leaves_count in &flat_leaves_per_stream[..num_streams] {
            assert_eq!(leaves_count % (1usize << PARTIAL_TREE_REDUCTION_LAYERS), 0);
        }
    }
    let mut flat_leaf_cursors = [0usize, flat_leaves_per_stream[0]];
    let mut staging_buffers = Vec::with_capacity(num_streams);
    if is_partial {
        for _ in 0..num_streams {
            staging_buffers
                .push(context.alloc::<Digest>(staging_capacity, AllocationPlacement::BestFit)?);
        }
    }
    let mut partial_tree_batches = (0..num_streams)
        .map(|_| PartialTreeBatch::default())
        .collect::<Vec<_>>();

    let mut ntt_output_matrix = DeviceMatrixMut::new(ntt_output, trace_len);
    let (start_event, end_event) = if num_streams > 1 {
        (
            Some(CudaEvent::create_with_flags(
                CudaEventCreateFlags::DISABLE_TIMING,
            )?),
            Some(CudaEvent::create_with_flags(
                CudaEventCreateFlags::DISABLE_TIMING,
            )?),
        )
    } else {
        (None, None)
    };

    let mut occupancy_hint_numerator = 1;
    let mut occupancy_hint_denominator = 1;
    let exec_stream = context.get_exec_stream();
    let side_stream = context.get_side_stream();
    let streams = [exec_stream, side_stream];

    if !include_lde_in_l2_persistence_chain {
        let scratch_opt = d_scratch.as_mut().map(|scratch| &mut scratch[..]);
        lde_with_coset_range(
            inputs_matrix,
            ntt_output_matrix.slice_mut(),
            log_trace_len as usize,
            natural_log_lde_factor as usize,
            total_cosets,
            0,
            src_cols_per_coset,
            occupancy_hint_numerator,
            occupancy_hint_denominator,
            ntt_ctx,
            scratch_opt,
            streams[0],
            device_properties,
        )?;
    }

    if num_streams > 1 {
        occupancy_hint_numerator = 5;
        occupancy_hint_denominator = 8;
        start_event.as_ref().unwrap().record(streams[0])?;
        streams[1].wait_event(
            start_event.as_ref().unwrap(),
            CudaStreamWaitEventFlags::DEFAULT,
        )?;
    }

    for coset_index_base in (0..total_cosets).step_by(num_streams * cosets_in_tile_chunk) {
        let helpers_per_stream = helpers_for_base(coset_index_base);

        // Preserve the breadth-first two-stream launch order.
        for (i, &(coset_index_base_this_stream, cosets_in_tile, offset)) in
            helpers_per_stream.iter().enumerate()
        {
            if include_lde_in_l2_persistence_chain {
                let scratch_opt = d_scratch.as_mut().map(|scratch| &mut scratch[..]);
                lde_with_coset_range(
                    inputs_matrix,
                    &mut ntt_output_matrix.slice_mut()[offset..],
                    log_trace_len as usize,
                    natural_log_lde_factor as usize,
                    cosets_in_tile,
                    coset_index_base_this_stream,
                    src_cols_per_coset,
                    occupancy_hint_numerator,
                    occupancy_hint_denominator,
                    ntt_ctx,
                    scratch_opt,
                    streams[i],
                    device_properties,
                )?;
            }
        }
        for (i, &(stream_coset_base, cosets_in_tile, offset)) in
            helpers_per_stream.iter().enumerate()
        {
            match &mut target {
                LeafCommitTarget::FullTree(leaves) => {
                    if transform_leaves_to_multilinear_coeffs {
                        assert_eq!(src_cols_per_coset, 4, "coefficient WHIR leaves require E4");
                        let transform_params =
                            ntt_ctx.whir_leaf_transform_params(log_values_per_leaf);
                        crate::kernels::transform_and_hash_whir_leaves_from_ntt_multi_coset(
                            &ntt_output_matrix.slice()[offset..],
                            leaves,
                            log_trace_len,
                            natural_log_lde_factor,
                            log_values_per_leaf,
                            stream_coset_base as u32,
                            cosets_in_tile as u32,
                            transform_params,
                            streams[i],
                        )?;
                    } else {
                        gpu_hash::blake2s::hash_leaves_from_ntt_multi_coset(
                            &ntt_output_matrix.slice()[offset..],
                            leaves,
                            log_values_per_leaf,
                            src_cols_per_coset as u32,
                            natural_log_lde_factor,
                            stream_coset_base as u32,
                            cosets_in_tile,
                            packed_leaf_count,
                            trace_len as u32,
                            streams[i],
                        )?;
                    }
                }
                LeafCommitTarget::PartialTree(boundary_roots) => {
                    let staging = &mut staging_buffers[i];
                    let batch = &mut partial_tree_batches[i];
                    if use_flat_partial {
                        let subtree_leaves = 1usize << PARTIAL_TREE_REDUCTION_LAYERS;
                        let mut leaves_remaining = cosets_in_tile * packed_leaf_count;
                        while leaves_remaining > 0 {
                            if batch.leaves_len == staging_capacity {
                                flush_partial_tree_batch(
                                    batch,
                                    staging,
                                    boundary_roots,
                                    log_trace_len - log_values_per_leaf,
                                    natural_log_lde_factor,
                                    streams[i],
                                )?;
                            }
                            let flat_leaf_base = flat_leaf_cursors[i];
                            let leaves_count = std::cmp::min(
                                leaves_remaining,
                                staging_capacity - batch.leaves_len,
                            );
                            assert_eq!(flat_leaf_base % subtree_leaves, 0);
                            assert_eq!(leaves_count % subtree_leaves, 0);
                            if batch.leaves_len == 0 {
                                batch.flat_root_base =
                                    flat_leaf_base >> PARTIAL_TREE_REDUCTION_LAYERS;
                            } else {
                                assert_eq!(
                                    batch.flat_root_base
                                        + (batch.leaves_len >> PARTIAL_TREE_REDUCTION_LAYERS),
                                    flat_leaf_base >> PARTIAL_TREE_REDUCTION_LAYERS
                                );
                            }
                            let stage_offset = batch.leaves_len;
                            let stage_dst = &mut staging[stage_offset..stage_offset + leaves_count];
                            if transform_leaves_to_multilinear_coeffs {
                                assert_eq!(
                                    src_cols_per_coset, 4,
                                    "coefficient WHIR leaves require E4"
                                );
                                let transform_params =
                                    ntt_ctx.whir_leaf_transform_params(log_values_per_leaf);
                                crate::kernels::transform_and_hash_whir_leaves_from_ntt_flat_range_to_staging(
                                    ntt_output_matrix.slice(),
                                    stage_dst,
                                    log_trace_len,
                                    natural_log_lde_factor,
                                    log_values_per_leaf,
                                    flat_leaf_base,
                                    leaves_count,
                                    transform_params,
                                    streams[i],
                                )?;
                            } else {
                                gpu_hash::blake2s::hash_leaves_from_ntt_flat_range_to_staging(
                                    ntt_output_matrix.slice(),
                                    stage_dst,
                                    log_values_per_leaf,
                                    src_cols_per_coset as u32,
                                    natural_log_lde_factor,
                                    flat_leaf_base,
                                    leaves_count,
                                    packed_leaf_count,
                                    trace_len as u32,
                                    streams[i],
                                )?;
                            }
                            batch.leaves_len += leaves_count;
                            flat_leaf_cursors[i] += leaves_count;
                            leaves_remaining -= leaves_count;
                        }
                    } else {
                        let max_cosets_per_stage = staging_capacity / packed_leaf_count;
                        assert!(max_cosets_per_stage >= 1);
                        let mut cosets_staged = 0;
                        while cosets_staged < cosets_in_tile {
                            let sub_cosets =
                                std::cmp::min(max_cosets_per_stage, cosets_in_tile - cosets_staged);
                            let tile_leaves = sub_cosets * packed_leaf_count;
                            let tile_coset_base = stream_coset_base + cosets_staged;
                            let shape_matches = batch.leaves_len == 0
                                || (batch.staged_tile_leaves == tile_leaves
                                    && batch.leaves_len + tile_leaves <= staging_capacity
                                    && (batch.tiles_count == 1
                                        || tile_coset_base
                                            == batch.first_tile_coset_base
                                                + batch.tiles_count * batch.tile_coset_stride));
                            if !shape_matches {
                                flush_partial_tree_batch(
                                    batch,
                                    staging,
                                    boundary_roots,
                                    log_trace_len - log_values_per_leaf,
                                    natural_log_lde_factor,
                                    streams[i],
                                )?;
                            }
                            if batch.leaves_len == 0 {
                                batch.first_tile_coset_base = tile_coset_base;
                                batch.staged_tile_leaves = tile_leaves;
                            } else if batch.tiles_count == 1 {
                                batch.tile_coset_stride =
                                    tile_coset_base - batch.first_tile_coset_base;
                            }
                            let stage_offset = batch.leaves_len;
                            let stage_dst = &mut staging[stage_offset..stage_offset + tile_leaves];
                            let source_offset =
                                offset + cosets_staged * src_cols_per_coset * trace_len;
                            if transform_leaves_to_multilinear_coeffs {
                                assert_eq!(
                                    src_cols_per_coset, 4,
                                    "coefficient WHIR leaves require E4"
                                );
                                let transform_params =
                                    ntt_ctx.whir_leaf_transform_params(log_values_per_leaf);
                                crate::kernels::transform_and_hash_whir_leaves_from_ntt_multi_coset_to_staging(
                                    &ntt_output_matrix.slice()[source_offset..],
                                    stage_dst,
                                    log_trace_len,
                                    natural_log_lde_factor,
                                    log_values_per_leaf,
                                    tile_coset_base as u32,
                                    sub_cosets as u32,
                                    transform_params,
                                    streams[i],
                                )?;
                            } else {
                                gpu_hash::blake2s::hash_leaves_from_ntt_multi_coset_to_staging(
                                    &ntt_output_matrix.slice()[source_offset..],
                                    stage_dst,
                                    log_values_per_leaf,
                                    src_cols_per_coset as u32,
                                    natural_log_lde_factor,
                                    tile_coset_base as u32,
                                    sub_cosets,
                                    packed_leaf_count,
                                    trace_len as u32,
                                    streams[i],
                                )?;
                            }
                            batch.leaves_len += tile_leaves;
                            batch.tiles_count += 1;
                            cosets_staged += sub_cosets;
                            if batch.leaves_len == staging_capacity {
                                flush_partial_tree_batch(
                                    batch,
                                    staging,
                                    boundary_roots,
                                    log_trace_len - log_values_per_leaf,
                                    natural_log_lde_factor,
                                    streams[i],
                                )?;
                            }
                        }
                    }
                }
            }
        }
    }

    if is_partial {
        let LeafCommitTarget::PartialTree(boundary_roots) = &mut target else {
            unreachable!()
        };
        for i in 0..num_streams {
            flush_partial_tree_batch(
                &mut partial_tree_batches[i],
                &staging_buffers[i],
                boundary_roots,
                log_trace_len - log_values_per_leaf,
                natural_log_lde_factor,
                streams[i],
            )?;
        }
    }

    if use_flat_partial {
        assert_eq!(flat_leaf_cursors[0], flat_leaves_per_stream[0]);
        assert_eq!(flat_leaf_cursors[num_streams - 1], total_leaf_count);
    }

    if num_streams > 1 {
        end_event.as_ref().unwrap().record(side_stream)?;
        exec_stream.wait_event(
            end_event.as_ref().unwrap(),
            CudaStreamWaitEventFlags::DEFAULT,
        )?;
    }

    Ok(())
}
