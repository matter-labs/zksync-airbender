use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart::{
    cuda_kernel, cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function,
};

use crate::ops::simple::pow;
use crate::primitives::context::ProverContext;
use crate::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{
    get_grid_block_dims_for_threads_count, get_grid_block_dims_for_warp_groups, GetChunksCount,
    WARP_SIZE,
};
use crate::prover::gkr::backward::{
    eq_group_count, gkr_dim_reducing_launch_config, make_eq_sizes, GkrEqSizes,
    GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS,
};
use crate::upstream::FieldExtension;

cuda_kernel_signature_arguments_and_function!(
    SerializeWhirE4Columns,
    src: *const E4,
    dst: *mut BF,
    count: u32,
);

cuda_kernel_declaration!(
    ab_serialize_whir_e4_columns_kernel(
        src: *const E4,
        dst: *mut BF,
        count: u32,
    )
);

pub(crate) fn serialize_whir_e4_columns(
    src: &DeviceSlice<E4>,
    dst: &mut DeviceSlice<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(dst.len(), src.len() * <E4 as FieldExtension<BF>>::DEGREE);
    assert!(src.len() <= u32::MAX as usize);
    let count = src.len() as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_warp_groups(4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = SerializeWhirE4ColumnsArguments::new(src.as_ptr(), dst.as_mut_ptr(), count);
    SerializeWhirE4ColumnsFunction(ab_serialize_whir_e4_columns_kernel).launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    DeserializeWhirE4Columns,
    src: *const BF,
    dst: *mut E4,
    count: u32,
);

cuda_kernel_declaration!(
    ab_deserialize_whir_e4_columns_kernel(
        src: *const BF,
        dst: *mut E4,
        count: u32,
    )
);

pub(crate) fn deserialize_whir_e4_columns(
    src: &DeviceSlice<BF>,
    dst: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(src.len(), dst.len() * <E4 as FieldExtension<BF>>::DEGREE);
    assert!(dst.len() <= u32::MAX as usize);
    let count = dst.len() as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_warp_groups(4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = DeserializeWhirE4ColumnsArguments::new(src.as_ptr(), dst.as_mut_ptr(), count);
    DeserializeWhirE4ColumnsFunction(ab_deserialize_whir_e4_columns_kernel).launch(&config, &args)
}

const TRACE_CHUNKS: usize = 3;

#[repr(C)]
struct BaseColumnsBatchingMetadata {
    values: [*const BF; TRACE_CHUNKS],
    weights: [*const E4; TRACE_CHUNKS],
    cols: [u32; TRACE_CHUNKS],
    strides: [u32; TRACE_CHUNKS],
    result: *mut E4,
    rows: u32,
}

cuda_kernel_signature_arguments_and_function!(
    AccumulateWhirBaseColumns,
    metadata: BaseColumnsBatchingMetadata,
);

cuda_kernel_declaration!(
    ab_accumulate_whir_base_columns_e4_kernel(metadata: BaseColumnsBatchingMetadata)
);

pub(crate) fn accumulate_whir_base_columns(
    memory_values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    witness_values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    setup_values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    memory_weights: &DeviceSlice<E4>,
    witness_weights: &DeviceSlice<E4>,
    setup_weights: &DeviceSlice<E4>,
    result: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(memory_values.cols(), memory_weights.len());
    assert_eq!(memory_values.rows(), result.len());
    assert!(memory_values.rows() <= u32::MAX as usize);
    assert!(memory_values.cols() <= u32::MAX as usize);
    assert_eq!(witness_values.cols(), witness_weights.len());
    assert_eq!(witness_values.rows(), result.len());
    assert!(witness_values.rows() <= u32::MAX as usize);
    assert!(witness_values.cols() <= u32::MAX as usize);
    assert_eq!(setup_values.cols(), setup_weights.len());
    assert_eq!(setup_values.rows(), result.len());
    assert!(setup_values.rows() <= u32::MAX as usize);
    assert!(setup_values.cols() <= u32::MAX as usize);
    let values = [
        memory_values.as_ptr(),
        witness_values.as_ptr(),
        setup_values.as_ptr(),
    ];
    let weights = [
        memory_weights.as_ptr(),
        witness_weights.as_ptr(),
        setup_weights.as_ptr(),
    ];
    let cols = [
        memory_values.cols() as u32,
        witness_values.cols() as u32,
        setup_values.cols() as u32,
    ];
    let strides = [
        memory_values.stride() as u32,
        witness_values.stride() as u32,
        setup_values.stride() as u32,
    ];
    let result = result.as_mut_ptr();
    let rows = memory_values.rows() as u32;
    let metadata = BaseColumnsBatchingMetadata {
        values,
        weights,
        cols,
        strides,
        result,
        rows,
    };
    let (grid_dim, block_dim) = get_grid_block_dims_for_warp_groups(4, rows);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = AccumulateWhirBaseColumnsArguments::new(metadata);
    AccumulateWhirBaseColumnsFunction(ab_accumulate_whir_base_columns_e4_kernel)
        .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    WhirFoldSplitHalfVectorized,
    src: PtrAndStride<BF>,
    dst: MutPtrAndStride<BF>,
    challenge: *const E4,
    half_len: i32,
);

cuda_kernel_declaration!(
    ab_whir_fold_split_half_vectorized_e4_kernel(
        src: PtrAndStride<BF>,
        dst: MutPtrAndStride<BF>,
        challenge: *const E4,
        half_len: i32,
    )
);

pub(crate) fn whir_fold_split_half_in_place_vectorized(
    values: &mut impl DeviceMatrixChunkMutImpl<BF>,
    challenge: &DeviceVariable<E4>,
    half_len: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(values.rows().is_power_of_two());
    assert_eq!(values.cols(), 4);
    let (grid_dim, block_dim) = get_grid_block_dims_for_warp_groups(4, half_len as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirFoldSplitHalfVectorizedArguments::new(
        values.as_ptr_and_stride(),
        values.as_mut_ptr_and_stride(),
        challenge.as_ptr(),
        half_len as i32,
    );
    WhirFoldSplitHalfVectorizedFunction(ab_whir_fold_split_half_vectorized_e4_kernel)
        .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    WhirFoldSplitHalf,
    values: *mut E4,
    challenge: *const E4,
    half_len: u32,
);

cuda_kernel_declaration!(
    ab_whir_fold_split_half_e4_kernel(
        values: *mut E4,
        challenge: *const E4,
        half_len: u32,
    )
);

pub(crate) fn whir_fold_split_half_in_place(
    values: &mut DeviceSlice<E4>,
    challenge: &DeviceVariable<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(values.len().is_power_of_two());
    assert!(values.len() >= 2);
    assert!(values.len() / 2 <= u32::MAX as usize);
    let half_len = (values.len() / 2) as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_warp_groups(4, half_len);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirFoldSplitHalfArguments::new(values.as_mut_ptr(), challenge.as_ptr(), half_len);
    WhirFoldSplitHalfFunction(ab_whir_fold_split_half_e4_kernel).launch(&config, &args)
}

#[cfg(test)]
cuda_kernel_signature_arguments_and_function!(
    PackRowsForWhirLeavesMultiCoset,
    src: PtrAndStride<BF>,
    dst: MutPtrAndStride<BF>,
    log_values_per_leaf: u32,
    dst_rows_per_slot: u32,
    log_blocks_per_row_tile: u32,
    log_lde_factor: u32,
    coset_index_base: u32,
    src_cols_per_coset: u32,
);

#[cfg(test)]
cuda_kernel_declaration!(
    ab_pack_rows_for_whir_leaves_multi_coset_bf_kernel(
        src: PtrAndStride<BF>,
        dst: MutPtrAndStride<BF>,
        log_values_per_leaf: u32,
        dst_rows_per_slot: u32,
        log_blocks_per_row_tile: u32,
        log_lde_factor: u32,
        coset_index_base: u32,
        src_cols_per_coset: u32,
    )
);

/// Multi-coset pack: one launch handles `num_cosets_in_tile` independent
/// cosets of an `EXT4_DEGREE`-column NTT output, writing into the bitreversed
/// coset placement inside the WHIR-leaves packed trace.
///
/// Inputs:
/// * `src` — multi-coset NTT output: rows = `dst_rows_per_slot <<
///   log_values_per_leaf`, cols = `num_cosets_in_tile * src_cols_per_coset`
///   with coset-major outer layout (coset `k`'s columns occupy `[k *
///   src_cols_per_coset, (k + 1) * src_cols_per_coset)`).
/// * `dst` — full packed trace slab: total rows `dst_rows_per_slot <<
///   log_lde_factor`, cols `src_cols_per_coset << log_values_per_leaf`. The
///   kernel writes coset `coset_index_base + k` at row offset
///   `bitreverse(coset_index_base + k, log_lde_factor) * dst_rows_per_slot`.
#[cfg(test)]
pub(crate) fn pack_rows_for_whir_leaves_multi_coset(
    src: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    dst: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_values_per_leaf: u32,
    dst_rows_per_slot: usize,
    log_lde_factor: u32,
    coset_index_base: u32,
    num_cosets_in_tile: usize,
    src_cols_per_coset: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let src_rows = src.rows();
    let src_cols = src.cols();
    let dst_rows = dst.rows();
    let dst_cols = dst.cols();
    assert_eq!(src_rows, dst_rows_per_slot << log_values_per_leaf);
    assert_eq!(src_cols, num_cosets_in_tile * src_cols_per_coset);
    assert_eq!(dst_rows, dst_rows_per_slot << log_lde_factor);
    assert_eq!(dst_cols, src_cols_per_coset << log_values_per_leaf);
    assert!(num_cosets_in_tile.is_power_of_two());
    assert!(coset_index_base as usize + num_cosets_in_tile <= 1usize << log_lde_factor);
    assert!(dst_rows_per_slot <= u32::MAX as usize);
    assert!(num_cosets_in_tile <= u32::MAX as usize);
    assert!(src_cols_per_coset <= u32::MAX as usize);
    assert!(dst_cols <= u32::MAX as usize);
    let block_dim = (WARP_SIZE, 4);
    // Flat blockIdx.x packs (row_block, coset_in_tile) so num_cosets_in_tile
    // can scale to ~2^19 without hitting the gridDim.y/z 65535 cap. row_blocks
    // is a power of two since both packed_leaf_count (= dst_rows_per_slot) and
    // WARP_SIZE are; the kernel decomposes blockIdx.x with a shift+mask.
    let row_blocks = dst_rows_per_slot.get_chunks_count(WARP_SIZE as usize);
    assert!(row_blocks.is_power_of_two());
    let log_blocks_per_row_tile = row_blocks.trailing_zeros();
    let flat_blocks = row_blocks
        .checked_mul(num_cosets_in_tile)
        .expect("flat grid overflow");
    assert!(
        flat_blocks <= u32::MAX as usize,
        "flat grid {flat_blocks} > u32::MAX"
    );
    let grid_dim = (flat_blocks as u32, dst_cols.get_chunks_count(4) as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = PackRowsForWhirLeavesMultiCosetArguments::new(
        src.as_ptr_and_stride(),
        dst.as_mut_ptr_and_stride(),
        log_values_per_leaf,
        dst_rows_per_slot as u32,
        log_blocks_per_row_tile,
        log_lde_factor,
        coset_index_base,
        src_cols_per_coset as u32,
    );
    PackRowsForWhirLeavesMultiCosetFunction(ab_pack_rows_for_whir_leaves_multi_coset_bf_kernel)
        .launch(&config, &args)
}

cuda_kernel!(
  PartiallyEvaluateMonomialFormByRefSmall,
  partially_evaluate_monomial_form_by_ref_small,
  src: PtrAndStride<BF>,
  dst: *mut E4,
  z: *const E4,
  count: i32,
);

partially_evaluate_monomial_form_by_ref_small!(
    ab_partially_evaluate_monomial_form_by_ref_small_kernel
);

cuda_kernel!(
  PartiallyEvaluateMonomialFormByRef,
  partially_evaluate_monomial_form_by_ref,
  src: PtrAndStride<BF>,
  dst: *mut E4,
  z: *const E4,
  z_adjustment_ptr: *const E4,
  count: i32,
);

partially_evaluate_monomial_form_by_ref!(ab_partially_evaluate_monomial_form_by_ref_kernel);

#[allow(non_snake_case)]
pub(crate) fn partially_evaluate_monomials_by_ref(
    monomials: &impl DeviceMatrixChunkImpl<BF>,
    scratch0: &mut DeviceSlice<E4>,
    scratch1: &mut DeviceSlice<E4>,
    point: &DeviceSlice<E4>,
    count: usize,
    stream: &CudaStream,
) -> CudaResult<usize> {
    assert!(count.is_power_of_two());
    let log_count = count.trailing_zeros() as i32;
    let monomials = monomials.as_ptr_and_stride();
    let partial_evals = scratch0.as_mut_ptr();
    let z_ptr = point.as_ptr();
    let BLOCK_DIM = WARP_SIZE * 4;
    let VALS_PER_THREAD = 32;
    if count < (BLOCK_DIM * VALS_PER_THREAD) as usize {
        assert!(scratch0.len() >= count);
        let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(BLOCK_DIM, count as u32);
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = PartiallyEvaluateMonomialFormByRefSmallArguments::new(
            monomials,
            partial_evals,
            z_ptr,
            log_count as i32,
        );
        PartiallyEvaluateMonomialFormByRefSmallFunction(
            ab_partially_evaluate_monomial_form_by_ref_small_kernel,
        )
        .launch(&config, &args)?;
        return Ok(count);
    }
    let z_chunk_adjustment = &mut scratch1[..1];
    pow(&point[..1], VALS_PER_THREAD, z_chunk_adjustment, stream)?;
    let z_adjustment_ptr = z_chunk_adjustment.as_ptr();
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(BLOCK_DIM, count as u32 / VALS_PER_THREAD);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = PartiallyEvaluateMonomialFormByRefArguments::new(
        monomials,
        partial_evals,
        z_ptr,
        z_adjustment_ptr,
        log_count as i32,
    );
    PartiallyEvaluateMonomialFormByRefFunction(ab_partially_evaluate_monomial_form_by_ref_kernel)
        .launch(&config, &args)?;
    Ok(count / 32)
}

cuda_kernel_signature_arguments_and_function!(
    WhirFoldSplitHalfPair,
    values_a: *mut E4,
    values_b: *mut E4,
    challenge: *const E4,
    half_len: u32,
);

cuda_kernel_declaration!(
    ab_whir_fold_split_half_pair_e4_kernel(
        values_a: *mut E4,
        values_b: *mut E4,
        challenge: *const E4,
        half_len: u32,
    )
);

pub(crate) fn whir_fold_split_half_in_place_pair(
    values_a: &mut DeviceSlice<E4>,
    values_b: &mut DeviceSlice<E4>,
    challenge: &DeviceVariable<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(values_a.len(), values_b.len());
    assert!(values_a.len().is_power_of_two());
    assert!(values_a.len() >= 2);
    let half_len = (values_a.len() / 2) as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_warp_groups(4, half_len);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirFoldSplitHalfPairArguments::new(
        values_a.as_mut_ptr(),
        values_b.as_mut_ptr(),
        challenge.as_ptr(),
        half_len,
    );
    WhirFoldSplitHalfPairFunction(ab_whir_fold_split_half_pair_e4_kernel).launch(&config, &args)
}

const WHIR_THREE_POINT_BLOCK_THREADS: u32 = 256;

cuda_kernel_signature_arguments_and_function!(
    WhirThreePointPartials,
    eval: *const E4,
    eq: *const E4,
    partials: *mut E4,
    half: u32,
);

cuda_kernel_declaration!(
    ab_whir_three_point_partials_e4_kernel(
        eval: *const E4,
        eq: *const E4,
        partials: *mut E4,
        half: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    WhirThreePointFinalize,
    partials: *const E4,
    num_blocks: u32,
    reduce_out: *mut E4,
);

cuda_kernel_declaration!(
    ab_whir_three_point_finalize_e4_kernel(
        partials: *const E4,
        num_blocks: u32,
        reduce_out: *mut E4,
    )
);

cuda_kernel_signature_arguments_and_function!(
    WhirThreePointCombined,
    eval: *const E4,
    eq: *const E4,
    reduce_out: *mut E4,
    half: u32,
);

cuda_kernel_declaration!(
    ab_whir_three_point_combined_e4_kernel(
        eval: *const E4,
        eq: *const E4,
        reduce_out: *mut E4,
        half: u32,
    )
);

/// Computes the three sumcheck partials into `reduce_out[0..3]`. Picks the
/// single-launch combined kernel when `half` fits in one block, otherwise
/// stage-1 partials + stage-2 finalize. `partials` (typically `state.scratch0`)
/// must hold at least `num_blocks * 3` E4 on the two-launch path.
pub(crate) fn launch_whir_three_point_partials(
    eval: &DeviceSlice<E4>,
    eq: &DeviceSlice<E4>,
    partials: &mut DeviceSlice<E4>,
    reduce_out: &mut DeviceSlice<E4>,
    half: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(eval.len() >= 2 * half);
    assert!(eq.len() >= 2 * half);
    assert!(reduce_out.len() >= 3);
    assert!(half >= 1);
    assert!(half <= u32::MAX as usize);

    let block = WHIR_THREE_POINT_BLOCK_THREADS;
    if half as u32 <= block {
        let config = CudaLaunchConfig::basic(1, block, stream);
        let args = WhirThreePointCombinedArguments::new(
            eval.as_ptr(),
            eq.as_ptr(),
            reduce_out.as_mut_ptr(),
            half as u32,
        );
        return WhirThreePointCombinedFunction(ab_whir_three_point_combined_e4_kernel)
            .launch(&config, &args);
    }

    let num_blocks = half.div_ceil(block as usize) as u32;
    assert!(partials.len() >= (num_blocks as usize) * 3);
    let partials_ptr = partials.as_mut_ptr();
    let stage1_config = CudaLaunchConfig::basic(num_blocks, block, stream);
    let stage1_args =
        WhirThreePointPartialsArguments::new(eval.as_ptr(), eq.as_ptr(), partials_ptr, half as u32);
    WhirThreePointPartialsFunction(ab_whir_three_point_partials_e4_kernel)
        .launch(&stage1_config, &stage1_args)?;

    let stage2_config = CudaLaunchConfig::basic(1, block, stream);
    let stage2_args =
        WhirThreePointFinalizeArguments::new(partials_ptr, num_blocks, reduce_out.as_mut_ptr());
    WhirThreePointFinalizeFunction(ab_whir_three_point_finalize_e4_kernel)
        .launch(&stage2_config, &stage2_args)
}

cuda_kernel_signature_arguments_and_function!(
    WhirBuildEqFactorTablesBatched,
    claim_points: *const E4,
    challenge_count: u32,
    eq_high_array: *mut E4,
    eq_low_array: *mut E4,
);

cuda_kernel_declaration!(
    ab_whir_build_eq_factor_tables_batched_e4_kernel(
        claim_points: *const E4,
        challenge_count: u32,
        eq_high_array: *mut E4,
        eq_low_array: *mut E4,
    )
);

cuda_kernel_signature_arguments_and_function!(
    WhirAccumulateEqSamplesBatched,
    eq_high_array: *const E4,
    eq_low_array: *const E4,
    sizes: GkrEqSizes,
    challenges: *const E4,
    eq_poly: *mut E4,
    num_queries: u32,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_whir_accumulate_eq_samples_batched_e4_kernel(
        eq_high_array: *const E4,
        eq_low_array: *const E4,
        sizes: GkrEqSizes,
        challenges: *const E4,
        eq_poly: *mut E4,
        num_queries: u32,
        acc_size: u32,
    )
);

/// `(eq_high_array_len, eq_low_array_len)` in E4 for `num_queries` queries.
pub(crate) fn batched_eq_factor_scratch_lens(num_queries: usize) -> (usize, usize) {
    (
        num_queries * GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN,
        num_queries * GKR_EQ_GROUP_TABLE_LEN,
    )
}

/// Builds per-query factored-eq slabs and folds
/// `sum_q( eq(point_q, gid) * challenges[q] )` into `eq_poly[gid]` (RMW).
/// Two launches regardless of `num_queries`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_batched_accumulate_eq_samples(
    claim_points: *const E4,
    challenges: *const E4,
    num_queries: usize,
    challenge_count: usize,
    eq_high_array: *mut E4,
    eq_low_array: *mut E4,
    eq_poly: *mut E4,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(num_queries <= u32::MAX as usize);
    assert!(challenge_count <= u32::MAX as usize);
    assert!(acc_size <= u32::MAX as usize);
    let blocks_x = eq_group_count(challenge_count).max(GKR_EQ_HIGH_SLOTS);
    let build_config = CudaLaunchConfig::basic(
        (blocks_x as u32, num_queries as u32, 1u32),
        GKR_EQ_GROUP_TABLE_LEN as u32,
        context.get_exec_stream(),
    );
    let build_args = WhirBuildEqFactorTablesBatchedArguments::new(
        claim_points,
        challenge_count as u32,
        eq_high_array,
        eq_low_array,
    );
    WhirBuildEqFactorTablesBatchedFunction(ab_whir_build_eq_factor_tables_batched_e4_kernel)
        .launch(&build_config, &build_args)?;

    let acc_config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let acc_args = WhirAccumulateEqSamplesBatchedArguments::new(
        eq_high_array,
        eq_low_array,
        make_eq_sizes(challenge_count),
        challenges,
        eq_poly,
        num_queries as u32,
        acc_size as u32,
    );
    WhirAccumulateEqSamplesBatchedFunction(ab_whir_accumulate_eq_samples_batched_e4_kernel)
        .launch(&acc_config, &acc_args)
}

#[cfg(test)]
mod tests;
