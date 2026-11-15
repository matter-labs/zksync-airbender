use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart::{
    cuda_kernel, cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function,
};

use gpu_core::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use gpu_core::primitives::field::{BF, E4};
use gpu_hash::blake2s::Digest;
use gpu_ops::simple::pow;
// Production: the (de)serialize / accumulate launchers here read `EXT4_DEGREE`
// via `<E4 as FieldExtension<BF>>::DEGREE`.
use crate::upstream::FieldExtension;
use gpu_core::primitives::utils::{
    get_grid_block_dims_for_threads_count, get_grid_block_dims_for_warp_groups, WARP_SIZE,
};
use gpu_gkr::backward::{
    eq_group_count, gkr_dim_reducing_launch_config, make_eq_sizes, GkrEqSizes,
    GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS,
};
use gpu_prover_context::ProverContext;

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
    AccumulateWhirBaseColumnsWithSerializedBf,
    metadata: BaseColumnsBatchingMetadata,
    serialized_bf: *mut BF,
);

cuda_kernel_declaration!(
    ab_accumulate_whir_base_columns_with_serialized_bf_e4_kernel(
        metadata: BaseColumnsBatchingMetadata,
        serialized_bf: *mut BF,
    )
);

/// Write the E4 result and its column-major BF vectorization in one pass.
pub(crate) fn accumulate_whir_base_columns_with_serialized_bf(
    memory_values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    witness_values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    setup_values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    memory_weights: &DeviceSlice<E4>,
    witness_weights: &DeviceSlice<E4>,
    setup_weights: &DeviceSlice<E4>,
    result: &mut DeviceSlice<E4>,
    serialized_bf: &mut DeviceSlice<BF>,
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
    assert_eq!(
        serialized_bf.len(),
        result.len() * <E4 as FieldExtension<BF>>::DEGREE
    );
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
    let rows = memory_values.rows() as u32;
    let metadata = BaseColumnsBatchingMetadata {
        values,
        weights,
        cols,
        strides,
        result: result.as_mut_ptr(),
        rows,
    };
    let (grid_dim, block_dim) = get_grid_block_dims_for_warp_groups(4, rows);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = AccumulateWhirBaseColumnsWithSerializedBfArguments::new(
        metadata,
        serialized_bf.as_mut_ptr(),
    );
    AccumulateWhirBaseColumnsWithSerializedBfFunction(
        ab_accumulate_whir_base_columns_with_serialized_bf_e4_kernel,
    )
    .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    WhirFoldAdjacentVectorized,
    src: PtrAndStride<BF>,
    dst: MutPtrAndStride<BF>,
    challenge: *const E4,
    half_len: i32,
);

cuda_kernel_declaration!(
    ab_whir_fold_adjacent_vectorized_e4_kernel(
        src: PtrAndStride<BF>,
        dst: MutPtrAndStride<BF>,
        challenge: *const E4,
        half_len: i32,
    )
);

/// Out of place — the adjacent pairing overlaps the read and write ranges
/// across blocks.
pub(crate) fn whir_fold_adjacent_vectorized(
    src: &impl DeviceMatrixChunkImpl<BF>,
    dst: &mut impl DeviceMatrixChunkMutImpl<BF>,
    challenge: &DeviceVariable<E4>,
    half_len: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(src.cols(), 4);
    assert_eq!(dst.cols(), 4);
    assert!(2 * half_len <= src.stride());
    assert!(half_len <= dst.stride());
    let (grid_dim, block_dim) = get_grid_block_dims_for_warp_groups(4, half_len as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirFoldAdjacentVectorizedArguments::new(
        src.as_ptr_and_stride(),
        dst.as_mut_ptr_and_stride(),
        challenge.as_ptr(),
        half_len as i32,
    );
    WhirFoldAdjacentVectorizedFunction(ab_whir_fold_adjacent_vectorized_e4_kernel)
        .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    WhirFoldAdjacent,
    src: *const E4,
    dst: *mut E4,
    challenge: *const E4,
    half_len: u32,
);

cuda_kernel_declaration!(
    ab_whir_fold_adjacent_e4_kernel(
        src: *const E4,
        dst: *mut E4,
        challenge: *const E4,
        half_len: u32,
    )
);

/// Out of place — the adjacent pairing overlaps the read and write ranges
/// across blocks.
#[cfg(test)]
pub(crate) fn whir_fold_adjacent(
    src: &DeviceSlice<E4>,
    dst: &mut DeviceSlice<E4>,
    challenge: &DeviceVariable<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(src.len().is_power_of_two());
    assert!(src.len() >= 2);
    assert!(src.len() / 2 <= u32::MAX as usize);
    let half_len = (src.len() / 2) as u32;
    assert!(dst.len() >= half_len as usize);
    let (grid_dim, block_dim) = get_grid_block_dims_for_warp_groups(4, half_len);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirFoldAdjacentArguments::new(
        src.as_ptr(),
        dst.as_mut_ptr(),
        challenge.as_ptr(),
        half_len,
    );
    WhirFoldAdjacentFunction(ab_whir_fold_adjacent_e4_kernel).launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    ReduceStagedWhirSubtreesNaturalTiles,
    staged: *const u32,
    boundary_roots: *mut u32,
    log_packed_leaf_count: u32,
    log_lde_factor: u32,
    first_tile_coset_base: u32,
    staged_tile_leaves: u32,
    tiles_count: u32,
    tile_coset_stride: u32,
    roots_count: u32,
);

cuda_kernel_declaration!(
    ab_reduce_staged_whir_subtrees_natural_tiles_kernel(
        staged: *const u32,
        boundary_roots: *mut u32,
        log_packed_leaf_count: u32,
        log_lde_factor: u32,
        first_tile_coset_base: u32,
        staged_tile_leaves: u32,
        tiles_count: u32,
        tile_coset_stride: u32,
        roots_count: u32,
    )
);

pub(crate) fn reduce_staged_whir_subtrees_natural_tiles(
    staged: &DeviceSlice<Digest>,
    boundary_roots: &mut DeviceSlice<Digest>,
    log_packed_leaf_count: u32,
    log_lde_factor: u32,
    first_tile_coset_base: u32,
    staged_tile_leaves: u32,
    tiles_count: u32,
    tile_coset_stride: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    const ROOTS_PER_BLOCK: u32 = 16;
    const LEAVES_PER_BLOCK: usize = 512;
    assert!(log_packed_leaf_count >= WARP_SIZE.trailing_zeros());
    assert!(log_lde_factor < 32);
    assert!(tiles_count >= 1);
    assert!(staged_tile_leaves >= WARP_SIZE);
    assert_eq!(staged_tile_leaves % WARP_SIZE, 0);
    assert_eq!(
        staged.len(),
        staged_tile_leaves as usize * tiles_count as usize
    );
    let packed_leaf_count = 1usize << log_packed_leaf_count;
    let lde_factor = 1usize << log_lde_factor;
    assert_eq!(staged_tile_leaves as usize % packed_leaf_count, 0);
    let tile_cosets = staged_tile_leaves as usize / packed_leaf_count;
    assert!(tiles_count == 1 || tile_coset_stride as usize >= tile_cosets);
    let last_natural_coset = first_tile_coset_base as usize
        + (tiles_count as usize - 1) * tile_coset_stride as usize
        + tile_cosets
        - 1;
    assert!(last_natural_coset < lde_factor);
    let roots_per_coset = packed_leaf_count / WARP_SIZE as usize;
    let max_bitrev_coset = (0..tiles_count as usize)
        .flat_map(|tile| {
            let tile_base = first_tile_coset_base as usize + tile * tile_coset_stride as usize;
            (0..tile_cosets).map(move |coset| {
                (tile_base + coset).reverse_bits() >> (usize::BITS - log_lde_factor)
            })
        })
        .max()
        .unwrap();
    assert!(boundary_roots.len() >= (max_bitrev_coset + 1) * roots_per_coset);
    let roots_count = staged.len() / WARP_SIZE as usize;
    assert!(roots_count <= u32::MAX as usize);
    let mut config = CudaLaunchConfig::basic(
        (roots_count as u32).div_ceil(ROOTS_PER_BLOCK),
        256u32,
        stream,
    );
    config.dynamic_smem_bytes = LEAVES_PER_BLOCK * core::mem::size_of::<Digest>();
    let args = ReduceStagedWhirSubtreesNaturalTilesArguments::new(
        staged.as_ptr() as *const u32,
        boundary_roots.as_mut_ptr() as *mut u32,
        log_packed_leaf_count,
        log_lde_factor,
        first_tile_coset_base,
        staged_tile_leaves,
        tiles_count,
        tile_coset_stride,
        roots_count as u32,
    );
    ReduceStagedWhirSubtreesNaturalTilesFunction(
        ab_reduce_staged_whir_subtrees_natural_tiles_kernel,
    )
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
  z_stride_ptr: *const E4,
  count: i32,
);

partially_evaluate_monomial_form_by_ref!(ab_partially_evaluate_monomial_form_by_ref_kernel);

const MONOMIAL_EVAL_BLOCK_THREADS: u32 = WARP_SIZE * 4;
const MONOMIAL_EVAL_VALUES_PER_THREAD: usize = 32;

/// Scratch for monomial partial evaluations and their subsequent sum. The
/// second buffer also holds the large kernel's single point-power adjustment.
pub(crate) fn monomial_eval_scratch_lens(count: usize) -> (usize, usize) {
    assert!(count.is_power_of_two());
    let large = count >= MONOMIAL_EVAL_BLOCK_THREADS as usize * MONOMIAL_EVAL_VALUES_PER_THREAD;
    let partials = if large {
        count / MONOMIAL_EVAL_VALUES_PER_THREAD
    } else {
        count
    };
    let sum_partials = if partials > WHIR_SUM_BLOCK_THREADS as usize {
        partials.div_ceil(WHIR_SUM_BLOCK_THREADS as usize)
    } else {
        0
    };
    (partials, sum_partials.max(usize::from(large)))
}

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
    let partials_len = monomial_eval_scratch_lens(count).0;
    assert!(scratch0.len() >= partials_len);
    // This launcher only needs the point-power slot on its large path.
    // Scratch for a subsequent whir_sum is the caller's separate requirement.
    if count < MONOMIAL_EVAL_BLOCK_THREADS as usize * MONOMIAL_EVAL_VALUES_PER_THREAD {
        let (grid_dim, block_dim) =
            get_grid_block_dims_for_threads_count(MONOMIAL_EVAL_BLOCK_THREADS, count as u32);
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = PartiallyEvaluateMonomialFormByRefSmallArguments::new(
            monomials,
            partial_evals,
            z_ptr,
            log_count,
        );
        PartiallyEvaluateMonomialFormByRefSmallFunction(
            ab_partially_evaluate_monomial_form_by_ref_small_kernel,
        )
        .launch(&config, &args)?;
        return Ok(count);
    }
    // The grid is exact: `count / MONOMIAL_EVAL_VALUES_PER_THREAD` is a power of two >= MONOMIAL_EVAL_BLOCK_THREADS.
    let gmem_stride = count as u32 / MONOMIAL_EVAL_VALUES_PER_THREAD as u32;
    let z_stride = &mut scratch1[..1];
    pow(&point[..1], gmem_stride, z_stride, stream)?;
    let z_stride_ptr = z_stride.as_ptr();
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(MONOMIAL_EVAL_BLOCK_THREADS, gmem_stride);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = PartiallyEvaluateMonomialFormByRefArguments::new(
        monomials,
        partial_evals,
        z_ptr,
        z_stride_ptr,
        log_count,
    );
    PartiallyEvaluateMonomialFormByRefFunction(ab_partially_evaluate_monomial_form_by_ref_kernel)
        .launch(&config, &args)?;
    Ok(count / MONOMIAL_EVAL_VALUES_PER_THREAD)
}

cuda_kernel_signature_arguments_and_function!(
    WhirFoldAdjacentPair,
    src_a: *const E4,
    dst_a: *mut E4,
    src_b: *const E4,
    dst_b: *mut E4,
    challenge: *const E4,
    half_len: u32,
);

cuda_kernel_declaration!(
    ab_whir_fold_adjacent_pair_e4_kernel(
        src_a: *const E4,
        dst_a: *mut E4,
        src_b: *const E4,
        dst_b: *mut E4,
        challenge: *const E4,
        half_len: u32,
    )
);

pub(crate) fn whir_fold_adjacent_pair(
    src_a: &DeviceSlice<E4>,
    dst_a: &mut DeviceSlice<E4>,
    src_b: &DeviceSlice<E4>,
    dst_b: &mut DeviceSlice<E4>,
    challenge: &DeviceVariable<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(src_a.len(), src_b.len());
    assert!(src_a.len().is_power_of_two());
    assert!(src_a.len() >= 2);
    let half_len = (src_a.len() / 2) as u32;
    assert!(dst_a.len() >= half_len as usize);
    assert!(dst_b.len() >= half_len as usize);
    let (grid_dim, block_dim) = get_grid_block_dims_for_warp_groups(4, half_len);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirFoldAdjacentPairArguments::new(
        src_a.as_ptr(),
        dst_a.as_mut_ptr(),
        src_b.as_ptr(),
        dst_b.as_mut_ptr(),
        challenge.as_ptr(),
        half_len,
    );
    WhirFoldAdjacentPairFunction(ab_whir_fold_adjacent_pair_e4_kernel).launch(&config, &args)
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

pub(crate) fn whir_three_point_partials_len(half: usize) -> usize {
    if half <= WHIR_THREE_POINT_BLOCK_THREADS as usize {
        0
    } else {
        half.div_ceil(WHIR_THREE_POINT_BLOCK_THREADS as usize) * 3
    }
}

/// Computes the three sumcheck partials into `reduce_out[0..3]`. Picks the
/// single-launch combined kernel when `half` fits in one block, otherwise
/// stage-1 partials + stage-2 finalize. `partials`
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
    assert!(partials.len() >= whir_three_point_partials_len(half));
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

const WHIR_SUM_BLOCK_THREADS: u32 = 256;

cuda_kernel_signature_arguments_and_function!(
    WhirSum,
    values: *const E4,
    count: u32,
    out: *mut E4,
);

cuda_kernel_declaration!(
    ab_whir_sum_e4_kernel(
        values: *const E4,
        count: u32,
        out: *mut E4,
    )
);

/// Sums `values` into `out`. Single-launch when `values` fits in one block,
/// otherwise stage-1 block partials (into `partials`) + stage-2 single-block
/// finish; `partials` must hold at least `values.len().div_ceil(256)` E4 on
/// the two-launch path.
pub(crate) fn whir_sum(
    values: &DeviceSlice<E4>,
    partials: &mut DeviceSlice<E4>,
    out: &mut DeviceVariable<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = values.len();
    assert!(count >= 1);
    assert!(count <= u32::MAX as usize);

    let block = WHIR_SUM_BLOCK_THREADS;
    if count as u32 <= block {
        let config = CudaLaunchConfig::basic(1, block, stream);
        let args = WhirSumArguments::new(values.as_ptr(), count as u32, out.as_mut_ptr());
        return WhirSumFunction(ab_whir_sum_e4_kernel).launch(&config, &args);
    }

    let num_blocks = count.div_ceil(block as usize) as u32;
    assert!(partials.len() >= num_blocks as usize);
    let partials_ptr = partials.as_mut_ptr();
    let stage1_config = CudaLaunchConfig::basic(num_blocks, block, stream);
    let stage1_args = WhirSumArguments::new(values.as_ptr(), count as u32, partials_ptr);
    WhirSumFunction(ab_whir_sum_e4_kernel).launch(&stage1_config, &stage1_args)?;

    let stage2_config = CudaLaunchConfig::basic(1, block, stream);
    let stage2_args = WhirSumArguments::new(partials_ptr, num_blocks, out.as_mut_ptr());
    WhirSumFunction(ab_whir_sum_e4_kernel).launch(&stage2_config, &stage2_args)
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

// 2-chunk split-eq path: balanced high/low factored tables (high_bits + low_bits == log_n).
// Replaces the 3-slot 8/8/7 layout used by the GKR-style builder when running
// the WHIR query accumulator, dropping the inner loop from 3 E4 muls/query to 1.

cuda_kernel_signature_arguments_and_function!(
    WhirBuildSplitEqTable,
    claim_points: *const E4,
    scales: *const E4,
    log_n: u32,
    bits: u32,
    claim_offset: u32,
    out_array: *mut E4,
);

cuda_kernel_declaration!(
    ab_whir_build_split_eq_table_e4_kernel(
        claim_points: *const E4,
        scales: *const E4,
        log_n: u32,
        bits: u32,
        claim_offset: u32,
        out_array: *mut E4,
    )
);

cuda_kernel_signature_arguments_and_function!(
    WhirAccumulateEqSplit,
    eq_high_array: *const E4,
    eq_low_array: *const E4,
    high_bits: u32,
    low_bits: u32,
    eq_poly: *mut E4,
    num_queries: u32,
    acc_size: u32,
);

cuda_kernel_declaration!(
    ab_whir_accumulate_eq_split_e4_kernel(
        eq_high_array: *const E4,
        eq_low_array: *const E4,
        high_bits: u32,
        low_bits: u32,
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
    // At `challenge_count == 0` the low eq buffer is never written but
    // `make_eq_sizes(0)` still reports `low = 0`, so the accumulator would read
    // uninitialized device memory.
    assert!(
        challenge_count >= 1,
        "challenge_count >= 1: at 0 the low eq buffer is never written and the \
         accumulator would read uninitialized device memory at eq_low[0]"
    );
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

/// `(high_bits, low_bits)` for the 2-chunk split-eq layout:
/// `high_bits = ceil(log_n / 2)`, `low_bits = log_n - high_bits`.
pub(crate) fn split_eq_bits(log_n: usize) -> (usize, usize) {
    let high_bits = log_n.div_ceil(2);
    let low_bits = log_n - high_bits;
    (high_bits, low_bits)
}

/// `(eq_high_array_len, eq_low_array_len)` in E4 for `num_queries` queries
/// using the 2-chunk split layout.
pub(crate) fn split_eq_factor_scratch_lens(num_queries: usize, log_n: usize) -> (usize, usize) {
    let (high_bits, low_bits) = split_eq_bits(log_n);
    (
        num_queries * (1usize << high_bits),
        num_queries * (1usize << low_bits),
    )
}

const SPLIT_BUILD_BLOCK_THREADS: u32 = 256;

fn launch_build_split_eq_table(
    claim_points: *const E4,
    scales: *const E4,
    log_n: usize,
    bits: usize,
    claim_offset: usize,
    num_queries: usize,
    out_array: &mut DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<()> {
    // Both bounds fail silently: an over-large `bits` writes past the
    // destination while staying inside the pool, so no CUDA error is raised.
    assert!(claim_offset + bits <= log_n);
    assert!(out_array.len() >= num_queries << bits);
    let table_size = 1u32 << bits;
    let block = SPLIT_BUILD_BLOCK_THREADS.min(table_size);
    let grid_x = table_size.div_ceil(block);
    let config = CudaLaunchConfig::basic(
        (grid_x, num_queries as u32, 1u32),
        block,
        context.get_exec_stream(),
    );
    let args = WhirBuildSplitEqTableArguments::new(
        claim_points,
        scales,
        log_n as u32,
        bits as u32,
        claim_offset as u32,
        out_array.as_mut_ptr(),
    );
    WhirBuildSplitEqTableFunction(ab_whir_build_split_eq_table_e4_kernel).launch(&config, &args)
}

/// 2-chunk variant of [`launch_batched_accumulate_eq_samples`]: builds
/// per-query high (size `1 << high_bits`) and challenges-scaled low
/// (size `1 << low_bits`) slabs, then accumulates
/// `sum_q( eq(point_q, gid) * challenges[q] )` into `eq_poly[gid]` (RMW)
/// using one E4 mul + one E4 add per query in the inner loop.
/// Three launches total (one per slab build + accumulator), regardless of
/// `num_queries`.
pub(crate) fn launch_split_accumulate_eq_samples(
    claim_points: *const E4,
    challenges: *const E4,
    num_queries: usize,
    log_n: usize,
    eq_high_array: &mut DeviceSlice<E4>,
    eq_low_array: &mut DeviceSlice<E4>,
    eq_poly: *mut E4,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(num_queries <= u32::MAX as usize);
    assert!(log_n >= 2);
    assert!(log_n <= 30);
    assert!(acc_size <= u32::MAX as usize);
    let (high_bits, low_bits) = split_eq_bits(log_n);

    // LSB pairing puts coordinates `low_bits..log_n` on the high slab and
    // `0..low_bits` on the low slab.
    // High slab: no challenge scaling.
    launch_build_split_eq_table(
        claim_points,
        std::ptr::null(),
        log_n,
        high_bits,
        low_bits,
        num_queries,
        eq_high_array,
        context,
    )?;
    // Low slab: pre-scaled by challenges[q] so the accumulator inner loop
    // collapses to one E4 mul + one E4 add per query.
    launch_build_split_eq_table(
        claim_points,
        challenges,
        log_n,
        low_bits,
        0,
        num_queries,
        eq_low_array,
        context,
    )?;

    let acc_config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let acc_args = WhirAccumulateEqSplitArguments::new(
        eq_high_array.as_ptr(),
        eq_low_array.as_ptr(),
        high_bits as u32,
        low_bits as u32,
        eq_poly,
        num_queries as u32,
        acc_size as u32,
    );
    WhirAccumulateEqSplitFunction(ab_whir_accumulate_eq_split_e4_kernel)
        .launch(&acc_config, &acc_args)
}

#[cfg(test)]
mod tests;
