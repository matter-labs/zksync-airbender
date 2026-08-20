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
use gpu_ntt::ntt_twiddles::WhirLeafTransformParams;
use gpu_ops::simple::pow;
// Production: the (de)serialize / accumulate launchers here read `EXT4_DEGREE`
// via `<E4 as FieldExtension<BF>>::DEGREE`.
use crate::upstream::FieldExtension;
// Only used by the #[cfg(test)] `pack_rows_for_whir_leaves_multi_coset` below.
#[cfg(test)]
use gpu_core::primitives::utils::GetChunksCount;
use gpu_core::primitives::utils::{
    get_grid_block_dims_for_threads_count, get_grid_block_dims_for_warp_groups, WARP_SIZE,
};
use gpu_gkr::backward::{
    eq_group_count, gkr_dim_reducing_launch_config, make_eq_sizes, GkrEqSizes,
    GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS,
};
use gpu_prover_context::ProverContext;

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

#[cfg(test)]
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

#[cfg(test)]
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

/// Fused `accumulate_whir_base_columns` + `serialize_whir_e4_columns`: writes
/// the E4 result into `result` and the column-major BF vectorization (4
/// columns of `rows` BFs each) into `serialized_bf` in a single pass.
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

/// LSB-binding fold of the vectorized monomial form:
/// `dst[i] = src[2i] + challenge * src[2i + 1]` (CPU `fold_monomial_form`).
/// Out of place — the adjacent pairing makes the read range overlap the write
/// range across blocks.
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

/// LSB-binding fold of one evaluation-form leg: `dst[i] = src[2i] + r * (src[2i+1] - src[2i])`.
/// Out of place — the adjacent pairing makes the read and write ranges overlap
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
    GatherCoefficientLeavesForQueriesFromNtt,
    src: PtrAndStride<BF>,
    leaf_dst: *mut BF,
    transform_params: WhirLeafTransformParams,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    query_indexes: *const u32,
    indexes_count: u32,
);

cuda_kernel_declaration!(
    ab_gather_coefficient_leaves_for_queries_from_ntt_kernel(
        src: PtrAndStride<BF>,
        leaf_dst: *mut BF,
        transform_params: WhirLeafTransformParams,
        log_trace_len: u32,
        log_lde_factor: u32,
        log_values_per_leaf: u32,
        query_indexes: *const u32,
        indexes_count: u32,
    )
);

pub(crate) fn gather_coefficient_leaves_for_queries_from_ntt(
    ntt_output: &DeviceSlice<BF>,
    leaf_dst: &mut DeviceSlice<BF>,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    log_src_cols_per_coset: u32,
    transform_params: WhirLeafTransformParams,
    query_indexes: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!((1..=5).contains(&log_values_per_leaf));
    assert!(log_trace_len > log_values_per_leaf);
    assert_eq!(log_src_cols_per_coset, 2, "coefficient queries require E4");
    assert!(!query_indexes.is_empty());
    assert!(query_indexes.len() <= u32::MAX as usize);
    let trace_len = 1usize << log_trace_len;
    let lde_factor = 1usize << log_lde_factor;
    assert_eq!(ntt_output.len(), trace_len * lde_factor * 4);
    let values_per_leaf = 1usize << log_values_per_leaf;
    assert_eq!(leaf_dst.len(), query_indexes.len() * values_per_leaf * 4);

    let block_dim_x = (query_indexes.len() as u32).min(WARP_SIZE);
    let block_dim_y = (values_per_leaf / 2) as u32;
    let grid_dim_x = (query_indexes.len() as u32).div_ceil(block_dim_x);
    let mut config = CudaLaunchConfig::basic(grid_dim_x, (block_dim_x, block_dim_y), stream);
    if log_values_per_leaf > 1 {
        config.dynamic_smem_bytes =
            2 * block_dim_x as usize * block_dim_y as usize * core::mem::size_of::<E4>()
                + block_dim_x as usize * block_dim_y as usize * core::mem::size_of::<BF>();
    }
    let args = GatherCoefficientLeavesForQueriesFromNttArguments::new(
        PtrAndStride::new(ntt_output.as_ptr(), trace_len),
        leaf_dst.as_mut_ptr(),
        transform_params,
        log_trace_len,
        log_lde_factor,
        log_values_per_leaf,
        query_indexes.as_ptr(),
        query_indexes.len() as u32,
    );
    GatherCoefficientLeavesForQueriesFromNttFunction(
        ab_gather_coefficient_leaves_for_queries_from_ntt_kernel,
    )
    .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    GatherCoefficientLeavesAndMerklePathsPartialForQueriesFromNtt,
    src: PtrAndStride<BF>,
    partial_tree: *const u32,
    leaf_dst: *mut BF,
    path_dst: *mut u32,
    transform_params: WhirLeafTransformParams,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    log_total_leaves_count: u32,
    layers_count: u32,
    query_indexes: *const u32,
    indexes_count: u32,
);

cuda_kernel_declaration!(
    ab_gather_coefficient_leaves_and_merkle_paths_partial_for_queries_from_ntt_kernel(
        src: PtrAndStride<BF>,
        partial_tree: *const u32,
        leaf_dst: *mut BF,
        path_dst: *mut u32,
        transform_params: WhirLeafTransformParams,
        log_trace_len: u32,
        log_lde_factor: u32,
        log_values_per_leaf: u32,
        log_total_leaves_count: u32,
        layers_count: u32,
        query_indexes: *const u32,
        indexes_count: u32,
    )
);

pub(crate) fn gather_coefficient_leaves_and_merkle_paths_partial_for_queries_from_ntt(
    ntt_output: &DeviceSlice<BF>,
    partial_tree: &DeviceSlice<u32>,
    leaf_dst: &mut DeviceSlice<BF>,
    path_dst: &mut DeviceSlice<u32>,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    log_src_cols_per_coset: u32,
    log_packed_leaf_count: u32,
    log_total_leaves_count: u32,
    layers_count: u32,
    transform_params: WhirLeafTransformParams,
    query_indexes: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!((1..=5).contains(&log_values_per_leaf));
    assert!(log_trace_len > log_values_per_leaf);
    assert_eq!(log_src_cols_per_coset, 2, "coefficient queries require E4");
    assert_eq!(log_packed_leaf_count, log_trace_len - log_values_per_leaf);
    assert_eq!(
        log_total_leaves_count,
        log_packed_leaf_count + log_lde_factor
    );
    assert!(log_total_leaves_count >= 6);
    assert!(layers_count > 5);
    assert!(!query_indexes.is_empty());
    assert!(query_indexes.len() <= u32::MAX as usize);
    let trace_len = 1usize << log_trace_len;
    let lde_factor = 1usize << log_lde_factor;
    assert_eq!(ntt_output.len(), trace_len * lde_factor * 4);
    let values_per_leaf = 1usize << log_values_per_leaf;
    assert_eq!(leaf_dst.len(), query_indexes.len() * values_per_leaf * 4);
    assert_eq!(
        path_dst.len(),
        query_indexes.len() * layers_count as usize * gpu_hash::blake2s::STATE_SIZE
    );
    assert_eq!(
        partial_tree.len(),
        (1usize << (log_total_leaves_count + 1 - 5)) * gpu_hash::blake2s::STATE_SIZE
    );

    let block_dim = (WARP_SIZE, (values_per_leaf / 2) as u32);
    let mut config = CudaLaunchConfig::basic(query_indexes.len() as u32, block_dim, stream);
    config.dynamic_smem_bytes = WARP_SIZE as usize * values_per_leaf * core::mem::size_of::<E4>()
        + if log_values_per_leaf > 1 {
            WARP_SIZE as usize * (values_per_leaf / 2) * core::mem::size_of::<BF>()
        } else {
            0
        };
    let args = GatherCoefficientLeavesAndMerklePathsPartialForQueriesFromNttArguments::new(
        PtrAndStride::new(ntt_output.as_ptr(), trace_len),
        partial_tree.as_ptr(),
        leaf_dst.as_mut_ptr(),
        path_dst.as_mut_ptr(),
        transform_params,
        log_trace_len,
        log_lde_factor,
        log_values_per_leaf,
        log_total_leaves_count,
        layers_count,
        query_indexes.as_ptr(),
        query_indexes.len() as u32,
    );
    GatherCoefficientLeavesAndMerklePathsPartialForQueriesFromNttFunction(
        ab_gather_coefficient_leaves_and_merkle_paths_partial_for_queries_from_ntt_kernel,
    )
    .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    TransformAndHashWhirLeavesFromNttMultiCoset,
    src: PtrAndStride<BF>,
    results: *mut u32,
    transform_params: WhirLeafTransformParams,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    coset_index_base: u32,
    leaves_count: u32,
);

cuda_kernel_declaration!(
    ab_transform_and_hash_whir_leaves_from_ntt_multi_coset_kernel(
        src: PtrAndStride<BF>,
        results: *mut u32,
        transform_params: WhirLeafTransformParams,
        log_trace_len: u32,
        log_lde_factor: u32,
        log_values_per_leaf: u32,
        coset_index_base: u32,
        leaves_count: u32,
    )
);

pub(crate) fn transform_and_hash_whir_leaves_from_ntt_multi_coset(
    ntt_output: &DeviceSlice<BF>,
    results: &mut DeviceSlice<Digest>,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    coset_index_base: u32,
    cosets_in_tile: u32,
    transform_params: WhirLeafTransformParams,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_lde_factor >= 1);
    assert!((1..=5).contains(&log_values_per_leaf));
    assert!(log_trace_len > log_values_per_leaf);
    assert!(cosets_in_tile >= 1);
    assert!(coset_index_base + cosets_in_tile <= 1u32 << log_lde_factor);
    let trace_len = 1usize << log_trace_len;
    let packed_leaf_count = 1usize << (log_trace_len - log_values_per_leaf);
    let leaves_count = packed_leaf_count
        .checked_mul(cosets_in_tile as usize)
        .expect("tile leaf count overflow");
    assert!(leaves_count <= u32::MAX as usize);
    assert!(ntt_output.len() >= trace_len * 4 * cosets_in_tile as usize);

    let max_bitrev_coset = (0..cosets_in_tile)
        .map(|offset| (coset_index_base + offset).reverse_bits() >> (u32::BITS - log_lde_factor))
        .max()
        .unwrap();
    assert!(
        results.len() >= (max_bitrev_coset as usize + 1) * packed_leaf_count,
        "results do not cover the tile's highest bit-reversed coset",
    );

    let values_per_leaf = 1usize << log_values_per_leaf;
    let block_dim_x = if values_per_leaf == 2 {
        (leaves_count as u32).min(4 * WARP_SIZE)
    } else {
        WARP_SIZE
    };
    let block_dim_y = (values_per_leaf / 2) as u32;
    let grid_dim_x = (leaves_count as u32).div_ceil(block_dim_x);
    let mut config = CudaLaunchConfig::basic(grid_dim_x, (block_dim_x, block_dim_y), stream);
    config.dynamic_smem_bytes = block_dim_x as usize * values_per_leaf * core::mem::size_of::<E4>()
        + if log_values_per_leaf > 1 {
            block_dim_x as usize * block_dim_y as usize * core::mem::size_of::<BF>()
        } else {
            0
        };
    let args = TransformAndHashWhirLeavesFromNttMultiCosetArguments::new(
        PtrAndStride::new(ntt_output.as_ptr(), trace_len),
        results.as_mut_ptr() as *mut u32,
        transform_params,
        log_trace_len,
        log_lde_factor,
        log_values_per_leaf,
        coset_index_base,
        leaves_count as u32,
    );
    TransformAndHashWhirLeavesFromNttMultiCosetFunction(
        ab_transform_and_hash_whir_leaves_from_ntt_multi_coset_kernel,
    )
    .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    TransformAndHashWhirLeavesFromNttMultiCosetToStaging,
    src: PtrAndStride<BF>,
    staging: *mut u32,
    transform_params: WhirLeafTransformParams,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    coset_index_base: u32,
);

cuda_kernel_declaration!(
    ab_transform_and_hash_whir_leaves_from_ntt_multi_coset_to_staging_kernel(
        src: PtrAndStride<BF>,
        staging: *mut u32,
        transform_params: WhirLeafTransformParams,
        log_trace_len: u32,
        log_lde_factor: u32,
        log_values_per_leaf: u32,
        coset_index_base: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    TransformAndHashWhirLeavesFromNttMultiCosetToStagingRegisterV32,
    src: PtrAndStride<BF>,
    staging: *mut u32,
    transform_params: WhirLeafTransformParams,
    log_trace_len: u32,
    log_lde_factor: u32,
    coset_index_base: u32,
    leaves_count: u32,
);

cuda_kernel_declaration!(
    ab_transform_and_hash_whir_leaves_from_ntt_multi_coset_to_staging_register_v32_kernel(
        src: PtrAndStride<BF>,
        staging: *mut u32,
        transform_params: WhirLeafTransformParams,
        log_trace_len: u32,
        log_lde_factor: u32,
        coset_index_base: u32,
        leaves_count: u32,
    )
);

const NATURAL_REGISTER_RESIDENT_V32_MIN_LEAVES_COUNT: usize = 1 << 16;

fn use_register_resident_natural_v32(log_values_per_leaf: u32, leaves_count: usize) -> bool {
    log_values_per_leaf == 5 && leaves_count >= NATURAL_REGISTER_RESIDENT_V32_MIN_LEAVES_COUNT
}

pub(crate) fn transform_and_hash_whir_leaves_from_ntt_multi_coset_to_staging(
    ntt_output: &DeviceSlice<BF>,
    staging: &mut DeviceSlice<Digest>,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    coset_index_base: u32,
    cosets_in_tile: u32,
    transform_params: WhirLeafTransformParams,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_lde_factor >= 1);
    assert!((1..=5).contains(&log_values_per_leaf));
    assert!(log_trace_len > log_values_per_leaf);
    assert!(cosets_in_tile >= 1);
    assert!(coset_index_base + cosets_in_tile <= 1u32 << log_lde_factor);
    let trace_len = 1usize << log_trace_len;
    let packed_leaf_count = 1usize << (log_trace_len - log_values_per_leaf);
    let leaves_count = packed_leaf_count
        .checked_mul(cosets_in_tile as usize)
        .expect("tile leaf count overflow");
    assert_eq!(staging.len(), leaves_count);
    assert!(leaves_count <= u32::MAX as usize);
    assert!(ntt_output.len() >= trace_len * 4 * cosets_in_tile as usize);

    if use_register_resident_natural_v32(log_values_per_leaf, leaves_count) {
        let config = CudaLaunchConfig::basic(
            (leaves_count as u32).div_ceil(WARP_SIZE),
            (WARP_SIZE, 2u32),
            stream,
        );
        let args = TransformAndHashWhirLeavesFromNttMultiCosetToStagingRegisterV32Arguments::new(
            PtrAndStride::new(ntt_output.as_ptr(), trace_len),
            staging.as_mut_ptr() as *mut u32,
            transform_params,
            log_trace_len,
            log_lde_factor,
            coset_index_base,
            leaves_count as u32,
        );
        return TransformAndHashWhirLeavesFromNttMultiCosetToStagingRegisterV32Function(
            ab_transform_and_hash_whir_leaves_from_ntt_multi_coset_to_staging_register_v32_kernel,
        )
        .launch(&config, &args);
    }

    let values_per_leaf = 1usize << log_values_per_leaf;
    let block_dim_x = if values_per_leaf == 2 {
        (leaves_count as u32).min(4 * WARP_SIZE)
    } else {
        WARP_SIZE
    };
    // The transform uses block-wide barriers, so the x-grid cannot have inactive lanes.
    assert_eq!(leaves_count as u32 % block_dim_x, 0);
    let block_dim_y = (values_per_leaf / 2) as u32;
    let grid_dim_x = leaves_count as u32 / block_dim_x;
    let mut config = CudaLaunchConfig::basic(grid_dim_x, (block_dim_x, block_dim_y), stream);
    config.dynamic_smem_bytes = block_dim_x as usize * values_per_leaf * core::mem::size_of::<E4>()
        + if log_values_per_leaf > 1 {
            block_dim_x as usize * block_dim_y as usize * core::mem::size_of::<BF>()
        } else {
            0
        };
    let args = TransformAndHashWhirLeavesFromNttMultiCosetToStagingArguments::new(
        PtrAndStride::new(ntt_output.as_ptr(), trace_len),
        staging.as_mut_ptr() as *mut u32,
        transform_params,
        log_trace_len,
        log_lde_factor,
        log_values_per_leaf,
        coset_index_base,
    );
    TransformAndHashWhirLeavesFromNttMultiCosetToStagingFunction(
        ab_transform_and_hash_whir_leaves_from_ntt_multi_coset_to_staging_kernel,
    )
    .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    TransformAndHashWhirLeavesFromNttFlatRangeToStaging,
    src: PtrAndStride<BF>,
    staging: *mut u32,
    transform_params: WhirLeafTransformParams,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    flat_leaf_base: u32,
);

cuda_kernel_declaration!(
    ab_transform_and_hash_whir_leaves_from_ntt_flat_range_to_staging_kernel(
        src: PtrAndStride<BF>,
        staging: *mut u32,
        transform_params: WhirLeafTransformParams,
        log_trace_len: u32,
        log_lde_factor: u32,
        log_values_per_leaf: u32,
        flat_leaf_base: u32,
    )
);

pub(crate) fn transform_and_hash_whir_leaves_from_ntt_flat_range_to_staging(
    ntt_output: &DeviceSlice<BF>,
    staging: &mut DeviceSlice<Digest>,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    flat_leaf_base: usize,
    leaves_count: usize,
    transform_params: WhirLeafTransformParams,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_lde_factor >= 1);
    assert!((1..=5).contains(&log_values_per_leaf));
    assert!(log_trace_len > log_values_per_leaf);
    assert_eq!(flat_leaf_base % WARP_SIZE as usize, 0);
    assert!(leaves_count > 0);
    assert_eq!(leaves_count % WARP_SIZE as usize, 0);
    let trace_len = 1usize << log_trace_len;
    let packed_leaf_count = 1usize << (log_trace_len - log_values_per_leaf);
    let total_leaves = packed_leaf_count << log_lde_factor;
    assert!(flat_leaf_base + leaves_count <= total_leaves);
    assert_eq!(staging.len(), leaves_count);
    assert!(ntt_output.len() >= trace_len * 4 * (1usize << log_lde_factor));

    let values_per_leaf = 1usize << log_values_per_leaf;
    let block_dim_x = WARP_SIZE;
    let block_dim_y = (values_per_leaf / 2) as u32;
    // The transform uses block-wide barriers, so the x-grid cannot have inactive lanes.
    let grid_dim_x = leaves_count as u32 / block_dim_x;
    let mut config = CudaLaunchConfig::basic(grid_dim_x, (block_dim_x, block_dim_y), stream);
    config.dynamic_smem_bytes = block_dim_x as usize * values_per_leaf * core::mem::size_of::<E4>()
        + if log_values_per_leaf > 1 {
            block_dim_x as usize * block_dim_y as usize * core::mem::size_of::<BF>()
        } else {
            0
        };
    let args = TransformAndHashWhirLeavesFromNttFlatRangeToStagingArguments::new(
        PtrAndStride::new(ntt_output.as_ptr(), trace_len),
        staging.as_mut_ptr() as *mut u32,
        transform_params,
        log_trace_len,
        log_lde_factor,
        log_values_per_leaf,
        flat_leaf_base as u32,
    );
    TransformAndHashWhirLeavesFromNttFlatRangeToStagingFunction(
        ab_transform_and_hash_whir_leaves_from_ntt_flat_range_to_staging_kernel,
    )
    .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    ReduceStagedWhirSubtreesFlat,
    staged: *const u32,
    boundary_roots: *mut u32,
    roots_count: u32,
);

cuda_kernel_declaration!(
    ab_reduce_staged_whir_subtrees_flat_kernel(
        staged: *const u32,
        boundary_roots: *mut u32,
        roots_count: u32,
    )
);

pub(crate) fn reduce_staged_whir_subtrees_flat(
    staged: &DeviceSlice<Digest>,
    boundary_roots: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const ROOTS_PER_BLOCK: u32 = 16;
    const LEAVES_PER_BLOCK: usize = 512;
    assert!(!staged.is_empty());
    assert_eq!(staged.len() % WARP_SIZE as usize, 0);
    let roots_count = staged.len() / WARP_SIZE as usize;
    assert!(boundary_roots.len() >= roots_count);
    assert!(roots_count <= u32::MAX as usize);
    let mut config = CudaLaunchConfig::basic(
        (roots_count as u32).div_ceil(ROOTS_PER_BLOCK),
        256u32,
        stream,
    );
    config.dynamic_smem_bytes = LEAVES_PER_BLOCK * core::mem::size_of::<Digest>();
    let args = ReduceStagedWhirSubtreesFlatArguments::new(
        staged.as_ptr() as *const u32,
        boundary_roots.as_mut_ptr() as *mut u32,
        roots_count as u32,
    );
    ReduceStagedWhirSubtreesFlatFunction(ab_reduce_staged_whir_subtrees_flat_kernel)
        .launch(&config, &args)
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
  z_stride_ptr: *const E4,
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
            log_count,
        );
        PartiallyEvaluateMonomialFormByRefSmallFunction(
            ab_partially_evaluate_monomial_form_by_ref_small_kernel,
        )
        .launch(&config, &args)?;
        return Ok(count);
    }
    // Each thread Horners its own `gmem_stride`-strided slice of the natural-order
    // coefficients, so its Horner multiplier is `z^gmem_stride` and the grid is
    // exact (`count / VALS_PER_THREAD` is a power of two >= BLOCK_DIM).
    let gmem_stride = count as u32 / VALS_PER_THREAD;
    let z_stride = &mut scratch1[..1];
    pow(&point[..1], gmem_stride, z_stride, stream)?;
    let z_stride_ptr = z_stride.as_ptr();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(BLOCK_DIM, gmem_stride);
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
    Ok(count / 32)
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

/// LSB-binding fold of the (evaluation form, eq) pair. Both legs are read at
/// `2i` / `2i + 1` and written densely at `i` into SEPARATE destinations.
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
    out_array: *mut E4,
    context: &ProverContext,
) -> CudaResult<()> {
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
        out_array,
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
    eq_high_array: *mut E4,
    eq_low_array: *mut E4,
    eq_poly: *mut E4,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(num_queries <= u32::MAX as usize);
    assert!(log_n >= 2);
    assert!(log_n <= 30);
    assert!(acc_size <= u32::MAX as usize);
    let (high_bits, low_bits) = split_eq_bits(log_n);

    // The accumulator serves `gid` bits `low_bits..log_n` from the high slab
    // and bits `0..low_bits` from the low slab, so LSB pairing (coordinate `j`
    // on bit `j`) puts coordinates `low_bits..log_n` on the high slab and
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
        eq_high_array,
        eq_low_array,
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
