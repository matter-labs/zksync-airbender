use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart::{
    cuda_kernel, cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function,
};

use crate::ops::simple::pow;
use crate::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use crate::upstream::FieldExtension;

use std::mem::size_of;

fn get_launch_dims(count: u32) -> (Dim3, Dim3) {
    get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count)
}

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
    let (grid_dim, block_dim) = get_launch_dims(count);
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
    let (grid_dim, block_dim) = get_launch_dims(count);
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
    let (grid_dim, block_dim) = get_launch_dims(rows);
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
    let (grid_dim, block_dim) = get_launch_dims(half_len as u32);
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
    let (grid_dim, block_dim) = get_launch_dims(half_len);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirFoldSplitHalfArguments::new(values.as_mut_ptr(), challenge.as_ptr(), half_len);
    WhirFoldSplitHalfFunction(ab_whir_fold_split_half_e4_kernel).launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    PackRowsForWhirLeaves,
    src: PtrAndStride<BF>,
    dst: MutPtrAndStride<BF>,
    log_trace_len: u32,
    log_blocks_per_coset: u32,
    log_values_per_leaf: u32,
    dst_rows_per_coset: u32,
);

cuda_kernel_declaration!(
    ab_pack_rows_for_whir_leaves_bf_kernel(
        src: PtrAndStride<BF>,
        dst: MutPtrAndStride<BF>,
        log_trace_len: u32,
        log_blocks_per_coset: u32,
        log_values_per_leaf: u32,
        dst_rows_per_coset: u32,
    )
);

pub(crate) fn pack_rows_for_whir_leaves(
    src: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    dst: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_lde_factor >= 1);
    assert!(log_values_per_leaf >= 1);
    assert!(log_values_per_leaf <= 5); // Based on max block size. Can be relaxed if needed.
    let src_rows = src.rows();
    let src_cols = src.cols();
    let dst_rows = dst.rows();
    let dst_cols = dst.cols();
    assert!(src_rows <= u32::MAX as usize);
    assert!(src_cols <= u32::MAX as usize);
    assert!(dst_rows <= u32::MAX as usize);
    assert!(dst_cols <= u32::MAX as usize);
    assert_eq!(src_cols, 4);
    assert_eq!(src_rows, (1 << (log_trace_len + log_lde_factor)) as usize);
    assert_eq!(src_rows >> log_values_per_leaf, dst_rows);
    assert_eq!(src_cols << log_values_per_leaf, dst_cols);
    // Each thread reads and writes 2 ext4 values.
    let warps_per_block = dst_cols / 8;
    let block_dim = (WARP_SIZE, warps_per_block as u32);
    assert!(log_trace_len > log_values_per_leaf);
    let log_dst_rows_per_coset = log_trace_len - log_values_per_leaf;
    let log_blocks_per_coset = if log_dst_rows_per_coset > 5 {
        log_dst_rows_per_coset - 5
    } else {
        0
    };
    let dst_rows_per_coset = 1 << log_dst_rows_per_coset;
    assert_eq!(dst_rows_per_coset, dst_rows >> log_lde_factor);
    let grid_dim = 1 << (log_blocks_per_coset + log_lde_factor);
    let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let smem_bytes = warps_per_block * WARP_SIZE as usize * size_of::<E4>();
    config.dynamic_smem_bytes = smem_bytes;
    let args = PackRowsForWhirLeavesArguments::new(
        src.as_ptr_and_stride(),
        dst.as_mut_ptr_and_stride(),
        log_trace_len,
        log_blocks_per_coset,
        log_values_per_leaf,
        dst_rows_per_coset as u32,
    );
    PackRowsForWhirLeavesFunction(ab_pack_rows_for_whir_leaves_bf_kernel).launch(&config, &args)
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

#[cfg(test)]
mod tests;
