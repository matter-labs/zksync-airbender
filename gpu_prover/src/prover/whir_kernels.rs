use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use crate::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, GetChunksCount, WARP_SIZE};
use field::FieldExtension;

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

pub fn serialize_whir_e4_columns(
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

pub fn deserialize_whir_e4_columns(
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

cuda_kernel_signature_arguments_and_function!(
    AccumulateWhirBaseColumns,
    values: *const BF,
    stride: u32,
    weights: *const E4,
    cols: u32,
    result: *mut E4,
    rows: u32,
);

cuda_kernel_declaration!(
    ab_accumulate_whir_base_columns_e4_kernel(
        values: *const BF,
        stride: u32,
        weights: *const E4,
        cols: u32,
        result: *mut E4,
        rows: u32,
    )
);

pub fn accumulate_whir_base_columns(
    values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    weights: &DeviceSlice<E4>,
    result: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(values.cols(), weights.len());
    assert_eq!(values.rows(), result.len());
    assert!(values.rows() <= u32::MAX as usize);
    assert!(values.cols() <= u32::MAX as usize);
    let rows = values.rows() as u32;
    let cols = values.cols() as u32;
    let (grid_dim, block_dim) = get_launch_dims(rows);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = AccumulateWhirBaseColumnsArguments::new(
        values.as_ptr(),
        values.stride() as u32,
        weights.as_ptr(),
        cols,
        result.as_mut_ptr(),
        rows,
    );
    AccumulateWhirBaseColumnsFunction(ab_accumulate_whir_base_columns_e4_kernel)
        .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    WhirFoldMonomial,
    src: *const E4,
    challenge: *const E4,
    dst: *mut E4,
    half_len: u32,
);

cuda_kernel_declaration!(
    ab_whir_fold_monomial_e4_kernel(
        src: *const E4,
        challenge: *const E4,
        dst: *mut E4,
        half_len: u32,
    )
);

pub fn whir_fold_monomial(
    src: &DeviceSlice<E4>,
    challenge: &DeviceVariable<E4>,
    dst: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(src.len().is_power_of_two());
    assert_eq!(src.len(), dst.len() * 2);
    assert!(dst.len() <= u32::MAX as usize);
    let half_len = dst.len() as u32;
    let (grid_dim, block_dim) = get_launch_dims(half_len);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirFoldMonomialArguments::new(
        src.as_ptr(),
        challenge.as_ptr(),
        dst.as_mut_ptr(),
        half_len,
    );
    WhirFoldMonomialFunction(ab_whir_fold_monomial_e4_kernel).launch(&config, &args)
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

pub fn whir_fold_split_half_in_place(
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
    log_values_per_leaf: u32,
    dst_rows_per_slot: u32,
    row_stride: u32,
    row_offset: u32,
    src_cols: u32,
);

cuda_kernel_declaration!(
    ab_pack_rows_for_whir_leaves_bf_kernel(
        src: PtrAndStride<BF>,
        dst: MutPtrAndStride<BF>,
        log_values_per_leaf: u32,
        dst_rows_per_slot: u32,
        row_stride: u32,
        row_offset: u32,
        src_cols: u32,
    )
);

pub fn pack_rows_for_whir_leaves(
    src: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    dst: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_values_per_leaf: u32,
    row_stride: u32,
    row_offset: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let src_rows = src.rows();
    let src_cols = src.cols();
    let dst_rows = dst.rows();
    let dst_cols = dst.cols();
    let dst_rows_per_slot = src_rows >> log_values_per_leaf;
    assert_eq!(dst_rows_per_slot * row_stride as usize, dst_rows);
    assert!(row_offset < row_stride);
    assert_eq!(src_cols << log_values_per_leaf, dst_cols);
    assert!(dst_rows_per_slot <= u32::MAX as usize);
    assert!(src_cols <= u32::MAX as usize);
    assert!(dst_cols <= u32::MAX as usize);
    let block_dim = (WARP_SIZE, 4);
    let grid_dim = (
        dst_rows_per_slot.get_chunks_count(WARP_SIZE as usize) as u32,
        dst_cols.get_chunks_count(4) as u32,
    );
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = PackRowsForWhirLeavesArguments::new(
        src.as_ptr_and_stride(),
        dst.as_mut_ptr_and_stride(),
        log_values_per_leaf,
        dst_rows_per_slot as u32,
        row_stride,
        row_offset,
        src_cols as u32,
    );
    PackRowsForWhirLeavesFunction(ab_pack_rows_for_whir_leaves_bf_kernel).launch(&config, &args)
}
