use era_cudart::{
    cuda_kernel, cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function,
};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use fft::field_utils::domain_generator_for_size;

pub use crate::ntt_twiddles::OMEGA_LOG_ORDER;
use crate::upstream::Field;
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::device_structures::{
    DeviceMatrix, DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::utils::{
    GetChunksCount, get_grid_block_dims_for_threads_count, WARP_SIZE,
};

/// Number of passes for the multi-stage NTT kernels at a given `log_n`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NttPassCount {
    Two,
    Three,
}

/// Pick 3-pass vs 2-pass based on whether a single column fits in L2.
pub fn ntt_pass_selection(log_n: usize, device_properties: &DeviceProperties) -> NttPassCount {
    let l2_bytes = device_properties.l2_cache_size_bytes;
    let column_bytes = (1usize << log_n) * size_of::<BF>();
    if column_bytes >= l2_bytes && log_n >= 23 {
        NttPassCount::Two
    } else {
        NttPassCount::Three
    }
}

#[cfg(test)]
mod tests;

pub(crate) mod dit;
mod ntt;
mod strategy;
#[allow(dead_code)]
pub use ntt::{
    bitreversed_monomials_to_natural_evals, bitreversed_monomials_to_natural_evals_multi_coset,
    natural_evals_to_bitreversed_monomials,
};
#[cfg(test)]
pub use ntt::{
    evals_to_monomials_2_pass, evals_to_monomials_3_pass, monomials_to_evals_2_pass,
    monomials_to_evals_3_pass,
};
#[allow(dead_code)]
pub use strategy::{
    select_ntt_strategy, NttDirection, NttKernelKind, NttPass, NttStrategy, NttStrategyError,
    MIN_SUPPORTED_LOG_N,
};

mod hypercube;
pub use hypercube::hypercube_x1_msb_evals_to_x1_msb_monomials;
#[cfg(test)]
pub use hypercube::{hypercube_evals_to_monomials_2_pass, hypercube_evals_to_monomials_3_pass};

cuda_kernel!(
    HypercubeStage,
    ab_hypercube_evals_natural_to_bitreversed_coeffs_stage_kernel(
        values: *mut BF,
        log_n: u32,
        stage: u32,
    )
);

cuda_kernel!(
    HypercubeForwardStage,
    ab_hypercube_coeffs_natural_to_natural_evals_stage_kernel(
        values: *mut BF,
        log_n: u32,
        stage: u32,
    )
);

cuda_kernel!(
    CopyScaleBitreversedCoeffs,
    ab_copy_scale_bitreversed_coeffs_kernel(
        src: *const BF,
        dst: *mut BF,
        coset_offset: BF,
        apply_scale: bool,
        log_n: u32,
    )
);

cuda_kernel!(
    BitreversedCoeffsToNaturalNttStage,
    ab_bitreversed_coeffs_to_natural_ntt_stage_kernel(
        values: *mut BF,
        log_n: u32,
        stage: u32,
    )
);

cuda_kernel!(
    NaturalEvalsToBitreversedCoeffsNttStage,
    ab_natural_evals_to_bitreversed_coeffs_ntt_stage_kernel(
        values: *mut BF,
        log_n: u32,
        stage: u32,
    )
);

cuda_kernel!(
    TransposeMonomialsNaive,
    ab_transpose_monomials_naive_kernel(values: *mut BF, log_n: u32,)
);

fn launch_dims(count: usize) -> (era_cudart::execution::Dim3, era_cudart::execution::Dim3) {
    assert!(count <= u32::MAX as usize);
    get_grid_block_dims_for_threads_count(256, count as u32)
}

fn launch_hypercube_stage(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    stage: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let pair_count = 1usize << (log_n - 1);
    let (grid_dim, block_dim) = launch_dims(pair_count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = HypercubeStageArguments::new(values.as_mut_ptr(), log_n as u32, stage as u32);
    HypercubeStageFunction::default().launch(&config, &args)
}

fn launch_hypercube_forward_stage(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    stage: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let pair_count = 1usize << (log_n - 1);
    let (grid_dim, block_dim) = launch_dims(pair_count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = HypercubeForwardStageArguments::new(values.as_mut_ptr(), log_n as u32, stage as u32);
    HypercubeForwardStageFunction::default().launch(&config, &args)
}

fn launch_copy_scale_bitreversed_coeffs(
    src: &DeviceSlice<BF>,
    dst: &mut DeviceSlice<BF>,
    coset_offset: BF,
    apply_scale: bool,
    log_n: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = 1usize << log_n;
    let (grid_dim, block_dim) = launch_dims(count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = CopyScaleBitreversedCoeffsArguments::new(
        src.as_ptr(),
        dst.as_mut_ptr(),
        coset_offset,
        apply_scale,
        log_n as u32,
    );
    CopyScaleBitreversedCoeffsFunction::default().launch(&config, &args)
}

fn launch_bitreversed_coeffs_to_natural_ntt_stage(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    stage: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let pair_count = 1usize << (log_n - 1);
    let (grid_dim, block_dim) = launch_dims(pair_count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = BitreversedCoeffsToNaturalNttStageArguments::new(
        values.as_mut_ptr(),
        log_n as u32,
        stage as u32,
    );
    BitreversedCoeffsToNaturalNttStageFunction::default().launch(&config, &args)
}

fn launch_natural_evals_to_bitreversed_coeffs_ntt_stage(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    stage: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let pair_count = 1usize << (log_n - 1);
    let (grid_dim, block_dim) = launch_dims(pair_count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = NaturalEvalsToBitreversedCoeffsNttStageArguments::new(
        values.as_mut_ptr(),
        log_n as u32,
        stage as u32,
    );
    NaturalEvalsToBitreversedCoeffsNttStageFunction::default().launch(&config, &args)
}

fn launch_transpose_monomials_naive(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    let tile_count = 1usize << (log_n - 10);
    let config = CudaLaunchConfig::basic(tile_count as u32, 32, stream);
    let args = TransposeMonomialsNaiveArguments::new(values.as_mut_ptr(), log_n as u32);
    TransposeMonomialsNaiveFunction::default().launch(&config, &args)
}

pub fn hypercube_evals_natural_to_bitreversed_coeffs(
    src: &DeviceSlice<BF>,
    dst: &mut DeviceSlice<BF>,
    log_n: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_n <= OMEGA_LOG_ORDER as usize);
    assert_eq!(src.len(), 1usize << log_n);
    assert_eq!(dst.len(), src.len());
    memory_copy_async(dst, src, stream)?;
    if log_n == 0 {
        return Ok(());
    }

    // Run the inverse-hypercube butterflies directly on the source slice and land in
    // bitreversed monomial order without any extra permutation pass.
    for stage in (0..log_n).rev() {
        launch_hypercube_stage(dst, log_n, stage, stream)?;
    }
    Ok(())
}

pub fn hypercube_coeffs_to_evals_impl(
    src: &DeviceSlice<BF>,
    dst: &mut DeviceSlice<BF>,
    log_n: usize,
    bitrev: bool,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(src.len(), 1usize << log_n);
    assert_eq!(dst.len(), src.len());
    memory_copy_async(dst, src, stream)?;
    if log_n == 0 {
        return Ok(());
    }

    if bitrev {
        for stage in (0..log_n).rev() {
            launch_hypercube_forward_stage(dst, log_n, stage, stream)?;
        }
    } else {
        for stage in 0..log_n {
            launch_hypercube_forward_stage(dst, log_n, stage, stream)?;
        }
    };

    Ok(())
}

#[allow(dead_code)]
pub fn hypercube_coeffs_natural_to_natural_evals(
    src: &DeviceSlice<BF>,
    dst: &mut DeviceSlice<BF>,
    log_n: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    hypercube_coeffs_to_evals_impl(src, dst, log_n, false, stream)
}

#[allow(dead_code)]
pub fn hypercube_coeffs_bitrev_to_bitrev_evals(
    src: &DeviceSlice<BF>,
    dst: &mut DeviceSlice<BF>,
    log_n: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    hypercube_coeffs_to_evals_impl(src, dst, log_n, true, stream)
}

pub fn natural_evals_to_bitreversed_coeffs(
    src: &DeviceSlice<BF>,
    dst: &mut DeviceSlice<BF>,
    log_n: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_n <= OMEGA_LOG_ORDER as usize);
    assert_eq!(src.len(), 1usize << log_n);
    assert_eq!(dst.len(), src.len());
    memory_copy_async(dst, src, stream)?;
    if log_n == 0 {
        return Ok(());
    }

    for stage in 0..log_n {
        launch_natural_evals_to_bitreversed_coeffs_ntt_stage(dst, log_n, stage, stream)?;
    }
    Ok(())
}

#[allow(dead_code)]
pub fn transpose_monomials_naive(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_n <= OMEGA_LOG_ORDER as usize);
    assert!(log_n >= 10);
    assert_eq!(values.len(), 1usize << log_n);
    launch_transpose_monomials_naive(values, log_n, stream)
}

pub fn bitreversed_coeffs_to_natural_coset(
    src: &DeviceSlice<BF>,
    dst: &mut DeviceSlice<BF>,
    log_n: usize,
    log_lde_factor: usize,
    coset_index: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_n <= OMEGA_LOG_ORDER as usize);
    assert!(log_n + log_lde_factor <= OMEGA_LOG_ORDER as usize);
    assert!(coset_index < (1usize << log_lde_factor));
    assert_eq!(src.len(), 1usize << log_n);
    assert_eq!(dst.len(), src.len());
    if log_n == 0 {
        return memory_copy_async(dst, src, stream);
    }

    let coset_offset = if coset_index == 0 {
        BF::ONE
    } else {
        domain_generator_for_size::<BF>(1u64 << (log_n + log_lde_factor)).pow(coset_index as u32)
    };
    launch_copy_scale_bitreversed_coeffs(src, dst, coset_offset, coset_index != 0, log_n, stream)?;
    for stage in 0..log_n {
        launch_bitreversed_coeffs_to_natural_ntt_stage(dst, log_n, stage, stream)?;
    }
    Ok(())
}

pub const MIN_LOG_N_FOR_MULTISTAGE_KERNELS: usize = 21;

pub fn log_size_supports_transposed_monomials(log_n: usize) -> bool {
    log_n >= MIN_LOG_N_FOR_MULTISTAGE_KERNELS
}

cuda_kernel_signature_arguments_and_function!(
    TransformWhirLeavesFromNttMultiCoset,
    src: PtrAndStride<BF>,
    dst: MutPtrAndStride<BF>,
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
);

cuda_kernel_declaration!(
    ab_transform_whir_leaves_from_ntt_multi_coset_kernel(
        src: PtrAndStride<BF>,
        dst: MutPtrAndStride<BF>,
        log_trace_len: u32,
        log_lde_factor: u32,
        log_values_per_leaf: u32,
    )
);

pub fn transform_whir_leaves_from_ntt_multi_coset(
    src: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    dst: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_lde_factor >= 1);
    assert!(log_values_per_leaf >= 1);
    assert!(log_values_per_leaf <= 5); // Based on block size. Can be relaxed if needed.
    assert!(log_trace_len > log_values_per_leaf);
    let rows = src.rows();
    let cols = src.cols();
    assert!(rows <= u32::MAX as usize);
    assert!(cols <= u32::MAX as usize);
    assert!(dst.rows() <= u32::MAX as usize);
    assert!(dst.cols() <= u32::MAX as usize);
    // A warning to rework kernel for < 32B contiguous accesses if needed:
    assert_eq!(cols, 4);
    assert_eq!(rows, (1 << (log_trace_len + log_lde_factor)) as usize);
    assert_eq!(rows, dst.rows());
    assert_eq!(cols, dst.cols());
    // Each thread reads and writes 2 ext4 values.
    let values_per_leaf = 1 << log_values_per_leaf;
    let block_dim_y = values_per_leaf / 2;
    let block_dim_x = if block_dim_y > 1 {
        WARP_SIZE as usize
    } else {
        assert!(rows >= WARP_SIZE as usize);
        // yields low occupany for small total size corner cases,
        // but such cases are negligible/typically testing-only
        std::cmp::min(rows, 4 * WARP_SIZE as usize)
    };
    assert_eq!(rows % block_dim_x, 0);
    let block_dim = (block_dim_x as u32, block_dim_y as u32);
    let grid_dim = rows.get_chunks_count(block_dim_x);
    let mut config = CudaLaunchConfig::basic(grid_dim as u32, block_dim, stream);
    let smem_bytes = if log_values_per_leaf > 1 {
        2 * block_dim_y * block_dim_x * size_of::<E4>() +
            block_dim_y * block_dim_x * size_of::<BF>()
    } else {
        0
    };
    config.dynamic_smem_bytes = smem_bytes;
    let args = TransformWhirLeavesFromNttMultiCosetArguments::new(
        src.as_ptr_and_stride(),
        dst.as_mut_ptr_and_stride(),
        log_trace_len,
        log_lde_factor,
        log_values_per_leaf,
    );
    TransformWhirLeavesFromNttMultiCosetFunction(
        ab_transform_whir_leaves_from_ntt_multi_coset_kernel,
    ).launch(&config, &args)
}

pub fn transform_whir_leaves_from_ntt_in_place_multi_coset(
    dst: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    log_trace_len: u32,
    log_lde_factor: u32,
    log_values_per_leaf: u32,
    coset_index_base: u32,
    cosets_in_tile: u32,
    src_cols_per_coset: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(src_cols_per_coset, 4);
    // Creates src as alias of dst
    let dst_slice = dst.slice();
    assert_eq!(dst_slice.len(), (src_cols_per_coset << (log_trace_len + log_lde_factor)) as usize);
    let dst_ptr = dst_slice.as_ptr();
    let dst_slice = unsafe { DeviceSlice::from_raw_parts(dst_ptr, dst_slice.len()) };
    let src = DeviceMatrix::new(&dst_slice, 1 << log_trace_len);
    transform_whir_leaves_from_ntt_multi_coset(
        &src,
        dst,
        log_trace_len,
        log_lde_factor,
        log_values_per_leaf,
        stream,
    )
}
