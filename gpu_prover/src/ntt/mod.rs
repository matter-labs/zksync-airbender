use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use fft::field_utils::domain_generator_for_size;
use field::Field;

use crate::primitives::device_context::OMEGA_LOG_ORDER;
use crate::primitives::field::BF;
use crate::primitives::utils::get_grid_block_dims_for_threads_count;

#[cfg(test)]
mod tests;

cuda_kernel!(
    HypercubeStage,
    ab_hypercube_evals_natural_to_bitreversed_coeffs_stage_kernel(
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

pub(crate) fn hypercube_evals_natural_to_bitreversed_coeffs(
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

    // Match the CPU setup convention: run the inverse-hypercube butterflies directly on the
    // source slice and land in bitreversed monomial order without any extra permutation pass.
    for stage in (0..log_n).rev() {
        launch_hypercube_stage(dst, log_n, stage, stream)?;
    }
    Ok(())
}

pub(crate) fn bitreversed_coeffs_to_natural_coset(
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
