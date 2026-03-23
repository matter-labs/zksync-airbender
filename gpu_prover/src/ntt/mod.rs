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

mod ntt;
#[allow(unused)]
pub use ntt::{bitreversed_monomials_to_natural_evals, natural_evals_to_bitreversed_monomials};
#[cfg(test)]
pub(crate) use ntt::{
    evals_to_monomials_2_pass, evals_to_monomials_3_pass, monomials_to_evals_2_pass,
    monomials_to_evals_3_pass,
};

mod hypercube;
pub use hypercube::hypercube_natural_evals_to_bitreversed_monomials;
#[cfg(test)]
pub(crate) use hypercube::{
    hypercube_evals_to_monomials_2_pass, hypercube_evals_to_monomials_3_pass,
};

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

    // Run the inverse-hypercube butterflies directly on the source slice and land in
    // bitreversed monomial order without any extra permutation pass.
    for stage in (0..log_n).rev() {
        launch_hypercube_stage(dst, log_n, stage, stream)?;
    }
    Ok(())
}

pub(crate) fn hypercube_coeffs_natural_to_natural_evals(
    src: &DeviceSlice<BF>,
    dst: &mut DeviceSlice<BF>,
    log_n: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(src.len(), 1usize << log_n);
    assert_eq!(dst.len(), src.len());
    memory_copy_async(dst, src, stream)?;
    if log_n == 0 {
        return Ok(());
    }

    for stage in 0..log_n {
        launch_hypercube_forward_stage(dst, log_n, stage, stream)?;
    }
    Ok(())
}

pub(crate) fn natural_evals_to_bitreversed_coeffs(
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

#[allow(unused)]
pub(crate) fn transpose_monomials_naive(
    values: &mut DeviceSlice<BF>,
    log_n: usize,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_n <= OMEGA_LOG_ORDER as usize);
    assert!(log_n >= 10);
    assert_eq!(values.len(), 1usize << log_n);
    launch_transpose_monomials_naive(values, log_n, stream)
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

pub(crate) const MIN_LOG_N_FOR_MULTISTAGE_KERNELS: usize = 21;

pub fn log_size_supports_transposed_monomials(log_n: usize) -> bool {
    log_n >= MIN_LOG_N_FOR_MULTISTAGE_KERNELS
}
