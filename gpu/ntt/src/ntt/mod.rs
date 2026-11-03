use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

pub use crate::ntt_twiddles::OMEGA_LOG_ORDER;
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::get_grid_block_dims_for_threads_count;

/// Number of passes for the multi-stage NTT kernels at a given `log_n`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NttPassCount {
    Two,
    Three,
}

/// Pick 3-pass vs 2-pass based on whether a single column fits in L2.
pub(crate) fn ntt_pass_selection(
    log_n: usize,
    device_properties: &DeviceProperties,
) -> NttPassCount {
    let l2_bytes = device_properties.l2_cache_size_bytes;
    let column_bytes = (1usize << log_n) * size_of::<BF>();
    if column_bytes >= l2_bytes && log_n >= 23 {
        NttPassCount::Two
    } else {
        NttPassCount::Three
    }
}

pub(crate) fn hypercube_three_pass(log_n: usize, properties: &DeviceProperties) -> bool {
    log_n != 20 && ntt_pass_selection(log_n, properties) == NttPassCount::Three
}

#[cfg(test)]
mod tests;

mod dispatch;
pub(crate) mod dit;
mod forward;
mod in_place;
mod inverse;
pub use in_place::{
    coset_to_monomials_in_place, hypercube_to_coset_in_place, monomials_to_coset_in_place,
    monomials_to_hypercube_in_place,
};
mod kernels;
mod lde;
mod retained_monomials;
pub use retained_monomials::{
    hypercube_to_retained_monomials_and_coset, hypercube_to_retained_monomials_and_coset_in_place,
    retained_monomials_to_coset,
};
mod shared;
mod strategy;
pub use dispatch::natural_evals_to_bitreversed_monomials;
#[cfg(test)]
pub(crate) use forward::{monomials_to_evals_2_pass_smem, monomials_to_evals_3_pass};
#[cfg(test)]
pub(crate) use inverse::{evals_to_monomials_2_pass, evals_to_monomials_3_pass};
pub use lde::{
    bitreversed_monomials_to_natural_evals_multi_coset,
    hypercube_to_bitreversed_multi_coset_evals_fused_log_n_20,
    hypercube_to_multi_coset_bitrev_evals_fused, hypercube_to_multi_coset_evals_fused,
    lde_with_coset_range, natural_monomials_to_bitreversed_evals_coset_range,
    natural_monomials_to_bitreversed_evals_multi_coset, MAX_LOG_N_FOR_SINGLE_KERNEL_LDE,
};
pub(crate) use strategy::{select_ntt_strategy, NttDirection, NttKernelKind, NttStrategy};

mod hypercube;
pub use hypercube::hypercube_evals_to_monomials;
#[cfg(test)]
pub(crate) use hypercube::{
    hypercube_evals_to_monomials_2_pass, hypercube_evals_to_monomials_3_pass,
};

cuda_kernel!(
    HypercubeStage,
    ab_hypercube_evals_to_monomial_coeffs_stage_kernel(
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
    NaturalEvalsToBitreversedCoeffsNttStage,
    ab_natural_evals_to_bitreversed_coeffs_ntt_stage_kernel(
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

/// Multilinear hypercube evaluations -> multilinear monomial coefficients, one
/// butterfly stage per variable. This is the Mobius transform, and Mobius
/// commutes with bit-reversal (`P*M*P == M`: every stage applies the same 2x2
/// matrix to a distinct index bit, so conjugating by `P` only permutes the
/// tensor factors). It therefore PRESERVES whatever labeling its input had —
/// no name here can decide the labeling question, only measuring the array can.
pub(crate) fn hypercube_evals_to_monomial_coeffs(
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

    for stage in (0..log_n).rev() {
        launch_hypercube_stage(dst, log_n, stage, stream)?;
    }
    Ok(())
}

/// Multilinear monomial coefficients -> multilinear hypercube evaluations, one
/// butterfly stage per variable. This is the inverse of
/// [`hypercube_evals_to_monomial_coeffs`]. Preserves its input's labeling
/// (Mobius commutes with bit-reversal), and there is no labeling-changing
/// variant of it to select — which is why it takes no stage-order or
/// bitreversal flag.
pub fn hypercube_coeffs_to_evals(
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

pub const MIN_LOG_N_FOR_MULTISTAGE_KERNELS: usize = 21;

pub fn log_size_supports_transposed_monomials(log_n: usize) -> bool {
    log_n >= MIN_LOG_N_FOR_MULTISTAGE_KERNELS
}

/// Smallest `log_n` [`natural_monomials_to_bitreversed_evals_multi_coset`] has a
/// dispatch family for.
pub const MIN_LOG_N_FOR_NATURAL_TO_BITREV_LDE: usize = strategy::TWO_PASS_COMPACT_MIN_LOG_N;

/// `true` when [`natural_monomials_to_bitreversed_evals_multi_coset`] has a
/// dispatch family for `log_n` (it panics outside its range).
pub fn log_size_supports_natural_to_bitrev_lde(log_n: usize) -> bool {
    (MIN_LOG_N_FOR_NATURAL_TO_BITREV_LDE..=strategy::NATURAL_TO_BITREV_MAX_LOG_N).contains(&log_n)
}
