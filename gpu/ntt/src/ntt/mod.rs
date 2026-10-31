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
    coset_to_monomials_in_place, hypercube_to_coset_in_place, log_size_supports_in_place,
    monomials_to_coset_in_place, monomials_to_hypercube_in_place,
};
mod kernels;
mod lde;
mod retained_monomials;
pub use retained_monomials::{
    hypercube_to_retained_monomials_and_coset, hypercube_to_retained_monomials_and_coset_in_place,
    log_size_supports_retained_monomials, retained_monomials_to_coset,
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

/// A base commitment must fit both the generated transforms and the field's
/// root domain. This validation does not initialize CUDA or allocate tables.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BaseCommitmentTransformError {
    UnsupportedMessageSize { requested: u32, min: u32, max: u32 },
    LogSizeOverflow { message_log2: u32, lde_log2: u32 },
    LdeDomainTooLarge { requested: u32, max: u32 },
}

impl std::fmt::Display for BaseCommitmentTransformError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::UnsupportedMessageSize { requested, min, max } => write!(
                f,
                "base commitment message log2 {requested} is outside the GPU transform range {min}..={max}"
            ),
            Self::LogSizeOverflow { message_log2, lde_log2 } => write!(
                f,
                "base commitment LDE log2 overflows: message {message_log2} + LDE {lde_log2}"
            ),
            Self::LdeDomainTooLarge { requested, max } => write!(
                f,
                "base commitment LDE domain log2 {requested} exceeds BabyBear root-order limit {max}"
            ),
        }
    }
}

impl std::error::Error for BaseCommitmentTransformError {}

/// Validates the Mobius and natural-coefficient to bit-reversed LDE path used
/// by base commitments. The smaller legacy MSB-convention path is excluded.
pub fn validate_base_commitment_transform_shape(
    message_log2: u32,
    lde_log2: u32,
) -> Result<(), BaseCommitmentTransformError> {
    // The generated Mobius final pass and the finest twiddle arrays share this
    // upper bound. Widening the LDE selector alone must not widen admission.
    let max =
        strategy::NATURAL_TO_BITREV_MAX_LOG_N.min(crate::ntt_twiddles::LOG_MAX_NTT_SIZE) as u32;
    if !log_size_supports_natural_to_bitrev_lde(message_log2 as usize) || message_log2 > max {
        return Err(BaseCommitmentTransformError::UnsupportedMessageSize {
            requested: message_log2,
            min: MIN_LOG_N_FOR_NATURAL_TO_BITREV_LDE as u32,
            max,
        });
    }
    let domain_log2 = message_log2.checked_add(lde_log2).ok_or(
        BaseCommitmentTransformError::LogSizeOverflow {
            message_log2,
            lde_log2,
        },
    )?;
    if domain_log2 > OMEGA_LOG_ORDER {
        return Err(BaseCommitmentTransformError::LdeDomainTooLarge {
            requested: domain_log2,
            max: OMEGA_LOG_ORDER,
        });
    }
    Ok(())
}

#[cfg(test)]
mod cpu_base_commitment_transform_tests {
    use super::*;

    #[test]
    fn supported_domains_include_compact_and_production_shapes() {
        for message in 13..=24 {
            for lde in 0..=27 - message {
                assert_eq!(
                    validate_base_commitment_transform_shape(message, lde),
                    Ok(())
                );
            }
        }
        // Blake 20/4 and unified 23/1 both commit a log-24 message with LDE 2.
        assert_eq!(validate_base_commitment_transform_shape(24, 1), Ok(()));
    }

    #[test]
    fn rejects_legacy_and_above_range_messages() {
        for requested in [0, 12, 25, u32::MAX] {
            assert_eq!(
                validate_base_commitment_transform_shape(requested, 0),
                Err(BaseCommitmentTransformError::UnsupportedMessageSize {
                    requested,
                    min: 13,
                    max: 24,
                })
            );
        }
    }

    #[test]
    fn rejects_field_domain_even_when_message_transform_fits() {
        assert_eq!(
            validate_base_commitment_transform_shape(24, 4),
            Err(BaseCommitmentTransformError::LdeDomainTooLarge {
                requested: 28,
                max: 27
            })
        );
    }

    #[test]
    fn rejects_log_addition_overflow() {
        assert_eq!(
            validate_base_commitment_transform_shape(24, u32::MAX),
            Err(BaseCommitmentTransformError::LogSizeOverflow {
                message_log2: 24,
                lde_log2: u32::MAX,
            })
        );
    }
}
