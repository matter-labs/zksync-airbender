//! CUDA kernel signature declarations, kernel-set traits, and launch helpers
//! for the compact backward main-layer path (round 0, round 1, round 2,
//! and rounds ≥ 3 continuation).

use std::ffi::c_void;
use std::ptr::null_mut;
use std::sync::OnceLock;

use era_cudart::cuda_kernel_declaration;
use era_cudart::execution::KernelFunction;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart_sys::cudaGetSymbolAddress;

use super::super::kernels::gkr_dim_reducing_launch_config;
use super::super::kernels::GkrEqLayoutCompact;
use super::cont_descs::GpuFlatContinuationUnifiedDesc;
use super::cont_descs::{GpuFlatRound1UnifiedDesc, GpuFlatRound2UnifiedDesc};
use super::kernel_limits::MAX_MAIN_LAYER_CLAIM_POINT_LEN;
use super::round0_desc::GpuFlatRound0StaticDesc;
use crate::primitives::context::ProverContext;
use crate::primitives::field::E4;

// ---------------------------------------------------------------------------
// Round 0 (compact) — non-constant variant
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound0FlatCompact<T>,
    static_desc: GpuFlatRound0StaticDesc,
    coefficients: *const T,
    eq_high_groups: *const T,
    eq_low_buffer: *const T,
    eq_layout: GkrEqLayoutCompact,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round0_flat_compact_e4_kernel(
        static_desc: GpuFlatRound0StaticDesc,
        coefficients: *const E4,
        eq_high_groups: *const E4,
        eq_low_buffer: *const E4,
        eq_layout: GkrEqLayoutCompact,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) fn launch_main_round0<E: crate::prover::gkr::GpuKernels>(
    static_desc: &GpuFlatRound0StaticDesc,
    coefficients: *const E,
    eq_high_groups: *const E,
    eq_low_buffer: *const E,
    eq_layout: &GkrEqLayoutCompact,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    let args = GpuGKRMainRound0FlatCompactArguments::new(
        *static_desc,
        coefficients,
        eq_high_groups,
        eq_low_buffer,
        *eq_layout,
        contributions,
        acc_size,
    );
    GpuGKRMainRound0FlatCompactFunction(E::MAIN_ROUND0_FLAT_COMPACT).launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Round 0 (compact) — constant variant
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound0FlatConstantCompact<T>,
    static_desc: GpuFlatRound0StaticDesc,
    eq_high_groups: *const T,
    eq_low_buffer: *const T,
    eq_layout: GkrEqLayoutCompact,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round0_flat_constant_compact_e4_kernel(
        static_desc: GpuFlatRound0StaticDesc,
        eq_high_groups: *const E4,
        eq_low_buffer: *const E4,
        eq_layout: GkrEqLayoutCompact,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) fn launch_main_round0_constant<E: crate::prover::gkr::GpuKernels>(
    static_desc: &GpuFlatRound0StaticDesc,
    eq_high_groups: *const E,
    eq_low_buffer: *const E,
    eq_layout: &GkrEqLayoutCompact,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    let args = GpuGKRMainRound0FlatConstantCompactArguments::new(
        *static_desc,
        eq_high_groups,
        eq_low_buffer,
        *eq_layout,
        contributions,
        acc_size,
    );
    GpuGKRMainRound0FlatConstantCompactFunction(E::MAIN_ROUND0_FLAT_CONSTANT_COMPACT)
        .launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Main-layer constants and __constant__ symbol addresses
// ---------------------------------------------------------------------------

extern "C" {
    static ab_gkr_round2_challenges: [E4; 3];
    static ab_gkr_main_layer_claim_point: [E4; MAX_MAIN_LAYER_CLAIM_POINT_LEN];
}

pub(crate) fn get_main_layer_claim_point_device_ptr() -> *mut E4 {
    static PTR: OnceLock<usize> = OnceLock::new();
    let ptr = *PTR.get_or_init(|| {
        let mut p: *mut c_void = null_mut();
        // SAFETY: ab_gkr_main_layer_claim_point is a valid __constant__ symbol
        // defined in backward/round1_flat_warp_split.cu.
        unsafe {
            cudaGetSymbolAddress(
                &mut p,
                &ab_gkr_main_layer_claim_point as *const _ as *const c_void,
            )
        }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_main_layer_claim_point");
        p as usize
    });
    ptr as *mut E4
}

fn get_round2_challenges_device_ptr() -> *mut E4 {
    static PTR: OnceLock<usize> = OnceLock::new();
    let ptr = *PTR.get_or_init(|| {
        let mut p: *mut c_void = null_mut();
        // SAFETY: ab_gkr_round2_challenges is a valid __constant__ e4[3]
        // symbol defined in backward/round2_flat_warp_split.cu.
        unsafe {
            cudaGetSymbolAddress(
                &mut p,
                &ab_gkr_round2_challenges as *const _ as *const c_void,
            )
        }
        .wrap()
        .expect("cudaGetSymbolAddress failed for ab_gkr_round2_challenges");
        p as usize
    });
    ptr as *mut E4
}

// ---------------------------------------------------------------------------
// Round 3+ (continuation) compact kernel declarations + launcher
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound3FlatConstantUnifiedCompact<T>,
    desc: GpuFlatContinuationUnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    eq_high_groups: *const T,
    eq_low_buffer: *const T,
    eq_layout: GkrEqLayoutCompact,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel(
        desc: GpuFlatContinuationUnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        eq_high_groups: *const E4,
        eq_low_buffer: *const E4,
        eq_layout: GkrEqLayoutCompact,
        contributions: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel(
        desc: GpuFlatContinuationUnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        eq_high_groups: *const E4,
        eq_low_buffer: *const E4,
        eq_layout: GkrEqLayoutCompact,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) fn launch_main_round3_unified<E: crate::prover::gkr::GpuKernels>(
    desc: &GpuFlatContinuationUnifiedDesc,
    _folding_challenge: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    eq_high_groups: *const E,
    eq_low_buffer: *const E,
    eq_layout: &GkrEqLayoutCompact,
    contributions: *mut E,
    acc_size: u32,
    explicit_form: bool,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let stream = context.get_exec_stream();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound3FlatConstantUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        folding_challenge_slot,
        eq_high_groups,
        eq_low_buffer,
        *eq_layout,
        contributions,
        acc_size,
    );
    let kernel = if explicit_form {
        E::MAIN_ROUND3_FLAT_CONSTANT_EXPLICIT_UNIFIED_COMPACT
    } else {
        E::MAIN_ROUND3_FLAT_CONSTANT_UNIFIED_COMPACT
    };
    GpuGKRMainRound3FlatConstantUnifiedCompactFunction(kernel).launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Round 1 compact kernel declaration + launcher
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound1FlatConstantCompactUnifiedCompact<T>,
    desc: GpuFlatRound1UnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    eq_high_groups: *const T,
    eq_low_buffer: *const T,
    eq_layout: GkrEqLayoutCompact,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel(
        desc: GpuFlatRound1UnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        eq_high_groups: *const E4,
        eq_low_buffer: *const E4,
        eq_layout: GkrEqLayoutCompact,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) fn launch_main_round1_unified<E: crate::prover::gkr::GpuKernels>(
    desc: &GpuFlatRound1UnifiedDesc,
    _folding_challenge: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    eq_high_groups: *const E,
    eq_low_buffer: *const E,
    eq_layout: &GkrEqLayoutCompact,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let stream = context.get_exec_stream();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound1FlatConstantCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        eq_high_groups,
        eq_low_buffer,
        *eq_layout,
        contributions,
        acc_size,
    );
    GpuGKRMainRound1FlatConstantCompactUnifiedCompactFunction(
        E::MAIN_ROUND1_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT,
    )
    .launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Round 2 compact kernel declaration + launcher
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRRound2ChallengesPrelude<T>,
    folding_challenges: *const T,
    staging: *mut T,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_round2_challenges_prelude(
        folding_challenges: *const E4,
        staging: *mut E4,
    )
);

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound2FlatConstantCompactUnifiedCompact<T>,
    desc: GpuFlatRound2UnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    eq_high_groups: *const T,
    eq_low_buffer: *const T,
    eq_layout: GkrEqLayoutCompact,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel(
        desc: GpuFlatRound2UnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        eq_high_groups: *const E4,
        eq_low_buffer: *const E4,
        eq_layout: GkrEqLayoutCompact,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) fn launch_main_round2_unified<E: crate::prover::gkr::GpuKernels>(
    desc: &GpuFlatRound2UnifiedDesc,
    folding_challenges: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    eq_high_groups: *const E,
    eq_low_buffer: *const E,
    eq_layout: &GkrEqLayoutCompact,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let stream = context.get_exec_stream();
    let prelude_config = CudaLaunchConfig::basic(1, 1, stream);
    let prelude_args = GpuGKRRound2ChallengesPreludeArguments::new(
        folding_challenges,
        get_round2_challenges_device_ptr() as *mut E,
    );
    GpuGKRRound2ChallengesPreludeFunction(E::ROUND2_CHALLENGES_PRELUDE)
        .launch(&prelude_config, &prelude_args)?;

    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound2FlatConstantCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        eq_high_groups,
        eq_low_buffer,
        *eq_layout,
        contributions,
        acc_size,
    );
    GpuGKRMainRound2FlatConstantCompactUnifiedCompactFunction(
        E::MAIN_ROUND2_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT,
    )
    .launch(&config, &args)
}
