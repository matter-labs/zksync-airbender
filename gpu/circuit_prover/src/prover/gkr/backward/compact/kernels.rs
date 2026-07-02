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
use super::super::kernels::GkrEqSizes;
use super::cont_descs::GpuFlatContinuationUnifiedDesc;
use super::cont_descs::{GpuFlatRound1UnifiedDesc, GpuFlatRound2UnifiedDesc};
use super::cont_descs::{
    GpuFlatContinuationUnifiedDescDevptr, GpuFlatRound1UnifiedDescDevptr,
    GpuFlatRound2UnifiedDescDevptr, GpuFlatTermTables,
};
use super::kernel_limits::MAX_MAIN_LAYER_CLAIM_POINT_LEN;
use super::round0_desc::GpuFlatRound0StaticDesc;
use crate::primitives::field::E4;
use crate::prover::ProverContext;

// ---------------------------------------------------------------------------
// Round 0 (compact) — non-constant variant
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound0FlatCompact<T>,
    static_desc: GpuFlatRound0StaticDesc,
    coefficients: *const T,
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round0_flat_compact_e4_kernel(
        static_desc: GpuFlatRound0StaticDesc,
        coefficients: *const E4,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) fn launch_main_round0<E: crate::prover::gkr::BackwardKernels>(
    static_desc: &GpuFlatRound0StaticDesc,
    coefficients: *const E,
    eq_low: *const E,
    eq_sizes: &GkrEqSizes,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    let args = GpuGKRMainRound0FlatCompactArguments::new(
        *static_desc,
        coefficients,
        eq_low,
        *eq_sizes,
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
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round0_flat_constant_compact_e4_kernel(
        static_desc: GpuFlatRound0StaticDesc,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) fn launch_main_round0_constant<E: crate::prover::gkr::BackwardKernels>(
    static_desc: &GpuFlatRound0StaticDesc,
    eq_low: *const E,
    eq_sizes: &GkrEqSizes,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size, context);
    let args = GpuGKRMainRound0FlatConstantCompactArguments::new(
        *static_desc,
        eq_low,
        *eq_sizes,
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

pub(crate) fn get_round2_challenges_device_ptr() -> *mut E4 {
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
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel(
        desc: GpuFlatContinuationUnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
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
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) fn launch_main_round3_unified<E: crate::prover::gkr::BackwardKernels>(
    desc: &GpuFlatContinuationUnifiedDesc,
    _folding_challenge: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    eq_low: *const E,
    eq_sizes: &GkrEqSizes,
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
        eq_low,
        *eq_sizes,
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
// Round 3+ (continuation) compact kernel declarations + launcher —
// device-pointer coeff variant
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound3FlatDevptrUnifiedCompact<T>,
    desc: GpuFlatContinuationUnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    coefficients: *const T,
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round3_flat_devptr_unified_compact_e4_kernel(
        desc: GpuFlatContinuationUnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        coefficients: *const E4,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round3_flat_devptr_explicit_unified_compact_e4_kernel(
        desc: GpuFlatContinuationUnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        coefficients: *const E4,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round3_unified_devptr<E: crate::prover::gkr::BackwardKernels>(
    desc: &GpuFlatContinuationUnifiedDesc,
    _folding_challenge: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    coefficients: *const E,
    eq_low: *const E,
    eq_sizes: &GkrEqSizes,
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
    let args = GpuGKRMainRound3FlatDevptrUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        folding_challenge_slot,
        coefficients,
        eq_low,
        *eq_sizes,
        contributions,
        acc_size,
    );
    let kernel = if explicit_form {
        E::MAIN_ROUND3_FLAT_DEVPTR_EXPLICIT_UNIFIED_COMPACT
    } else {
        E::MAIN_ROUND3_FLAT_DEVPTR_UNIFIED_COMPACT
    };
    GpuGKRMainRound3FlatDevptrUnifiedCompactFunction(kernel).launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Round 1 compact kernel declaration + launcher
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound1FlatConstantCompactUnifiedCompact<T>,
    desc: GpuFlatRound1UnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel(
        desc: GpuFlatRound1UnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

pub(crate) fn launch_main_round1_unified<E: crate::prover::gkr::BackwardKernels>(
    desc: &GpuFlatRound1UnifiedDesc,
    _folding_challenge: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    eq_low: *const E,
    eq_sizes: &GkrEqSizes,
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
        eq_low,
        *eq_sizes,
        contributions,
        acc_size,
    );
    GpuGKRMainRound1FlatConstantCompactUnifiedCompactFunction(
        E::MAIN_ROUND1_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT,
    )
    .launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Round 1 compact kernel declaration + launcher — device-pointer coeff variant
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound1FlatDevptrCompactUnifiedCompact<T>,
    desc: GpuFlatRound1UnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const T,
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round1_flat_devptr_compact_unified_compact_e4_kernel(
        desc: GpuFlatRound1UnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        coefficients: *const E4,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round1_unified_devptr<E: crate::prover::gkr::BackwardKernels>(
    desc: &GpuFlatRound1UnifiedDesc,
    _folding_challenge: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const E,
    eq_low: *const E,
    eq_sizes: &GkrEqSizes,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let stream = context.get_exec_stream();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound1FlatDevptrCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        coefficients,
        eq_low,
        *eq_sizes,
        contributions,
        acc_size,
    );
    GpuGKRMainRound1FlatDevptrCompactUnifiedCompactFunction(
        E::MAIN_ROUND1_FLAT_DEVPTR_COMPACT_UNIFIED_COMPACT,
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
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel(
        desc: GpuFlatRound2UnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

/// Stage the three round-2 folding challenges into the
/// `ab_gkr_round2_challenges` `__constant__` symbol. Every round-2 kernel
/// (unfused or warp-partial) depends on this prelude having run on the
/// same `exec_stream` immediately before its launch — round 2's lazy
/// base-fold reads three values from that symbol.
pub(crate) fn launch_round2_challenges_prelude<E: crate::prover::gkr::BackwardKernels>(
    folding_challenges: *const E,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let prelude_config = CudaLaunchConfig::basic(1, 1, context.get_exec_stream());
    let prelude_args = GpuGKRRound2ChallengesPreludeArguments::new(
        folding_challenges,
        get_round2_challenges_device_ptr() as *mut E,
    );
    GpuGKRRound2ChallengesPreludeFunction(E::ROUND2_CHALLENGES_PRELUDE)
        .launch(&prelude_config, &prelude_args)
}

pub(crate) fn launch_main_round2_unified<E: crate::prover::gkr::BackwardKernels>(
    desc: &GpuFlatRound2UnifiedDesc,
    folding_challenges: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    eq_low: *const E,
    eq_sizes: &GkrEqSizes,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let stream = context.get_exec_stream();
    launch_round2_challenges_prelude::<E>(folding_challenges, context)?;

    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound2FlatConstantCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        eq_low,
        *eq_sizes,
        contributions,
        acc_size,
    );
    GpuGKRMainRound2FlatConstantCompactUnifiedCompactFunction(
        E::MAIN_ROUND2_FLAT_CONSTANT_COMPACT_UNIFIED_COMPACT,
    )
    .launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Round 2 compact kernel declaration + launcher — device-pointer coeff variant
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound2FlatDevptrCompactUnifiedCompact<T>,
    desc: GpuFlatRound2UnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const T,
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round2_flat_devptr_compact_unified_compact_e4_kernel(
        desc: GpuFlatRound2UnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        coefficients: *const E4,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

/// Device-pointer coeff variant of `launch_main_round2_unified`. Schedules the
/// `ab_gkr_round2_challenges_prelude` before the round-2 kernel, matching the
/// constant launcher — round 2's lazy base-fold reads three values from the
/// `__constant__` `ab_gkr_round2_challenges` symbol regardless of where the
/// coefficients live.
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round2_unified_devptr<E: crate::prover::gkr::BackwardKernels>(
    desc: &GpuFlatRound2UnifiedDesc,
    folding_challenges: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const E,
    eq_low: *const E,
    eq_sizes: &GkrEqSizes,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let stream = context.get_exec_stream();
    launch_round2_challenges_prelude::<E>(folding_challenges, context)?;

    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound2FlatDevptrCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        coefficients,
        eq_low,
        *eq_sizes,
        contributions,
        acc_size,
    );
    GpuGKRMainRound2FlatDevptrCompactUnifiedCompactFunction(
        E::MAIN_ROUND2_FLAT_DEVPTR_COMPACT_UNIFIED_COMPACT,
    )
    .launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Device-pointer TERMS variants (Stage 3b): terms/tiles moved to device memory
// alongside the coefficients, selected when the inline __grid_constant__ desc
// would overflow the 32 KB cap (large delegations). Bit-identical to the
// coeff-devptr variants above; the ONLY difference is that `terms`,
// `tile_term_offsets`, `tile_fold_offsets` are read through the `term_tables`
// device pointers instead of the inline descriptor arrays.
// ---------------------------------------------------------------------------

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound1FlatDevptrTermsCompactUnifiedCompact<T>,
    desc: GpuFlatRound1UnifiedDescDevptr,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const T,
    term_tables: GpuFlatTermTables,
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round1_flat_devptr_terms_compact_unified_compact_e4_kernel(
        desc: GpuFlatRound1UnifiedDescDevptr,
        fold_stride: u32,
        next_layer_size: u32,
        coefficients: *const E4,
        term_tables: GpuFlatTermTables,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round1_unified_devptr_terms<E: crate::prover::gkr::BackwardKernels>(
    desc: &GpuFlatRound1UnifiedDescDevptr,
    _folding_challenge: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const E,
    term_tables: GpuFlatTermTables,
    eq_low: *const E,
    eq_sizes: &GkrEqSizes,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let stream = context.get_exec_stream();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound1FlatDevptrTermsCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        coefficients,
        term_tables,
        eq_low,
        *eq_sizes,
        contributions,
        acc_size,
    );
    GpuGKRMainRound1FlatDevptrTermsCompactUnifiedCompactFunction(
        E::MAIN_ROUND1_FLAT_DEVPTR_TERMS_COMPACT_UNIFIED_COMPACT,
    )
    .launch(&config, &args)
}

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound2FlatDevptrTermsCompactUnifiedCompact<T>,
    desc: GpuFlatRound2UnifiedDescDevptr,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const T,
    term_tables: GpuFlatTermTables,
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round2_flat_devptr_terms_compact_unified_compact_e4_kernel(
        desc: GpuFlatRound2UnifiedDescDevptr,
        fold_stride: u32,
        next_layer_size: u32,
        coefficients: *const E4,
        term_tables: GpuFlatTermTables,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round2_unified_devptr_terms<E: crate::prover::gkr::BackwardKernels>(
    desc: &GpuFlatRound2UnifiedDescDevptr,
    folding_challenges: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const E,
    term_tables: GpuFlatTermTables,
    eq_low: *const E,
    eq_sizes: &GkrEqSizes,
    contributions: *mut E,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    use era_cudart::execution::CudaLaunchConfig;
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let stream = context.get_exec_stream();
    launch_round2_challenges_prelude::<E>(folding_challenges, context)?;

    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GpuGKRMainRound2FlatDevptrTermsCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        coefficients,
        term_tables,
        eq_low,
        *eq_sizes,
        contributions,
        acc_size,
    );
    GpuGKRMainRound2FlatDevptrTermsCompactUnifiedCompactFunction(
        E::MAIN_ROUND2_FLAT_DEVPTR_TERMS_COMPACT_UNIFIED_COMPACT,
    )
    .launch(&config, &args)
}

era_cudart::cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound3FlatDevptrTermsUnifiedCompact<T>,
    desc: GpuFlatContinuationUnifiedDescDevptr,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    coefficients: *const T,
    term_tables: GpuFlatTermTables,
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round3_flat_devptr_terms_unified_compact_e4_kernel(
        desc: GpuFlatContinuationUnifiedDescDevptr,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        coefficients: *const E4,
        term_tables: GpuFlatTermTables,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round3_flat_devptr_terms_explicit_unified_compact_e4_kernel(
        desc: GpuFlatContinuationUnifiedDescDevptr,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        coefficients: *const E4,
        term_tables: GpuFlatTermTables,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        contributions: *mut E4,
        acc_size: u32,
    )
);

#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round3_unified_devptr_terms<E: crate::prover::gkr::BackwardKernels>(
    desc: &GpuFlatContinuationUnifiedDescDevptr,
    _folding_challenge: *const E,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    coefficients: *const E,
    term_tables: GpuFlatTermTables,
    eq_low: *const E,
    eq_sizes: &GkrEqSizes,
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
    let args = GpuGKRMainRound3FlatDevptrTermsUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        folding_challenge_slot,
        coefficients,
        term_tables,
        eq_low,
        *eq_sizes,
        contributions,
        acc_size,
    );
    let kernel = if explicit_form {
        E::MAIN_ROUND3_FLAT_DEVPTR_TERMS_EXPLICIT_UNIFIED_COMPACT
    } else {
        E::MAIN_ROUND3_FLAT_DEVPTR_TERMS_UNIFIED_COMPACT
    };
    GpuGKRMainRound3FlatDevptrTermsUnifiedCompactFunction(kernel).launch(&config, &args)
}
