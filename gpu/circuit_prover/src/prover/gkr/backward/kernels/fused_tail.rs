//! Rust-side launchers for the backward-sumcheck fused-tail kernels and
//! the warp-partial round kernels that feed them, both defined in
//! `gpu/circuit_prover/native/prover/gkr/backward/`. E4-only for now (matches the
//! upstream pattern in `ops/blake2s/gkr_ops.rs`); generic-on-E plumbing
//! through `GpuKernels` can come later if a second extension field ships.
//!
//! All kernel symbols here are stream-ordered on `exec_stream`. The
//! finalize kernels write to `active_eq_slot_base` (a device pointer into
//! either the `ab_gkr_eq_high` `__constant__` slabs or the per-layer
//! `eq_low_group` buffer) — callers compute that pointer + the active
//! slot's size BEFORE the launch from the same `GkrEqSizes` state that
//! `fold_factored_eq_one_round` consults, then update `eq_sizes` to
//! reflect the fold AFTER the launch is scheduled.

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use super::launchers::{GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS};
use crate::primitives::field::E4;
use crate::prover::gkr::backward::compact::{
    launch_round2_challenges_prelude, GpuFlatContinuationUnifiedDesc,
    GpuFlatContinuationUnifiedDescDevptr, GpuFlatRound0StaticDesc, GpuFlatRound1UnifiedDesc,
    GpuFlatRound1UnifiedDescDevptr, GpuFlatRound2UnifiedDesc, GpuFlatRound2UnifiedDescDevptr,
    GpuFlatTermTables,
};
use crate::prover::ProverContext;

/// Matches `MEGA_FINALIZE_BLOCK_THREADS` in
/// `gpu/circuit_prover/native/prover/gkr/backward/mega_finalize.cuh`. Read on the
/// Rust side to pick the stage-1-vs-combined-launch path in
/// `dispatch_fused_tail`, and to size `round_scratch.partials`.
pub(crate) const MEGA_FINALIZE_BLOCK_THREADS: u32 = 256;

cuda_kernel!(
    BackwardDualReduceBlockwise,
    ab_gkr_backward_dual_reduce_blockwise_e4_kernel(
        contributions: *const E4,
        acc_size: u32,
        partials: *mut E4,
    )
);

cuda_kernel!(
    BackwardDualFinalizeFromPartials,
    ab_gkr_backward_dual_finalize_from_partials_e4_kernel(
        partials: *const E4,
        num_partials: u32,
        prev_claim_coord: *const E4,
        seed_io: *mut u32,
        claim_io: *mut E4,
        eq_prefactor_io: *mut E4,
        coeffs_out: *mut E4,
        challenge_out: *mut E4,
        active_eq_slot_base: *mut E4,
        active_eq_size_before_fold: u32,
    )
);

cuda_kernel!(
    BackwardDualFinalizeFromAcc,
    ab_gkr_backward_dual_finalize_from_acc_e4_kernel(
        acc: *const E4,
        acc_size: u32,
        prev_claim_coord: *const E4,
        seed_io: *mut u32,
        claim_io: *mut E4,
        eq_prefactor_io: *mut E4,
        coeffs_out: *mut E4,
        challenge_out: *mut E4,
        active_eq_slot_base: *mut E4,
        active_eq_size_before_fold: u32,
    )
);

// Round-1/2/3 continuation argument structs — kernel signatures match
// the warp-partial continuation kernels: same desc, eq_low, eq_sizes,
// output ptr, acc_size.

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound1FlatConstantCompactUnifiedCompact<T>,
    desc: GpuFlatRound1UnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound2FlatConstantCompactUnifiedCompact<T>,
    desc: GpuFlatRound2UnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
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

// Warp-partial continuation kernel symbols — warp-reduce epilogue. Each
// block writes one (c0, c1) partial pair to `partials[]`;
// `num_partials = acc_size / 32`.
cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round1_flat_constant_compact_unified_compact_warp_partial_e4_kernel(
        desc: GpuFlatRound1UnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        partials: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round2_flat_constant_compact_unified_compact_warp_partial_e4_kernel(
        desc: GpuFlatRound2UnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        partials: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round3_flat_constant_unified_compact_warp_partial_e4_kernel(
        desc: GpuFlatContinuationUnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        partials: *mut E4,
        acc_size: u32,
    )
);

// Device-pointer coeff variants of the warp-partial continuation kernels.
// Identical to the constant variants plus a `coefficients` device-buffer
// argument; selected when the continuation coefficient count exceeds
// FLAT_CONST_MAX.
cuda_kernel_signature_arguments_and_function!(
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

cuda_kernel_signature_arguments_and_function!(
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

cuda_kernel_signature_arguments_and_function!(
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
    ab_gkr_main_round1_flat_devptr_compact_unified_compact_warp_partial_e4_kernel(
        desc: GpuFlatRound1UnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        coefficients: *const E4,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        partials: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round2_flat_devptr_compact_unified_compact_warp_partial_e4_kernel(
        desc: GpuFlatRound2UnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        coefficients: *const E4,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        partials: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round3_flat_devptr_unified_compact_warp_partial_e4_kernel(
        desc: GpuFlatContinuationUnifiedDesc,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        coefficients: *const E4,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        partials: *mut E4,
        acc_size: u32,
    )
);

// Device-pointer TERMS variants of the warp-partial continuation kernels
// (Stage 3b): terms/tiles moved to device memory alongside the coefficients,
// selected when the inline desc would overflow the 32 KB cap.
cuda_kernel_signature_arguments_and_function!(
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

cuda_kernel_signature_arguments_and_function!(
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

cuda_kernel_signature_arguments_and_function!(
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
    ab_gkr_main_round1_flat_devptr_terms_compact_unified_compact_warp_partial_e4_kernel(
        desc: GpuFlatRound1UnifiedDescDevptr,
        fold_stride: u32,
        next_layer_size: u32,
        coefficients: *const E4,
        term_tables: GpuFlatTermTables,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        partials: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round2_flat_devptr_terms_compact_unified_compact_warp_partial_e4_kernel(
        desc: GpuFlatRound2UnifiedDescDevptr,
        fold_stride: u32,
        next_layer_size: u32,
        coefficients: *const E4,
        term_tables: GpuFlatTermTables,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        partials: *mut E4,
        acc_size: u32,
    )
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round3_flat_devptr_terms_unified_compact_warp_partial_e4_kernel(
        desc: GpuFlatContinuationUnifiedDescDevptr,
        fold_stride: u32,
        next_layer_size: u32,
        folding_challenge_slot: u32,
        coefficients: *const E4,
        term_tables: GpuFlatTermTables,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        partials: *mut E4,
        acc_size: u32,
    )
);

// Warp-partial round 0 kernel — warp-reduce + full eq inlined per row,
// one E4 pair per warp written to `partials[]`.
cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGKRMainRound0FlatConstantCompactWarpPartial<T>,
    static_desc: GpuFlatRound0StaticDesc,
    eq_low: *const T,
    eq_sizes: GkrEqSizes,
    partials: *mut T,
    acc_size: u32,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_main_round0_flat_constant_compact_warp_partial_e4_kernel(
        static_desc: GpuFlatRound0StaticDesc,
        eq_low: *const E4,
        eq_sizes: GkrEqSizes,
        partials: *mut E4,
        acc_size: u32,
    )
);

/// Returns the number of stage-1 blocks needed for the given accumulator
/// size, given the mega-finalize block-size convention. Returns 0 when the
/// combined single-launch path applies.
pub(crate) fn dual_reduce_num_stage1_blocks(acc_size: usize) -> usize {
    if acc_size as u32 <= MEGA_FINALIZE_BLOCK_THREADS {
        0
    } else {
        acc_size.div_ceil(MEGA_FINALIZE_BLOCK_THREADS as usize)
    }
}

/// Sizes the per-round partials buffer to the worst-case producer. The
/// warp-partial round kernels write one (c0, c1) pair per warp
/// (`acc_size / 32`), which exceeds the fused-tail stage-1's per-block
/// pairs (`acc_size / 256`); pick the larger so the same buffer fits
/// either path.
pub(crate) fn max_partials_len(max_acc_size: usize) -> usize {
    let num_warps = max_acc_size.div_ceil(32usize).max(1);
    2 * num_warps
}

/// Resolves the active eq slot for the upcoming fold. Returns
/// `(slot_base_ptr, slot_size_before_fold)` and the **next** size for the
/// caller to write back into `eq_sizes` AFTER the kernel is scheduled.
/// Mirrors `fold_factored_eq_one_round`'s priority order:
/// `high[0]` > `high[1]` > `low`.
pub(crate) fn resolve_active_eq_slot(eq_sizes: &GkrEqSizes, eq_low: *mut E4) -> (*mut E4, u32) {
    if eq_sizes.high[0] > 0 {
        let base = unsafe {
            super::launchers::get_eq_high_constant_device_ptr().add(0 * GKR_EQ_GROUP_TABLE_LEN)
        };
        (base, eq_sizes.high[0])
    } else if eq_sizes.high[1] > 0 {
        assert!(GKR_EQ_HIGH_SLOTS >= 2);
        let base = unsafe {
            super::launchers::get_eq_high_constant_device_ptr().add(GKR_EQ_GROUP_TABLE_LEN)
        };
        (base, eq_sizes.high[1])
    } else {
        debug_assert!(eq_sizes.low >= 1);
        (eq_low, eq_sizes.low)
    }
}

/// Applies the in-place size decrement to `eq_sizes` after the mega-finalize
/// kernel has been scheduled. Stream ordering guarantees the next round's
/// kernel sees the post-fold slot values.
pub(crate) fn record_active_eq_slot_fold(eq_sizes: &mut GkrEqSizes) {
    if eq_sizes.high[0] > 0 {
        eq_sizes.high[0] -= 1;
    } else if eq_sizes.high[1] > 0 {
        eq_sizes.high[1] -= 1;
    } else {
        debug_assert!(eq_sizes.low >= 1);
        eq_sizes.low -= 1;
    }
}

/// Fused-tail stage 1: per-block dual reduce. Skip this and call the
/// combined launcher when `dual_reduce_num_stage1_blocks(acc_size) == 0`.
pub(crate) fn launch_backward_dual_reduce_blockwise(
    contributions: *const E4,
    acc_size: usize,
    partials: *mut E4,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(acc_size <= u32::MAX as usize);
    let num_blocks = dual_reduce_num_stage1_blocks(acc_size);
    debug_assert!(num_blocks > 0);
    let config = CudaLaunchConfig::basic(
        num_blocks as u32,
        MEGA_FINALIZE_BLOCK_THREADS,
        context.get_exec_stream(),
    );
    let args = BackwardDualReduceBlockwiseArguments::new(contributions, acc_size as u32, partials);
    BackwardDualReduceBlockwiseFunction::default().launch(&config, &args)
}

/// Fused-tail stage 2: single-block mega-finalize over the partials buffer
/// produced by stage 1 (or by the warp-partial round kernel).
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_backward_dual_finalize_from_partials(
    partials: *const E4,
    num_partials: usize,
    prev_claim_coord: *const E4,
    seed: *mut u32,
    claim: *mut E4,
    eq_prefactor: *mut E4,
    coeffs_out: *mut E4,
    challenge_out: *mut E4,
    active_eq_slot_base: *mut E4,
    active_eq_size_before_fold: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(num_partials <= u32::MAX as usize);
    let config = CudaLaunchConfig::basic(1, MEGA_FINALIZE_BLOCK_THREADS, context.get_exec_stream());
    let args = BackwardDualFinalizeFromPartialsArguments::new(
        partials,
        num_partials as u32,
        prev_claim_coord,
        seed,
        claim,
        eq_prefactor,
        coeffs_out,
        challenge_out,
        active_eq_slot_base,
        active_eq_size_before_fold,
    );
    BackwardDualFinalizeFromPartialsFunction::default().launch(&config, &args)
}

/// Warp-partial continuation launcher — round 1. Grid of `acc_size/32` blocks ×
/// 128 threads; each block writes one (c0, c1) partial pair.
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round1_unified_warp_partial(
    desc: &GpuFlatRound1UnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    eq_low: *const E4,
    eq_sizes: &GkrEqSizes,
    partials: *mut E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream());
    let args = GpuGKRMainRound1FlatConstantCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        eq_low,
        *eq_sizes,
        partials,
        acc_size,
    );
    GpuGKRMainRound1FlatConstantCompactUnifiedCompactFunction(
        ab_gkr_main_round1_flat_constant_compact_unified_compact_warp_partial_e4_kernel,
    )
    .launch(&config, &args)
}

/// Warp-partial continuation launcher — round 2.
///
/// Schedules the `ab_gkr_round2_challenges_prelude` kernel before the
/// round-2 kernel, matching `compact::launch_main_round2_unified` —
/// round 2's lazy base-fold reads three values from the `__constant__`
/// `ab_gkr_round2_challenges[0..3]` symbol, so the prelude has to stage
/// them on `exec_stream` before any round-2 launch.
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round2_unified_warp_partial(
    desc: &GpuFlatRound2UnifiedDesc,
    folding_challenges: *const E4,
    fold_stride: u32,
    next_layer_size: u32,
    eq_low: *const E4,
    eq_sizes: &GkrEqSizes,
    partials: *mut E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    launch_round2_challenges_prelude::<E4>(folding_challenges, context)?;

    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream());
    let args = GpuGKRMainRound2FlatConstantCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        eq_low,
        *eq_sizes,
        partials,
        acc_size,
    );
    GpuGKRMainRound2FlatConstantCompactUnifiedCompactFunction(
        ab_gkr_main_round2_flat_constant_compact_unified_compact_warp_partial_e4_kernel,
    )
    .launch(&config, &args)
}

/// Warp-partial continuation launcher — round 3+ (non-explicit form only;
/// explicit-form final-round launch in `launch_round3_kernels_from_symbol`
/// the explicit-form path keeps the unfused launch shape).
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round3_unified_warp_partial(
    desc: &GpuFlatContinuationUnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    eq_low: *const E4,
    eq_sizes: &GkrEqSizes,
    partials: *mut E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream());
    let args = GpuGKRMainRound3FlatConstantUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        folding_challenge_slot,
        eq_low,
        *eq_sizes,
        partials,
        acc_size,
    );
    GpuGKRMainRound3FlatConstantUnifiedCompactFunction(
        ab_gkr_main_round3_flat_constant_unified_compact_warp_partial_e4_kernel,
    )
    .launch(&config, &args)
}

/// Device-pointer coeff variant of `launch_main_round1_unified_warp_partial`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round1_unified_warp_partial_devptr(
    desc: &GpuFlatRound1UnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const E4,
    eq_low: *const E4,
    eq_sizes: &GkrEqSizes,
    partials: *mut E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream());
    let args = GpuGKRMainRound1FlatDevptrCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        coefficients,
        eq_low,
        *eq_sizes,
        partials,
        acc_size,
    );
    GpuGKRMainRound1FlatDevptrCompactUnifiedCompactFunction(
        ab_gkr_main_round1_flat_devptr_compact_unified_compact_warp_partial_e4_kernel,
    )
    .launch(&config, &args)
}

/// Device-pointer coeff variant of `launch_main_round2_unified_warp_partial`.
/// Schedules the round-2 challenges prelude first, matching the constant twin.
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round2_unified_warp_partial_devptr(
    desc: &GpuFlatRound2UnifiedDesc,
    folding_challenges: *const E4,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const E4,
    eq_low: *const E4,
    eq_sizes: &GkrEqSizes,
    partials: *mut E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    launch_round2_challenges_prelude::<E4>(folding_challenges, context)?;

    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream());
    let args = GpuGKRMainRound2FlatDevptrCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        coefficients,
        eq_low,
        *eq_sizes,
        partials,
        acc_size,
    );
    GpuGKRMainRound2FlatDevptrCompactUnifiedCompactFunction(
        ab_gkr_main_round2_flat_devptr_compact_unified_compact_warp_partial_e4_kernel,
    )
    .launch(&config, &args)
}

/// Device-pointer coeff variant of `launch_main_round3_unified_warp_partial`
/// (non-explicit form only, matching the constant twin).
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round3_unified_warp_partial_devptr(
    desc: &GpuFlatContinuationUnifiedDesc,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    coefficients: *const E4,
    eq_low: *const E4,
    eq_sizes: &GkrEqSizes,
    partials: *mut E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream());
    let args = GpuGKRMainRound3FlatDevptrUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        folding_challenge_slot,
        coefficients,
        eq_low,
        *eq_sizes,
        partials,
        acc_size,
    );
    GpuGKRMainRound3FlatDevptrUnifiedCompactFunction(
        ab_gkr_main_round3_flat_devptr_unified_compact_warp_partial_e4_kernel,
    )
    .launch(&config, &args)
}

/// Device-pointer TERMS variant of `launch_main_round1_unified_warp_partial_devptr`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round1_unified_warp_partial_devptr_terms(
    desc: &GpuFlatRound1UnifiedDescDevptr,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const E4,
    term_tables: GpuFlatTermTables,
    eq_low: *const E4,
    eq_sizes: &GkrEqSizes,
    partials: *mut E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream());
    let args = GpuGKRMainRound1FlatDevptrTermsCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        coefficients,
        term_tables,
        eq_low,
        *eq_sizes,
        partials,
        acc_size,
    );
    GpuGKRMainRound1FlatDevptrTermsCompactUnifiedCompactFunction(
        ab_gkr_main_round1_flat_devptr_terms_compact_unified_compact_warp_partial_e4_kernel,
    )
    .launch(&config, &args)
}

/// Device-pointer TERMS variant of `launch_main_round2_unified_warp_partial_devptr`.
/// Schedules the round-2 challenges prelude first, matching the coeff-devptr twin.
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round2_unified_warp_partial_devptr_terms(
    desc: &GpuFlatRound2UnifiedDescDevptr,
    folding_challenges: *const E4,
    fold_stride: u32,
    next_layer_size: u32,
    coefficients: *const E4,
    term_tables: GpuFlatTermTables,
    eq_low: *const E4,
    eq_sizes: &GkrEqSizes,
    partials: *mut E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    launch_round2_challenges_prelude::<E4>(folding_challenges, context)?;

    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream());
    let args = GpuGKRMainRound2FlatDevptrTermsCompactUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        coefficients,
        term_tables,
        eq_low,
        *eq_sizes,
        partials,
        acc_size,
    );
    GpuGKRMainRound2FlatDevptrTermsCompactUnifiedCompactFunction(
        ab_gkr_main_round2_flat_devptr_terms_compact_unified_compact_warp_partial_e4_kernel,
    )
    .launch(&config, &args)
}

/// Device-pointer TERMS variant of `launch_main_round3_unified_warp_partial_devptr`
/// (non-explicit form only, matching the coeff-devptr twin).
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_main_round3_unified_warp_partial_devptr_terms(
    desc: &GpuFlatContinuationUnifiedDescDevptr,
    fold_stride: u32,
    next_layer_size: u32,
    folding_challenge_slot: u32,
    coefficients: *const E4,
    term_tables: GpuFlatTermTables,
    eq_low: *const E4,
    eq_sizes: &GkrEqSizes,
    partials: *mut E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let block_dim = 128u32;
    let grid_dim = acc_size.div_ceil(32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream());
    let args = GpuGKRMainRound3FlatDevptrTermsUnifiedCompactArguments::new(
        *desc,
        fold_stride,
        next_layer_size,
        folding_challenge_slot,
        coefficients,
        term_tables,
        eq_low,
        *eq_sizes,
        partials,
        acc_size,
    );
    GpuGKRMainRound3FlatDevptrTermsUnifiedCompactFunction(
        ab_gkr_main_round3_flat_devptr_terms_unified_compact_warp_partial_e4_kernel,
    )
    .launch(&config, &args)
}

/// Warp-partial round-0 launcher. Block size matches the unfused round-0 launcher
/// (`GKR_DIM_REDUCING_THREADS_PER_BLOCK = 128` = 4 warps), so
/// `num_warps_total = ceil(acc_size / 32)` and the tail uses that as
/// `num_partials` in the stage-2 finalize.
pub(crate) fn launch_main_round0_constant_warp_partial(
    static_desc: &GpuFlatRound0StaticDesc,
    eq_low: *const E4,
    eq_sizes: &GkrEqSizes,
    partials: *mut E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    use crate::primitives::utils::get_grid_block_dims_for_threads_count;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(
        super::launchers::GKR_DIM_REDUCING_THREADS_PER_BLOCK,
        acc_size.max(1),
    );
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream());
    let args = GpuGKRMainRound0FlatConstantCompactWarpPartialArguments::new(
        *static_desc,
        eq_low,
        *eq_sizes,
        partials,
        acc_size,
    );
    GpuGKRMainRound0FlatConstantCompactWarpPartialFunction(
        ab_gkr_main_round0_flat_constant_compact_warp_partial_e4_kernel,
    )
    .launch(&config, &args)
}

/// Number of warp partials produced by `launch_main_round0_constant_warp_partial`.
/// Each warp handles 32 acc rows; the round-0 grid covers
/// `ceil(acc_size / 128)` blocks of 4 warps, so the total warp count
/// rounds the acc size up to the next multiple of 32.
pub(crate) fn warp_partial_count(acc_size: usize) -> usize {
    acc_size.div_ceil(32)
}

/// Fused-tail combined: single-block kernel that reads `acc[]` directly. Used when
/// `acc_size <= MEGA_FINALIZE_BLOCK_THREADS`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn launch_backward_dual_finalize_from_acc(
    acc: *const E4,
    acc_size: usize,
    prev_claim_coord: *const E4,
    seed: *mut u32,
    claim: *mut E4,
    eq_prefactor: *mut E4,
    coeffs_out: *mut E4,
    challenge_out: *mut E4,
    active_eq_slot_base: *mut E4,
    active_eq_size_before_fold: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(acc_size <= u32::MAX as usize);
    let config = CudaLaunchConfig::basic(1, MEGA_FINALIZE_BLOCK_THREADS, context.get_exec_stream());
    let args = BackwardDualFinalizeFromAccArguments::new(
        acc,
        acc_size as u32,
        prev_claim_coord,
        seed,
        claim,
        eq_prefactor,
        coeffs_out,
        challenge_out,
        active_eq_slot_base,
        active_eq_size_before_fold,
    );
    BackwardDualFinalizeFromAccFunction::default().launch(&config, &args)
}
