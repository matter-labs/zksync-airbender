//! Launchers for E4 backward-sumcheck fused-tail kernels.

use super::launchers::{GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

/// Matches `MEGA_FINALIZE_BLOCK_THREADS` in
/// `gpu/gkr/native/gkr/backward/mega_finalize.cuh`. Read on the
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
/// Priority is `high[0]` > `high[1]` > `low`.
pub(crate) fn resolve_active_eq_slot(eq_sizes: &GkrEqSizes, eq_low: *mut E4) -> (*mut E4, u32) {
    if eq_sizes.high[0] > 0 {
        #[allow(clippy::erasing_op)]
        // `0 * GKR_EQ_GROUP_TABLE_LEN` kept for symmetry with the implicit 1* sibling below
        let base = unsafe {
            super::launchers::get_eq_high_constant_device_ptr().add(0 * GKR_EQ_GROUP_TABLE_LEN)
        };
        (base, eq_sizes.high[0])
    } else if eq_sizes.high[1] > 0 {
        const { assert!(GKR_EQ_HIGH_SLOTS >= 2) };
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

/// Number of 32-row partials produced by a VM round.
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
