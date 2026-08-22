//! Launchers for the window tensor round tail: the three main-layer sumcheck
//! rounds a width-3 window replaces.
//!
//! The matching CUDA definitions live in
//! `native/gkr/backward/window_tail.cu`.

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

/// Cells of the reduced window tensor, `9 * x0 + 3 * x1 + x2` over
/// `{0, 1, infinity}`.
pub(crate) const WINDOW_TAIL_TENSOR_CELLS: usize = 27;
const WINDOW_TAIL_TILE_SLOTS: usize = 32;
const WINDOW_TAIL_ABSORBED_BLOCK_THREADS: u32 =
    (WINDOW_TAIL_TENSOR_CELLS * WINDOW_TAIL_TILE_SLOTS) as u32;
const WINDOW_TAIL_REDUCE_BLOCK_THREADS: u32 = 256;
const WINDOW_TAIL_BLOCK_THREADS: u32 = 256;

cuda_kernel!(
    WindowTailAbsorbed,
    ab_gkr_bwd_window3_tail_absorbed_kernel(
        partials: *const E4,
        row_tiles: u32,
        prev_claim_coords: *const E4,
        seed_io: *mut u32,
        claim_io: *mut E4,
        eq_prefactor_io: *mut E4,
        coeffs_out: *mut E4,
        challenges_out: *mut E4,
        active_eq_slot_base: *mut E4,
        active_eq_size_before_fold: u32,
    )
);

cuda_kernel!(
    WindowTailReduce,
    ab_gkr_bwd_window3_tail_reduce_kernel(
        partials: *const E4,
        row_tiles: u32,
        tensor_out: *mut E4,
    )
);

cuda_kernel!(
    WindowTailFromTensor,
    ab_gkr_bwd_window3_tail_from_tensor_kernel(
        tensor: *const E4,
        prev_claim_coords: *const E4,
        seed_io: *mut u32,
        claim_io: *mut E4,
        eq_prefactor_io: *mut E4,
        coeffs_out: *mut E4,
        challenges_out: *mut E4,
        active_eq_slot_base: *mut E4,
        active_eq_size_before_fold: u32,
    )
);

/// Which reduction the tail runs. Proof semantics are identical; the arm is a
/// measured performance choice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WindowTailArm {
    /// One block reduces the partial matrix and plays the rounds.
    Absorbed,
    /// 27 blocks reduce the partial matrix into `reduced_tensor`, then one
    /// block plays the rounds.
    Split,
}

/// Device state one tail launch consumes and advances.
pub(crate) struct WindowTailState {
    /// Row-tile-major `27 * row_tiles` window partial matrix.
    pub partials: *const E4,
    pub row_tiles: usize,
    /// 27 E4 of scratch, written and read by [`WindowTailArm::Split`] only.
    pub reduced_tensor: *mut E4,
    /// The three peeled coordinates of the previous claim point.
    pub prev_claim_coords: *const E4,
    pub seed: *mut u32,
    pub claim: *mut E4,
    pub eq_prefactor: *mut E4,
    /// 12 slab coefficients, round-major.
    pub coeffs_out: *mut E4,
    /// The three drawn challenges, in claim-point order.
    pub challenges_out: *mut E4,
    pub active_eq_slot_base: *mut E4,
    pub active_eq_size_before_fold: u32,
}

/// Reduces the window partial matrix, plays rounds 0-2, and folds the active eq
/// slot once.
pub(crate) fn launch_window_tensor_round_tail(
    arm: WindowTailArm,
    state: &WindowTailState,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(state.row_tiles > 0);
    assert!(state.row_tiles <= u32::MAX as usize);
    let row_tiles = state.row_tiles as u32;
    let stream = context.get_exec_stream();

    match arm {
        WindowTailArm::Absorbed => {
            let config = CudaLaunchConfig::basic(1, WINDOW_TAIL_ABSORBED_BLOCK_THREADS, stream);
            let args = WindowTailAbsorbedArguments::new(
                state.partials,
                row_tiles,
                state.prev_claim_coords,
                state.seed,
                state.claim,
                state.eq_prefactor,
                state.coeffs_out,
                state.challenges_out,
                state.active_eq_slot_base,
                state.active_eq_size_before_fold,
            );
            WindowTailAbsorbedFunction::default().launch(&config, &args)
        }
        WindowTailArm::Split => {
            let reduce_config = CudaLaunchConfig::basic(
                WINDOW_TAIL_TENSOR_CELLS as u32,
                WINDOW_TAIL_REDUCE_BLOCK_THREADS,
                stream,
            );
            let reduce_args =
                WindowTailReduceArguments::new(state.partials, row_tiles, state.reduced_tensor);
            WindowTailReduceFunction::default().launch(&reduce_config, &reduce_args)?;

            let config = CudaLaunchConfig::basic(1, WINDOW_TAIL_BLOCK_THREADS, stream);
            let args = WindowTailFromTensorArguments::new(
                state.reduced_tensor,
                state.prev_claim_coords,
                state.seed,
                state.claim,
                state.eq_prefactor,
                state.coeffs_out,
                state.challenges_out,
                state.active_eq_slot_base,
                state.active_eq_size_before_fold,
            );
            WindowTailFromTensorFunction::default().launch(&config, &args)
        }
    }
}
