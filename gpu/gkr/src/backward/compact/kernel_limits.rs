//! Kernel-argument size limits shared across compact descriptors.
//!
//! All `__grid_constant__` descriptors must fit in `cudaLaunchKernelExC`'s
//! 32 KB inline parameter area (`KERNEL_ARG_HARD_CEILING_BYTES`).
//! `KERNEL_ARG_SOFT_TARGET_BYTES` is a tighter test-only budget that keeps
//! headroom for future table growth.

use super::super::kernels::GKR_BACKWARD_MAX_TRACE_LEN_LOG2;

/// Hard ceiling: kernel arguments must fit in `cudaLaunchKernelExC`'s 32 KB
/// inline parameter area. Any descriptor whose size exceeds this fails the
/// build (see compile-time assertions on each descriptor).
pub(crate) const KERNEL_ARG_HARD_CEILING_BYTES: usize = 32 * 1024;

/// Soft target: keep descriptors under 16 KB for headroom against future
/// table growth without re-bumping back into H2D territory.
#[cfg(test)]
pub(crate) const KERNEL_ARG_SOFT_TARGET_BYTES: usize = 16 * 1024;

/// Main-layer next-layer state stores `(folding_steps - 1)` per-round
/// challenges plus 2 transcript-squeezed values: `[folding_challenges,
/// last_r, next_batching]`.
pub(crate) const MAX_MAIN_LAYER_CLAIM_POINT_LEN: usize = GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 1;
