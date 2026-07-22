// GPU scheduling contract: see docs/gpu_scheduling_contract.md

pub mod config;
pub mod gkr;
mod pow;
pub mod proof;
pub(crate) mod proof_layout;
pub use gpu_trace::trace; // TEMPORARY split bridge — removed in Task 12.
pub(crate) mod whir;

// Rewires internal `crate::prover::ProverContext` users AND serves
// `gpu_execution_prover`/`gpu_program_prover` downstream — this line stays
// until Task 12.
pub use gpu_prover_context::{ProverContext, ProverContextConfig};

/// One-time kernel configuration that must run before the first `prove()` call.
/// Called once from the prover-layer context builders (the GPU worker and the
/// test-context helper); idempotent via a `Once` guard in `gkr::backward::flat`.
pub fn configure_kernel_attributes() {
    gkr::backward::flat::configure_flat_kernel_cache_preference();
}

#[cfg(test)]
pub(crate) mod test_utils;
#[cfg(test)]
mod tests;
