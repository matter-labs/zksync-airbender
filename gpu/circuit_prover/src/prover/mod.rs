// GPU scheduling contract: see docs/gpu_scheduling_contract.md

pub mod config;
pub mod proof;
pub use gpu_trace::trace; // TEMPORARY split bridge — removed in Task 12.
                          // whir + pow moved to the gpu_whir crate (Task 10). Their apex consumers
                          // (proof/orchestration, tests) now import `gpu_whir::…` directly — no bridge,
                          // since nothing downstream of the apex imports whir/pow.

// Rewires internal `crate::prover::ProverContext` users AND serves
// `gpu_execution_prover`/`gpu_program_prover` downstream — this line stays
// until Task 12.
pub use gpu_prover_context::{ProverContext, ProverContextConfig};

// TEMPORARY split bridge — removed in Task 12.
pub mod gkr {
    pub use gpu_gkr::setup;
}
pub use gpu_gkr::configure_kernel_attributes; // TEMPORARY split bridge — removed in Task 12.

#[cfg(test)]
pub(crate) mod test_utils;
#[cfg(test)]
mod tests;
