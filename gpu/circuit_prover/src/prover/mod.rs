// GPU scheduling contract: see docs/gpu_scheduling_contract.md

pub mod config;
pub(crate) mod context;
pub mod gkr;
mod pow;
pub mod proof;
pub(crate) mod proof_layout;
pub mod trace;
pub(crate) mod transfer;
pub(crate) mod whir;

pub use context::{ProverContext, ProverContextConfig};

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
