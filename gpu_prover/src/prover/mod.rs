// GPU scheduling contract: see docs/gpu_scheduling_contract.md

pub(crate) mod decoder;
pub(crate) mod gkr;
pub(crate) mod memory;
pub(crate) mod memory_transfer;
mod pow;
pub(crate) mod proof;
pub(crate) mod proof_layout;
pub(crate) mod trace_holder;
pub(crate) mod tracing_data;
pub(crate) mod whir;
pub(crate) mod whir_fold;
pub(crate) mod whir_kernels;

/// One-time kernel configuration that must run before the first `prove()` call.
/// Called from `ProverContext` creation.
pub(crate) fn configure_kernel_attributes() {
    gkr::backward_flat::configure_flat_kernel_cache_preference();
}

#[cfg(test)]
pub(crate) mod test_utils;
#[cfg(test)]
mod tests;
