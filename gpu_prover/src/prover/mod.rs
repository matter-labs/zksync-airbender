// GPU scheduling contract: see docs/gpu_scheduling_contract.md

pub(crate) mod gkr;
mod pow;
pub(crate) mod proof;
pub(crate) mod trace;
pub(crate) mod whir;

/// One-time kernel configuration that must run before the first `prove()` call.
/// Called from `ProverContext` creation.
pub(crate) fn configure_kernel_attributes() {
    gkr::backward::flat::configure_flat_kernel_cache_preference();
}

#[cfg(test)]
pub(crate) mod test_utils;
#[cfg(test)]
mod tests;
