#![allow(incomplete_features)]
#![feature(allocator_api)]
// The e2e test suite normalizes prover's const-generic merkle/permutation types
// (e.g. `produce_initial_permutation_product_contribution`); without this the
// test build hits an E0391 predicate-normalization cycle (cf. gpu_whir, Task 10).
#![feature(generic_const_exprs)]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
// `UnsafeMutAccessor::get_mut(&self) -> &mut T` is the documented contract
// scaffolding for stream-scheduled callbacks — see gpu_core primitives/context.
#![allow(clippy::mut_from_ref)]

pub mod config;
pub mod proof;
pub(crate) mod upstream;

pub use config::{UnsupportedGpuSecurityLevel, GPU_SUPPORTED_SECURITY_LEVELS};

// TEMPORARY split bridges — removed in Task 12.
pub use gpu_trace::witness;
pub mod prover {
    pub use gpu_gkr::configure_kernel_attributes;
    pub use gpu_prover_context::{ProverContext, ProverContextConfig};
    pub use gpu_trace::trace;
    pub mod gkr {
        pub use gpu_gkr::setup;
    }
    pub mod config {
        pub use crate::config::*;
    }
    pub mod proof {
        pub use crate::proof::*;
        pub mod inputs {
            pub use crate::proof::inputs::*;
        }
    }
}

#[cfg(test)]
gpu_core::force_serial_libtest!();
#[cfg(test)]
pub(crate) mod test_utils;
#[cfg(test)]
mod tests;
