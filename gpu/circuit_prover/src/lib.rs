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
// The proof-orchestration/e2e-fixture functions here take one argument per
// distinct device buffer / layout / stream input; splitting them into config
// structs would obscure the pipeline wiring for a cosmetic win (same
// precedent as gpu_hash's / gpu_ntt's / gpu_execution_prover's / gpu_trace's /
// gpu_gkr's / gpu_whir's crate-level allow).
#![allow(clippy::too_many_arguments)]

pub mod config;
pub mod proof;
pub(crate) mod upstream;

pub use config::{UnsupportedGpuSecurityLevel, GPU_SUPPORTED_SECURITY_LEVELS};

#[cfg(test)]
gpu_core::force_serial_libtest!();
#[cfg(test)]
pub(crate) mod test_utils;
#[cfg(test)]
mod tests;
