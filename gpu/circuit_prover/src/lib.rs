#![allow(incomplete_features)]
#![cfg_attr(test, feature(allocator_api))]
// The e2e test suite normalizes prover's const-generic merkle/permutation types
// (e.g. `produce_initial_permutation_product_contribution`); without this the
// test build hits an E0391 predicate-normalization cycle.
#![feature(generic_const_exprs)]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
// Required by the stream-scheduled callback accessors.
#![allow(clippy::mut_from_ref)]

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
