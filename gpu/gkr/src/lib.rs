#![allow(incomplete_features)]
#![cfg_attr(test, feature(allocator_api))]
#![feature(generic_const_exprs)]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
// Required by the stream-scheduled callback accessors.
#![allow(clippy::mut_from_ref)]
// The scheduling/launcher functions here take one argument per distinct
// device buffer / layout / stream input; splitting them into config structs
// would obscure the pipeline wiring for a cosmetic win (same precedent as
// gpu_hash's / gpu_ntt's / gpu_execution_prover's / gpu_trace's crate-level
// allow).
#![allow(clippy::too_many_arguments)]
// `no_cuda` gates out every GPU test body, leaving their helpers and imports dead
// by construction. That mode only ever compiles, so this is not a real finding.
#![cfg_attr(no_cuda, allow(dead_code, unused_imports))]
pub mod backward;
pub mod base_layer_claims;
pub mod forward;
pub mod gkr_ops;
mod programs;
pub mod proof_layout;
pub mod setup;
pub mod stage1;
pub(crate) mod storage;
pub(crate) mod storage_types;
pub(crate) mod support;
pub(crate) mod upstream;

pub(crate) use forward::kernels::ForwardKernels;
pub(crate) use gpu_gkr_model::address_audit as gkr_address_audit;
pub(crate) use gpu_gkr_model::storage_layout;
pub(crate) use gpu_gkr_model::transform;
pub use programs::GkrPrograms;
pub(crate) use storage_types::*;
// Keep the public path `gpu_gkr::gkr_initial_inner_products` (apex proof).
pub use support::initial_inner_products as gkr_initial_inner_products;

#[cfg(test)]
gpu_core::force_serial_libtest!();
#[cfg(test)]
pub(crate) mod test_utils;
