#![allow(incomplete_features)]
#![cfg_attr(test, feature(allocator_api))]
#![feature(generic_const_exprs)]
#![warn(clippy::manual_div_ceil)]
#![warn(clippy::needless_pass_by_value)]
// `UnsafeMutAccessor::get_mut(&self) -> &mut T` is the documented contract
// scaffolding for stream-scheduled callbacks — see gpu_core primitives/context.rs.
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
// `ForwardKernels`/`BackwardKernels`/`SetupKernels` (`{forward,backward,setup}::kernels`)
// are deliberately sealed per-phase kernel-dispatch traits — `pub(crate)` on
// purpose, implemented only for the concrete field types this crate wires up
// (today, only `E4`), never named by another crate. Every pub fn/impl that
// used to bound a generic directly on one of these sub-traits has been
// rebound on the `GpuKernels` umbrella trait instead (equivalent today: E4 is
// the sole implementor of all three, so `T: GpuKernels` and `T: <the specific
// sub-trait>` admit exactly the same types); see `gpu_kernels.rs` for the one
// remaining `private_bounds` site this can't route around (the `GpuKernels`
// declaration's own supertrait bound) and its item-level `#[allow]`.

pub mod backward;
pub mod base_layer_claims;
pub mod forward;
pub mod gkr_ops;
pub mod proof_layout;
pub mod setup;
pub mod stage1;
pub(crate) mod storage;
pub(crate) mod storage_types;
pub(crate) mod support;
#[allow(unused_imports)]
pub(crate) mod upstream;

// `GpuKernels` is `#[doc(hidden)] pub` (with `gpu_kernels` compiled in all
// builds) so the apex e2e test suite can name it as a generic bound; its
// `pub(crate)` supertraits stay internal (a `private_bounds` warn-lint, cleaned
// up in a later task).
#[doc(hidden)]
pub mod gpu_kernels;
#[doc(hidden)]
pub use gpu_kernels::GpuKernels;

pub(crate) use backward::kernels::BackwardKernels;
pub(crate) use forward::kernels::ForwardKernels;
pub(crate) use setup::kernels::SetupKernels;
pub(crate) use storage_types::*;
// `#[doc(hidden)] pub` re-exports: apex e2e tests + proof orchestration name
// these storage/descriptor types via `gpu_gkr::…` across the crate boundary
// (rows 37/38/39 + cluster C). Test-reference surface.
#[doc(hidden)]
pub use storage_types::{
    GpuBaseFieldPoly, GpuBaseFieldPolySource,
    GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor, GpuExtensionFieldPoly,
    GpuExtensionFieldPolyContinuingLaunchDescriptor, GpuExtensionFieldPolyInitialSource,
    GpuGKRStorage, GpuSumcheckRound0LaunchDescriptors, GpuSumcheckRound1DeviceLaunchDescriptors,
    GpuSumcheckRound1ScheduledLaunchDescriptors,
};
pub(crate) use support::eval_recipes;
#[doc(hidden)] // test-reference: apex expected_specs builds these recipes
pub use support::immediate_factors;

// The GPU-free CPU model of the GKR layout lives in the standalone
// `gpu_gkr_model` crate; re-exported here as the public facade downstream and
// the apex consume (`gpu_gkr::{gkr_address_audit, storage_layout, transform}`).
pub use gpu_gkr_model::address_audit as gkr_address_audit;
pub use gpu_gkr_model::storage_layout;
pub use gpu_gkr_model::transform;
// Keep the public path `gpu_gkr::gkr_initial_inner_products` (apex proof).
pub use support::initial_inner_products as gkr_initial_inner_products;

/// One-time kernel configuration that must run before the first `prove()` call.
/// Idempotent via a `Once` guard in `backward::flat`.
pub fn configure_kernel_attributes() {
    backward::flat::configure_flat_kernel_cache_preference();
}

#[cfg(test)]
gpu_core::force_serial_libtest!();
#[cfg(test)]
pub(crate) mod gkr_address_audit_helpers;
#[cfg(test)]
pub(crate) mod test_utils;
#[cfg(test)]
mod tests;

// The tests.rs `GpuSumcheckRound0*` scaffolding types are consumed by
// `#[cfg(test)]` helper methods in production files (`storage::ops`,
// `backward::kernels::launchers`); re-exported at the crate root under the
// same gate so those `crate::…` paths resolve.
#[cfg(test)]
pub(crate) use tests::{
    GpuSumcheckRound0DeviceLaunchDescriptors, GpuSumcheckRound0HostLaunchDescriptors,
    GpuSumcheckRound0ScheduledLaunchDescriptors,
};
