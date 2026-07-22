//! Unified GPU-kernel dispatch surface.
//!
//! `GpuKernels` is the umbrella over the per-phase kernel sub-traits, each of
//! which is defined and implemented inside its own leaf module
//! (`forward::kernels`, `backward::kernels`, `setup::kernels`). Adding a new
//! extension field (e.g. `E6`) means writing one `impl` per sub-trait in the
//! leaves.

use crate::backward::kernels::BackwardKernels;
use crate::forward::kernels::ForwardKernels;
use crate::setup::kernels::SetupKernels;

// `#[doc(hidden)] pub` so the apex e2e test suite can name it as a generic
// bound; its `pub(crate)` supertraits stay internal by design (sealed
// per-phase kernel-dispatch traits — nothing outside this crate names
// `ForwardKernels`/`BackwardKernels`/`SetupKernels` directly, they only ever
// appear as inferred generic bounds, and every production/test bound that
// used to name a sub-trait directly has been rebound on this umbrella
// instead — see the individual call sites' "see gpu_kernels.rs" comments).
// This declaration itself is the one spot the sealing can't be routed
// around: `GpuKernels` must supertrait-bound the sealed traits to make the
// rebinding above sound, and that supertrait bound is inherently "more
// private than the pub trait" from rustc's point of view. Item-level allow
// (not crate-level): this is the sole remaining `private_bounds` site in the
// crate.
#[doc(hidden)]
#[allow(private_bounds)]
pub trait GpuKernels: ForwardKernels + BackwardKernels + SetupKernels {}

impl<E: ForwardKernels + BackwardKernels + SetupKernels> GpuKernels for E {}
