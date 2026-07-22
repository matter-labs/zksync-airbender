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
// bound; its `pub(crate)` supertraits stay internal (a `private_bounds`
// warn-lint, cleaned up in a later task).
#[doc(hidden)]
pub trait GpuKernels: ForwardKernels + BackwardKernels + SetupKernels {}

impl<E: ForwardKernels + BackwardKernels + SetupKernels> GpuKernels for E {}
