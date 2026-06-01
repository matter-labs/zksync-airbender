//! Unified GPU-kernel dispatch surface.
//!
//! `GpuKernels` is the umbrella over the per-phase kernel sub-traits, each of
//! which is defined and implemented inside its own leaf module
//! (`forward::kernels`, `backward::kernels`, `setup::kernels`). The spine no
//! longer imports concrete leaf kernel symbols — adding a new extension field
//! (e.g. `E6`) means writing one `impl` per sub-trait in the leaves.

use crate::prover::gkr::backward::kernels::BackwardKernels;
use crate::prover::gkr::forward::kernels::ForwardKernels;
use crate::prover::gkr::setup::kernels::SetupKernels;

pub(crate) trait GpuKernels: ForwardKernels + BackwardKernels + SetupKernels {}

impl<E: ForwardKernels + BackwardKernels + SetupKernels> GpuKernels for E {}
