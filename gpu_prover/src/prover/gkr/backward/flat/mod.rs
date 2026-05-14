//! Flattened GKR backward pass round 0 kernel.
//!
//! Instead of a 20-way switch on gate kind, this compiles every gate in the
//! layer into flat arrays of linear/quadratic terms. The structural part
//! (source table + term pairs) is passed as `__grid_constant__`, while the
//! challenge-dependent coefficients live in a separate device buffer filled
//! at schedule time via a stream callback.

mod build_plan;
mod builder;
mod compile;
mod continuation;
mod diagnostics;
mod emit;
mod kernel_setup;
mod round12_fused;
mod types;

pub(crate) use build_plan::*;
pub(crate) use compile::*;
pub(crate) use continuation::*;
pub(crate) use diagnostics::*;
pub(crate) use kernel_setup::*;
pub(crate) use round12_fused::*;
pub(crate) use types::*;

#[cfg(test)]
mod tests;
