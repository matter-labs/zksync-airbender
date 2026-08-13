//! Standalone first-window GKR sumcheck GPU experiment.

pub mod abi;
pub mod artifact;
pub mod geometry;
pub mod harness;
pub mod kernels;
pub mod nvtx;
pub mod timing;

#[cfg(test)]
mod wide_model;

#[cfg(feature = "artifact-gen")]
pub mod generator;
