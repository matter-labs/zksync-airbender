//! Standalone first-window GKR sumcheck GPU experiment.

pub mod abi;
pub mod artifact;
pub mod geometry;
pub mod harness;
pub mod kernels;
pub mod nvtx;
pub mod timing;

#[cfg(any(test, feature = "r0-prototype-bank"))]
mod wide_model;

#[cfg(feature = "artifact-gen")]
pub mod generator;

#[cfg(feature = "artifact-gen")]
pub mod host_eval;

#[cfg(feature = "artifact-gen")]
pub mod census;

#[cfg(feature = "artifact-gen")]
pub mod accumulator_schedule;

#[cfg(feature = "artifact-gen")]
pub mod accumulator_bounds;

#[cfg(feature = "artifact-gen")]
pub mod accumulator_locality;

#[cfg(feature = "artifact-gen")]
pub mod accumulator_encoding;

#[cfg(feature = "artifact-gen")]
pub mod accumulator_census;

#[cfg(feature = "artifact-gen")]
pub mod compact;

#[cfg(feature = "artifact-gen")]
pub mod lazy_segments;

#[cfg(feature = "artifact-gen")]
pub mod r0_artifact;

#[cfg(feature = "artifact-gen")]
pub mod r0_abi;

#[cfg(feature = "artifact-gen")]
pub mod r0_corpus;

#[cfg(feature = "artifact-gen")]
pub mod r0_input;

#[cfg(feature = "artifact-gen")]
pub mod r0_reference;

#[cfg(feature = "artifact-gen")]
pub mod r0_geometry;

#[cfg(feature = "artifact-gen")]
pub mod r0_harness;

#[cfg(feature = "artifact-gen")]
pub mod r0_kernels;

#[cfg(feature = "artifact-gen")]
pub mod r0_report;

#[cfg(feature = "r0-prototype-bank")]
pub mod r0_prototype_manifest;

#[cfg(feature = "r0-prototype-bank")]
pub mod r0_prototype_encoding;

#[cfg(feature = "r0-prototype-bank")]
pub mod r0_prototype_tile;

#[cfg(feature = "r0-prototype-bank")]
pub mod r0_prototype_abi;

#[cfg(feature = "r0-prototype-bank")]
pub mod r0_prototype_accumulator;

#[cfg(feature = "r0-prototype-bank")]
mod r0_prototype_native_contract;

#[cfg(feature = "r0-prototype-bank")]
pub mod r0_prototype_kernels;

#[cfg(feature = "r0-prototype-bank")]
pub mod r0_prototype_harness;

#[cfg(feature = "r0-prototype-bank")]
pub mod r0_prototype_report;

pub mod runtime_paths;

#[cfg(all(test, feature = "artifact-gen"))]
mod window_tail_cross;
