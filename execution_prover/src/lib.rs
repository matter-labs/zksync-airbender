//! Backend-independent execution proving: setup construction, simulation and
//! replay, the trace cache and the commit/prove protocol. Builds without CUDA.
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![feature(get_mut_unchecked)]
#![feature(likely_unlikely)]
#![feature(pointer_is_aligned_to)]
// Worker and orchestration entry points take one argument per pipeline input;
// bundling them into a params struct would hide the wiring.
#![allow(clippy::too_many_arguments)]

pub mod backend;
pub mod config;
pub mod messages;
mod prover;
pub mod setup;
mod tracing;
mod upstream;
mod workers;

#[cfg(test)]
mod test_support;

pub use config::{prover_config, ExecutionProverConfiguration};
pub use execution_prover_model::MachineType;
pub use prover::{
    BinaryHandle, CommitMemoryResult, ExecutionKind, ExecutionProver, ProgramArtifacts,
    ProveResult, RiscvFamilyArtifact,
};
pub use workers::spawn_abort_on_panic;
