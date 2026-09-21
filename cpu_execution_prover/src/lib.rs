//! CPU specialization of the shared execution prover.
//!
//! `CpuBackend` is what the shared `ExecutionProver` drives: finite host trace
//! blocks on ordinary heap memory, guest RAM and JIT snapshots without any
//! device registration, and a manager that runs one circuit request at a time.
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]

mod adapters;
pub mod backend;
pub mod config;
pub mod host_storage;
mod jobs;
mod manager;
pub mod precomputations;
mod upstream;

pub use backend::{CpuBackend, CpuExecutionProver};
pub use config::{CpuBackendConfiguration, CpuExecutionProverConfiguration};
pub use host_storage::{BoxedMemoryHolder, BoxedTraceChunk, CpuTraceAllocator};
pub use precomputations::CpuCircuitPrecomputations;

pub use execution_prover::{
    BinaryHandle, CommitMemoryResult, ExecutionKind, ExecutionProverError, MachineType,
    ProgramArtifacts, ProveResult, RiscvFamilyArtifact,
};

/// Not public API: the manager and its injected-executor seam, reachable under
/// the non-default `test_utils` feature so the integration tests in `tests/`
/// can drive its lifecycle. Mirrors `execution_prover::test_support`.
#[cfg(any(test, feature = "test_utils"))]
pub mod test_support {
    pub use crate::manager::{spawn_injection, CpuManager, RequestExecutor};
}
