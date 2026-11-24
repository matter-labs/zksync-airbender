#![feature(allocator_api)]
#![feature(once_cell_try)]

use host_storage::GpuTraceAllocator;

use gpu_circuit_prover::proof::memory_policy::presets as memory_policy;
pub mod baby_bear;
mod backend;
mod config;
mod host_storage;
mod precomputations;
mod proth120;
#[allow(unused_imports)]
mod upstream;
mod workers;

pub(crate) type A = GpuTraceAllocator;

pub type ExecutionProver = execution_prover::ExecutionProver<GpuBackend>;
pub type CommitMemoryResult = execution_prover::CommitMemoryResult;

pub type ExecutionProverConfiguration =
    execution_prover::ExecutionProverConfiguration<GpuBackendConfiguration>;

// Public API: the proving entry point + its handle/config/result types,
// plus the security-level surface re-exported from gpu_circuit_prover.
pub use backend::GpuBackend;
pub use config::{GpuBackendConfiguration, MemoryPreset};
pub use execution_prover::{
    BinaryHandle, CommitmentMode, ExecutionKind, ProgramArtifacts, ProveResult, RiscvFamilyArtifact,
};
pub use execution_prover_model::MachineType;
pub use gpu_circuit_prover::GPU_SUPPORTED_SECURITY_LEVELS;

#[cfg(test)]
gpu_core::force_serial_libtest!();
