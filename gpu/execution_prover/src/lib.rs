//! The GPU specialization of `execution_prover`: pinned host storage,
//! per-circuit GPU precomputations, the device memory policy, and the staged
//! manager/worker protocol.
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![feature(once_cell_try)]
// Prover-orchestration and worker-entry functions take one argument per
// distinct pipeline input (channels, configs, per-stage state); they aren't a
// cohesive bundle a params struct would clarify, and restructuring these
// worker entry points risks obscuring the pipeline wiring for a cosmetic win
// (same precedent as gpu_hash's / gpu_ntt's crate-level allow).
#![allow(clippy::too_many_arguments)]

use gpu_circuit_prover::proof::memory_policy::presets as memory_policy;

mod backend;
mod host_storage;
#[cfg(feature = "memory_sweep")]
pub mod memory_sweep;
pub mod precomputations;
mod upstream;
mod workers;

pub use backend::{GpuBackend, GpuBackendConfiguration, MemoryPreset};
pub use host_storage::GpuTraceAllocator;

pub type ExecutionProver = execution_prover::ExecutionProver<GpuBackend>;
pub type ExecutionProverConfiguration =
    execution_prover::ExecutionProverConfiguration<GpuBackendConfiguration>;

// Public API: the proving entry point + its handle/config/result types,
// plus the security-level surface re-exported from gpu_circuit_prover.
pub use execution_prover::{
    BinaryHandle, CommitMemoryResult, ExecutionKind, ProgramArtifacts, ProveResult,
    RiscvFamilyArtifact,
};
pub use execution_prover_model::MachineType;
pub use gpu_circuit_prover::{UnsupportedGpuSecurityLevel, GPU_SUPPORTED_SECURITY_LEVELS};

#[cfg(test)]
gpu_core::force_serial_libtest!();
