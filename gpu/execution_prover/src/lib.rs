#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![feature(get_mut_unchecked)]
#![feature(likely_unlikely)]
#![feature(once_cell_try)]
#![feature(pointer_is_aligned_to)]
// Prover-orchestration and worker-entry functions take one argument per
// distinct pipeline input (channels, configs, per-stage state); they aren't a
// cohesive bundle a params struct would clarify, and restructuring these
// worker entry points risks obscuring the pipeline wiring for a cosmetic win
// (same precedent as gpu_hash's / gpu_ntt's crate-level allow).
#![allow(clippy::too_many_arguments)]

use gpu_core::allocator::host::ConcurrentStaticHostAllocator;

mod messages;
mod precomputations;
mod prover;
mod tracing;
#[allow(unused_imports)]
mod upstream;
mod workers;

pub(crate) type A = ConcurrentStaticHostAllocator;

// Public API: the proving entry point + its handle/config/result types,
// plus the security-level surface re-exported from gpu_circuit_prover.
pub use gpu_circuit_prover::{UnsupportedGpuSecurityLevel, GPU_SUPPORTED_SECURITY_LEVELS};
pub use gpu_core::primitives::machine_type::MachineType;
pub use prover::{
    BinaryHandle, CircuitArtifact, CommitMemoryResult, ExecutionKind, ExecutionProver,
    ExecutionProverConfiguration, ProgramArtifacts, ProveResult,
};

#[cfg(test)]
gpu_core::force_serial_libtest!();
