#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![feature(get_mut_unchecked)]
#![feature(likely_unlikely)]
#![feature(once_cell_try)]
#![feature(pointer_is_aligned_to)]

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
// plus the security-level surface re-exported from circuit_prover.
pub use circuit_prover::{UnsupportedGpuSecurityLevel, GPU_SUPPORTED_SECURITY_LEVELS};
pub use gpu_core::primitives::machine_type::MachineType;
pub use prover::{
    BinaryHandle, CircuitArtifact, CommitMemoryResult, ExecutionKind, ExecutionProver,
    ExecutionProverConfiguration, ProgramArtifacts, ProveResult,
};
