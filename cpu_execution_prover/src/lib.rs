//! CPU backend with heap storage and one active proving request.
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
pub use host_storage::CpuTraceAllocator;

pub use execution_prover::{ExecutionKind, MachineType};
