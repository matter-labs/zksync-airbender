//! CPU backend with heap storage and one active proving request.
#![feature(allocator_api)]

mod backend;
mod config;
mod jobs;
mod manager;
mod precomputations;
mod upstream;

pub use backend::{CpuBackend, CpuExecutionProver};
pub use config::{CpuBackendConfiguration, CpuExecutionProverConfiguration};
