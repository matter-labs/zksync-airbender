//! CPU backend with heap storage and one active proving request.
#![feature(allocator_api)]

mod backend;
mod config;
mod jobs;
mod manager;
mod precomputations;
mod upstream;

#[doc(hidden)]
pub mod test_support;

pub use backend::{CpuBackend, CpuExecutionProver};
pub use config::{CpuBackendConfiguration, CpuExecutionProverConfiguration};
