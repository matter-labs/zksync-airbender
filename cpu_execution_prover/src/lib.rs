//! CPU backend with heap storage and one active proving request.
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]

mod backend;
mod config;
mod jobs;
mod manager;
mod precomputations;
mod upstream;

pub use backend::{CpuBackend, CpuExecutionProver};
pub use config::{CpuBackendConfiguration, CpuExecutionProverConfiguration};
