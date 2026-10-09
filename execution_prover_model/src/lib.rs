//! CUDA-free host model shared by the execution orchestrator and both proving
//! backends.
#![feature(allocator_api)]

pub mod allocator;
pub mod circuit_type;
mod machine_type;
pub mod trace;
mod upstream;

pub use machine_type::MachineType;
