//! CUDA-free host model shared by the execution orchestrator and both proving
//! backends.
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]

pub mod allocator;
pub mod circuit_type;
mod machine_type;
pub mod trace;
mod upstream;

pub use machine_type::MachineType;
