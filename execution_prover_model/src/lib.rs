//! CUDA-free host model shared by the execution orchestrator and both proving
//! backends.
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]

pub mod allocator;
pub mod caps;
pub mod circuit_type;
mod machine_type;
pub mod trace;
#[allow(unused_imports)]
mod upstream;

pub use machine_type::MachineType;
