//! CUDA-free host model shared by the execution orchestrator and both proving
//! backends: circuit identifiers and geometry, chunked host trace containers,
//! the finite-block allocator contract, and the Merkle memory-cap layout
//! conversion.
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]

pub mod allocator;
pub mod caps;
pub mod circuit_type;
pub mod trace;
#[allow(unused_imports)]
mod upstream;

pub use riscv_common::machine_type::MachineType;
