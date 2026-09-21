//! CUDA-free host model shared by the execution orchestrator and both proving
//! backends: circuit identifiers and geometry, chunked host trace containers,
//! the finite-block allocator contract, and the Merkle memory-cap layout
//! conversion.
//!
//! It owns no scheduling, no device code and no backend implementation, so it
//! can sit below `gpu_trace` while a CPU backend that never links CUDA also
//! consumes it.
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
