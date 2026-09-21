//! `MachineType` is defined in `riscv_common` so the CUDA-free execution model
//! and this CUDA stack can both name it without depending on each other. This
//! re-export keeps the historical `gpu_core::primitives::machine_type` path
//! working for every existing GPU caller.
pub use riscv_common::machine_type::MachineType;
