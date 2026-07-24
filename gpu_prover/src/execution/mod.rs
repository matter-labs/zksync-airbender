use crate::allocator::host::ConcurrentStaticHostAllocator;

pub mod cpu_pipeline_model;
mod cpu_worker;
mod gpu_manager;
mod gpu_worker;
pub(crate) mod messages;
pub(crate) mod precomputations;
pub mod prover;
mod simulation_runner;
mod tracing;

pub(crate) type A = ConcurrentStaticHostAllocator;
