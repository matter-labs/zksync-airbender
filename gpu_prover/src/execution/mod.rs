use crate::allocator::host::ConcurrentStaticHostAllocator;

mod cpu_worker;
mod gpu_manager;
mod gpu_worker;
mod messages;
mod precomputations;
pub mod prover;
mod simulation_runner;
mod tracing;

pub(crate) type A = ConcurrentStaticHostAllocator;
