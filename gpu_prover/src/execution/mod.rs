use crate::allocator::host::ConcurrentStaticHostAllocator;

mod cpu_worker;
mod gpu_manager;
mod gpu_worker;
mod messages;
mod precomputations;
pub mod prover;
mod ram;
mod simulation_runner;
mod snapshotter;
mod tracer;
mod tracing_data_producers;

type A = ConcurrentStaticHostAllocator;
