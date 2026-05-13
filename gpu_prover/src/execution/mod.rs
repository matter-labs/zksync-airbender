use crate::allocator::host::ConcurrentStaticHostAllocator;

mod messages;
mod precomputations;
pub(crate) mod prover;
mod tracing;
mod workers;

pub(crate) type A = ConcurrentStaticHostAllocator;
