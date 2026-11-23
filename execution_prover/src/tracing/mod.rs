use execution_prover_model::allocator::{HostTraceAllocator, PooledHostAllocator};

mod producer;
mod producers;
mod ranges;
mod tracer;
mod ty;

pub(crate) use producer::*;
pub(crate) use producers::*;
pub(crate) use ranges::*;
pub(crate) use tracer::*;
pub(crate) use ty::*;

/// Only producer threads wait for a free allocator.
pub(crate) fn take_partial_tree_allocator<A: HostTraceAllocator>(
    free: &crossbeam_channel::Receiver<A>,
    pool: &Option<crossbeam_channel::Sender<A>>,
) -> Option<PooledHostAllocator<A>> {
    pool.as_ref().map(|pool| {
        let allocator = free
            .recv()
            .expect("ExecutionProver host-buffer pool closed during commitment preparation");
        let capacity = allocator.capacity();
        PooledHostAllocator::new(allocator, capacity, pool.clone())
    })
}
