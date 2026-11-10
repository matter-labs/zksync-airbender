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

/// Only producer threads wait for a free buffer; the result loop returns them.
pub(crate) fn take_partial_tree_buffer<A: execution_prover_model::allocator::HostTraceAllocator>(
    free: &crossbeam_channel::Receiver<A>,
    pool: &Option<crossbeam_channel::Sender<A>>,
) -> Option<execution_prover_model::allocator::PooledHostBuffer<[u32; 8], A>> {
    pool.as_ref().map(|pool| {
        let allocator = free
            .recv()
            .expect("ExecutionProver host-buffer pool closed during commitment preparation");
        let capacity = allocator.capacity() / size_of::<[u32; 8]>();
        let values = Vec::with_capacity_in(capacity, allocator);
        execution_prover_model::allocator::PooledHostBuffer::new(values, pool.clone())
    })
}
