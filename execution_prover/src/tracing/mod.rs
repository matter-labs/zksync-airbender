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
pub(crate) fn take_partial_tree_allocator<A>(
    free: &crossbeam_channel::Receiver<A>,
    persist_partial_trees: bool,
) -> Option<A> {
    persist_partial_trees.then(|| {
        free.recv()
            .expect("ExecutionProver host-buffer pool closed during commitment preparation")
    })
}
