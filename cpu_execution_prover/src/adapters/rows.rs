//! Borrow contiguous trace rows; copy only when the trace spans several blocks.

use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::trace::ChunkedTraceHolder;
use std::borrow::Cow;

pub(crate) fn rows<'a, T: Clone, A: HostTraceAllocator>(
    holder: &'a ChunkedTraceHolder<T, A>,
) -> Cow<'a, [T]> {
    match holder.chunks.as_slice() {
        [] => Cow::Borrowed(&[]),
        [single] => Cow::Borrowed(single.as_slice()),
        chunks => {
            let mut flattened = Vec::with_capacity(holder.len());
            for chunk in chunks {
                flattened.extend_from_slice(chunk);
            }
            Cow::Owned(flattened)
        }
    }
}
