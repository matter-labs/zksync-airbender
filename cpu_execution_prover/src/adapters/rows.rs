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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::host_storage::CpuTraceAllocator;
    use std::sync::Arc;

    const BLOCK_BYTES: usize = 1 << 12;

    fn holder(chunk_lengths: &[usize]) -> (ChunkedTraceHolder<u32, CpuTraceAllocator>, Vec<u32>) {
        let mut expected = Vec::new();
        let mut chunks = Vec::new();
        let mut next = 0u32;
        for length in chunk_lengths {
            let allocator = CpuTraceAllocator::new(BLOCK_BYTES);
            let mut chunk = Vec::with_capacity_in(*length, allocator);
            for _ in 0..*length {
                chunk.push(next);
                expected.push(next);
                next += 1;
            }
            chunks.push(Arc::new(chunk));
        }
        (ChunkedTraceHolder { chunks }, expected)
    }

    #[test]
    fn an_empty_trace_has_no_rows() {
        let (trace, expected) = holder(&[]);
        assert!(expected.is_empty());
        let view = rows(&trace);
        assert!(view.is_empty());
    }

    #[test]
    fn a_single_chunk_is_borrowed_not_copied() {
        let (trace, expected) = holder(&[7]);
        let view = rows(&trace);
        assert_eq!(&*view, expected.as_slice());
        assert_eq!(
            view.as_ptr(),
            trace.chunks[0].as_ptr(),
            "a single chunk must not be copied"
        );
    }

    #[test]
    fn several_chunks_flatten_in_original_row_order() {
        let (trace, expected) = holder(&[4, 1, 6, 0, 2]);
        let view = rows(&trace);
        assert_ne!(view.as_ptr(), trace.chunks[0].as_ptr());
        assert_eq!(&*view, expected.as_slice());
        assert_eq!(view.len(), trace.len());
        drop(view);
        assert_eq!(trace.into_allocators().len(), 5);
    }
}
