//! Chunked host rows -> the contiguous slice the CPU primitives take.
//!
//! A single-chunk trace — the common case — is borrowed as-is; only a genuinely
//! multi-chunk trace is copied, and only for the request being served.
//!
//! What this must never do is take ownership of a chunk. The chunk `Arc`s are
//! the producer's credits: `ChunkedTraceHolder::into_allocators` returns them
//! only while each `Arc` is unique, so an adapter that kept one alive past the
//! completion would turn a returned credit into a panic.

use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::trace::ChunkedTraceHolder;
use std::ops::Deref;

/// One circuit's rows as a contiguous slice. Because the view borrows the
/// holder, the borrow checker is what guarantees `Flattened`'s scratch is gone
/// before the holder can be moved into a completion.
pub(crate) enum RowsView<'a, T> {
    Borrowed(&'a [T]),
    Flattened(Vec<T>),
}

impl<T> Deref for RowsView<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Borrowed(rows) => rows,
            Self::Flattened(rows) => rows,
        }
    }
}

impl<T> RowsView<'_, T> {
    #[cfg(test)]
    pub(crate) fn is_borrowed(&self) -> bool {
        matches!(self, Self::Borrowed(_))
    }
}

/// Borrow a trace's rows, copying only when it spans several blocks.
pub(crate) fn rows<'a, T: Clone, A: HostTraceAllocator>(
    holder: &'a ChunkedTraceHolder<T, A>,
) -> RowsView<'a, T> {
    match holder.chunks.as_slice() {
        [] => RowsView::Borrowed(&[]),
        [single] => RowsView::Borrowed(single.as_slice()),
        chunks => {
            let mut flattened = Vec::with_capacity(holder.len());
            for chunk in chunks {
                flattened.extend_from_slice(chunk);
            }
            RowsView::Flattened(flattened)
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
        assert!(view.is_borrowed());
    }

    #[test]
    fn a_single_chunk_is_borrowed_not_copied() {
        let (trace, expected) = holder(&[7]);
        let view = rows(&trace);
        assert!(view.is_borrowed(), "a single chunk must not be copied");
        assert_eq!(&*view, expected.as_slice());
        assert_eq!(view.as_ptr(), trace.chunks[0].as_ptr());
    }

    #[test]
    fn a_partial_chunk_keeps_its_length() {
        let (trace, expected) = holder(&[3]);
        assert_eq!(rows(&trace).len(), 3);
        assert_eq!(&*rows(&trace), expected.as_slice());
    }

    #[test]
    fn several_chunks_flatten_in_original_row_order() {
        let (trace, expected) = holder(&[4, 1, 6, 0, 2]);
        let view = rows(&trace);
        assert!(!view.is_borrowed());
        assert_eq!(&*view, expected.as_slice());
        assert_eq!(view.len(), trace.len());
    }

    #[test]
    fn adapter_scratch_releases_every_block() {
        let (trace, _) = holder(&[4, 5]);
        let view = rows(&trace);
        assert_eq!(view.len(), 9);
        drop(view);
        assert_eq!(trace.into_allocators().len(), 2);
    }

    #[test]
    #[should_panic(
        expected = "ChunkedTraceHolder::into_allocators requires unique Arc ownership per chunk"
    )]
    fn a_retained_chunk_trips_the_uniqueness_guard() {
        let (trace, _) = holder(&[4, 5]);
        let retained = Arc::clone(&trace.chunks[0]);
        let _ = trace.into_allocators();
        drop(retained);
    }
}
