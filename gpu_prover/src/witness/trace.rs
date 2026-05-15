use fft::GoodAllocator;
use std::sync::Arc;

#[derive(Clone)]
pub(crate) struct ChunkedTraceHolder<T, A: GoodAllocator> {
    pub chunks: Vec<Arc<Vec<T, A>>>,
}

impl<T, A: GoodAllocator> ChunkedTraceHolder<T, A> {
    pub fn len(&self) -> usize {
        self.chunks.iter().map(|chunk| chunk.len()).sum()
    }

    pub fn into_allocators(self) -> Vec<A> {
        self.chunks
            .into_iter()
            .map(|c| {
                Arc::into_inner(c)
                    .expect(
                        "ChunkedTraceHolder::into_allocators requires unique Arc ownership per chunk",
                    )
                    .allocator()
                    .clone()
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::Global;

    #[test]
    #[should_panic(
        expected = "ChunkedTraceHolder::into_allocators requires unique Arc ownership per chunk"
    )]
    fn into_allocators_names_arc_uniqueness_invariant() {
        let chunk = Arc::new(Vec::<u8, Global>::new_in(Global));
        let holder = ChunkedTraceHolder {
            chunks: vec![Arc::clone(&chunk), chunk],
        };

        let _ = holder.into_allocators();
    }
}
