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

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, index: usize) -> T
    where
        T: Copy,
    {
        let mut current_index = index;
        for chunk in self.chunks.iter() {
            if current_index < chunk.len() {
                return chunk[current_index];
            } else {
                current_index -= chunk.len();
            }
        }
        panic!("Index out of bounds");
    }

    pub fn get_allocators_count(&self) -> usize {
        self.chunks.len()
    }

    pub fn into_allocators(self) -> Vec<A> {
        self.chunks
            .into_iter()
            .map(|c| Arc::into_inner(c).unwrap().allocator().clone())
            .collect()
    }
}
