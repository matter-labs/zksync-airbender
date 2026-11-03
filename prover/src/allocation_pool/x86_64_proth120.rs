//! Proth120 on x86-64: trivial contiguous allocations (exact boxes,
//! retained by layout like the generic pool). The Proth120 backends have no
//! block-padded kernels yet, so there is nothing field-specific to place.

use super::*;
use field::Proth120;

#[derive(Clone, Default)]
pub struct X86Proth120AllocationPool {
    inner: GenericAllocationPool<Proth120, Proth120>,
}

impl X86Proth120AllocationPool {
    /// A retaining pool.
    pub fn new() -> Self {
        Self::with_retain(true)
    }
    /// `retain == false`: a trivial proxy of the global allocator.
    pub fn with_retain(retain: bool) -> Self {
        Self {
            inner: GenericAllocationPool::with_retain(retain),
        }
    }
    /// A proxy pool (nothing retained).
    pub fn proxy() -> Self {
        Self::with_retain(false)
    }
}

impl AllocationPool<Proth120, Proth120> for X86Proth120AllocationPool {
    fn alloc_base(&self, len: usize, layout: ColumnLayout) -> Buffer<Proth120> {
        self.inner.alloc_base(len, layout)
    }
    fn alloc_ext(&self, len: usize, layout: ColumnLayout) -> Buffer<Proth120> {
        self.inner.alloc_ext(len, layout)
    }
    fn give_base(&self, buffer: Buffer<Proth120>) {
        self.inner.give_base(buffer)
    }
    fn give_ext(&self, buffer: Buffer<Proth120>) {
        self.inner.give_ext(buffer)
    }
    fn alloc_raw(&self, layout: Layout) -> NonNull<u8> {
        self.inner.alloc_raw(layout)
    }
    fn give_raw(&self, ptr: NonNull<u8>, layout: Layout) {
        self.inner.give_raw(ptr, layout)
    }
    fn retained_raw(&self, layout: Layout) -> usize {
        self.inner.retained_raw(layout)
    }
    fn retains(&self) -> bool {
        self.inner.retains()
    }
    fn stats(&self) -> PoolStats {
        self.inner.stats()
    }
    fn share(&self) -> Arc<dyn AllocationPool<Proth120, Proth120>> {
        Arc::new(self.clone())
    }
}
