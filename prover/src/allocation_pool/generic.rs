//! The field- and target-agnostic pool: every request is one exact
//! contiguous box (`storage_len` elements for a padded request), retained
//! by its layout. It is the pool of Apple Silicon / aarch64 builds and the
//! one the pool-less prover entries create on every target; it promises no
//! alignment beyond the element's, so it serves no kernel that needs the
//! block-padded layout of a specific pool.

use super::*;
use core::marker::PhantomData;

pub struct GenericAllocationPool<F, E> {
    store: Arc<RetainedStore>,
    _marker: PhantomData<fn() -> (F, E)>,
}

impl<F, E> Clone for GenericAllocationPool<F, E> {
    fn clone(&self) -> Self {
        Self {
            store: Arc::clone(&self.store),
            _marker: PhantomData,
        }
    }
}

impl<F, E> GenericAllocationPool<F, E> {
    /// A retaining pool.
    pub fn new() -> Self {
        Self::with_retain(true)
    }
    /// `retain == false`: a trivial proxy of the global allocator.
    pub fn with_retain(retain: bool) -> Self {
        Self {
            store: Arc::new(RetainedStore::new(retain)),
            _marker: PhantomData,
        }
    }
    /// A proxy pool (nothing retained).
    pub fn proxy() -> Self {
        Self::with_retain(false)
    }
    /// Handles sharing one underlying pool.
    pub fn shares_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.store, &other.store)
    }

    fn alloc<T>(&self, len: usize, layout: ColumnLayout) -> Buffer<T> {
        let requested_len = layout.storage_len(len);
        let l = Layout::array::<MaybeUninit<T>>(requested_len).unwrap();
        if l.size() == 0 {
            return Buffer::from_parts(Box::new_uninit_slice(requested_len), 0, requested_len);
        }
        let ptr = self.store.alloc(l);
        Buffer::from_parts(
            unsafe { box_from_raw(ptr, requested_len) },
            0,
            requested_len,
        )
    }

    fn give<T>(&self, buffer: Buffer<T>) {
        let (ptr, layout) = raw_from_box(buffer.into_box());
        self.store.give(ptr, layout);
    }
}

impl<F, E> Default for GenericAllocationPool<F, E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: 'static, E: 'static> AllocationPool<F, E> for GenericAllocationPool<F, E> {
    fn alloc_base(&self, len: usize, layout: ColumnLayout) -> Buffer<F> {
        self.alloc::<F>(len, layout)
    }
    fn alloc_ext(&self, len: usize, layout: ColumnLayout) -> Buffer<E> {
        self.alloc::<E>(len, layout)
    }
    fn give_base(&self, buffer: Buffer<F>) {
        self.give(buffer)
    }
    fn give_ext(&self, buffer: Buffer<E>) {
        self.give(buffer)
    }
    fn alloc_raw(&self, layout: Layout) -> NonNull<u8> {
        self.store.alloc(layout)
    }
    fn give_raw(&self, ptr: NonNull<u8>, layout: Layout) {
        self.store.give(ptr, layout)
    }
    fn retained_raw(&self, layout: Layout) -> usize {
        self.store.retained(layout)
    }
    fn retains(&self) -> bool {
        self.store.retains()
    }
    fn stats(&self) -> PoolStats {
        self.store.stats()
    }
    fn share(&self) -> Arc<dyn AllocationPool<F, E>> {
        Arc::new(self.clone())
    }
}
