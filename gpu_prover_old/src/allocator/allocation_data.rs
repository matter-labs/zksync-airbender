use std::marker::PhantomData;
use std::ptr::NonNull;

#[derive(Debug)]
pub(crate) struct StaticAllocationData<T> {
    pub ptr: NonNull<T>,
    pub len: usize,
    pub alloc_len: usize,
    _owns_t: PhantomData<T>,
}

impl<T> StaticAllocationData<T> {
    pub fn new(ptr: NonNull<T>, len: usize, alloc_len: usize) -> Self {
        Self {
            ptr,
            len,
            alloc_len,
            _owns_t: PhantomData,
        }
    }
}

impl<T> Clone for StaticAllocationData<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for StaticAllocationData<T> {}

unsafe impl<T> Send for StaticAllocationData<T> where Vec<T>: Send {}

unsafe impl<T> Sync for StaticAllocationData<T> where Vec<T>: Sync {}
