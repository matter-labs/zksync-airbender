use crate::allocator::allocation_data::StaticAllocationData;
use crate::allocator::{
    ConcurrentInnerStaticAllocatorWrapper, InnerStaticAllocatorWrapper,
    NonConcurrentInnerStaticAllocatorWrapper, StaticAllocation, StaticAllocationBackend,
    StaticAllocator,
};
use era_cudart::memory::HostAllocation;
use fft::GoodAllocator;
use log::error;
use std::alloc::{AllocError, Allocator, Layout};
use std::fmt::{Debug, Formatter};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;
use std::slice;
use std::sync::OnceLock;

pub static STATIC_HOST_ALLOCATOR: OnceLock<ConcurrentStaticHostAllocator> = OnceLock::new();

impl StaticAllocationBackend for HostAllocation<u8> {
    fn as_non_null(&mut self) -> NonNull<u8> {
        unsafe { NonNull::new_unchecked(self.deref_mut().as_mut_ptr()) }
    }

    fn len(&self) -> usize {
        self.deref().len()
    }

    fn is_empty(&self) -> bool {
        self.deref().is_empty()
    }
}

trait InnerStaticHostAllocatorWrapper: InnerStaticAllocatorWrapper<HostAllocation<u8>> {}

type ConcurrentInnerStaticHostAllocatorWrapper =
    ConcurrentInnerStaticAllocatorWrapper<HostAllocation<u8>>;

impl InnerStaticHostAllocatorWrapper for ConcurrentInnerStaticHostAllocatorWrapper {}

type NonConcurrentInnerStaticHostAllocatorWrapper =
    NonConcurrentInnerStaticAllocatorWrapper<HostAllocation<u8>>;

impl InnerStaticHostAllocatorWrapper for NonConcurrentInnerStaticHostAllocatorWrapper {}

type StaticHostAllocator<W> = StaticAllocator<HostAllocation<u8>, W>;

pub type ConcurrentStaticHostAllocator =
    StaticHostAllocator<ConcurrentInnerStaticHostAllocatorWrapper>;

impl ConcurrentStaticHostAllocator {
    pub fn initialize_global(
        backends: impl IntoIterator<Item = HostAllocation<u8>>,
        log_chunk_size: u32,
    ) {
        let allocator = ConcurrentStaticHostAllocator::new(backends, log_chunk_size);
        assert!(STATIC_HOST_ALLOCATOR.set(allocator).is_ok());
    }

    pub fn get_global() -> &'static ConcurrentStaticHostAllocator {
        STATIC_HOST_ALLOCATOR.get().unwrap()
    }

    pub fn is_initialized_global() -> bool {
        STATIC_HOST_ALLOCATOR.get().is_some()
    }
}

pub type NonConcurrentStaticHostAllocator =
    StaticHostAllocator<NonConcurrentInnerStaticHostAllocatorWrapper>;

impl<T, W: InnerStaticHostAllocatorWrapper> Deref for StaticAllocation<T, HostAllocation<u8>, W> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        unsafe { slice::from_raw_parts(self.data.ptr.as_ptr(), self.data.len) }
    }
}

impl<T, W: InnerStaticHostAllocatorWrapper> DerefMut
    for StaticAllocation<T, HostAllocation<u8>, W>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { slice::from_raw_parts_mut(self.data.ptr.as_ptr(), self.data.len) }
    }
}

unsafe impl Allocator for ConcurrentStaticHostAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let len = layout.size();
        if let Ok(data) = self.inner.lock().unwrap().alloc(len) {
            let ptr = data.ptr;
            assert!(ptr.is_aligned_to(layout.align()));
            Ok(NonNull::slice_from_raw_parts(ptr, len))
        } else {
            error!("allocation of {len} bytes in ConcurrentStaticHostAllocator failed");
            Err(AllocError)
        }
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        let len = layout.size().next_multiple_of(1 << self.log_chunk_size);
        let data = StaticAllocationData::new(ptr, len);
        self.inner.lock().unwrap().free(data);
    }
}

impl Default for ConcurrentStaticHostAllocator {
    fn default() -> Self {
        ConcurrentStaticHostAllocator::get_global().clone()
    }
}

impl Debug for ConcurrentStaticHostAllocator {
    fn fmt(&self, _: &mut Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

impl GoodAllocator for ConcurrentStaticHostAllocator {}
