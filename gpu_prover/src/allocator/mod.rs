mod allocation_data;
pub mod device;
pub mod host;
mod tracker;

use allocation_data::StaticAllocationData;
use era_cudart::result::CudaResult;
use era_cudart_sys::CudaError;
use itertools::Itertools;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::mem::forget;
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use tracker::StaticAllocationsTracker;

pub trait StaticAllocationBackend: Sized {
    fn as_non_null(&mut self) -> NonNull<u8>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}

pub struct InnerStaticAllocator<B: StaticAllocationBackend> {
    _backends: Vec<B>,
    tracker: StaticAllocationsTracker,
    log_chunk_size: u32,
}

impl<B: StaticAllocationBackend> InnerStaticAllocator<B> {
    pub(crate) fn new(backends: impl IntoIterator<Item = B>, log_chunk_size: u32) -> Self {
        let mut backends: Vec<B> = backends.into_iter().collect();
        let ptrs_and_lens = backends
            .iter_mut()
            .map(|backend| {
                let ptr = backend.as_non_null();
                let len = backend.len();
                assert_ne!(len, 0);
                assert!(len.trailing_zeros() >= log_chunk_size);
                (ptr, len)
            })
            .collect_vec();
        let tracker = StaticAllocationsTracker::new(&ptrs_and_lens);
        Self {
            _backends: backends,
            tracker,
            log_chunk_size,
        }
    }

    pub(crate) fn alloc<T>(&mut self, len: usize) -> CudaResult<StaticAllocationData<T>> {
        let size_of_t = size_of::<T>();
        let lcs = self.log_chunk_size;
        let alloc_len = (len * size_of_t).next_multiple_of(1 << lcs);
        match self.tracker.alloc(alloc_len) {
            Ok(ptr) => {
                assert!(ptr.is_aligned_to(align_of::<T>()));
                let ptr = ptr.cast::<T>();
                let len = alloc_len / size_of_t;
                let data = StaticAllocationData::new(ptr, len);
                Ok(data)
            }
            Err(_) => Err(CudaError::ErrorMemoryAllocation),
        }
    }

    pub(crate) fn free<T>(&mut self, data: StaticAllocationData<T>) {
        let lcs = self.log_chunk_size;
        let ptr = data.ptr.cast::<u8>();
        let len = data.len * size_of::<T>();
        assert_eq!(len & ((1 << lcs) - 1), 0);
        self.tracker.free(ptr, len);
    }
}

pub struct StaticAllocation<T, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> {
    allocator: StaticAllocator<B, W>,
    data: StaticAllocationData<T>,
}

impl<T, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> StaticAllocation<T, B, W> {
    pub fn alloc(len: usize, allocator: &mut StaticAllocator<B, W>) -> CudaResult<Self> {
        allocator.alloc(len)
    }

    pub fn free(self) {
        drop(self)
    }
}

impl<T, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> Drop
    for StaticAllocation<T, B, W>
{
    fn drop(&mut self) {
        let data = StaticAllocationData::new(self.data.ptr, self.data.len);
        unsafe { self.allocator.free_using_data(data) }
    }
}

pub trait InnerStaticAllocatorWrapper<B: StaticAllocationBackend>: Clone {
    fn new(inner_static_allocator: InnerStaticAllocator<B>) -> Self;
    fn execute<R>(&self, f: impl FnOnce(&mut InnerStaticAllocator<B>) -> R) -> R;
}

pub type ConcurrentInnerStaticAllocatorWrapper<B> = Arc<Mutex<InnerStaticAllocator<B>>>;

impl<B: StaticAllocationBackend> InnerStaticAllocatorWrapper<B>
    for ConcurrentInnerStaticAllocatorWrapper<B>
{
    fn new(inner_static_allocator: InnerStaticAllocator<B>) -> Self {
        Arc::new(Mutex::new(inner_static_allocator))
    }

    fn execute<R>(&self, f: impl FnOnce(&mut InnerStaticAllocator<B>) -> R) -> R {
        f(&mut self.lock().unwrap())
    }
}

pub type NonConcurrentInnerStaticAllocatorWrapper<B> = Rc<RefCell<InnerStaticAllocator<B>>>;

impl<B: StaticAllocationBackend> InnerStaticAllocatorWrapper<B>
    for NonConcurrentInnerStaticAllocatorWrapper<B>
{
    fn new(inner_static_allocator: InnerStaticAllocator<B>) -> Self {
        Rc::new(RefCell::new(inner_static_allocator))
    }

    fn execute<R>(&self, f: impl FnOnce(&mut InnerStaticAllocator<B>) -> R) -> R {
        f(&mut self.borrow_mut())
    }
}

pub struct StaticAllocator<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> {
    inner: W,
    log_chunk_size: u32,
    _phantom: PhantomData<B>,
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> StaticAllocator<B, W> {
    fn from_inner(inner: W, log_chunk_size: u32) -> Self {
        Self {
            inner,
            log_chunk_size,
            _phantom: Default::default(),
        }
    }

    pub fn new(backends: impl IntoIterator<Item = B>, log_chunk_size: u32) -> Self {
        let allocator = InnerStaticAllocator::new(backends, log_chunk_size);
        let inner = W::new(allocator);
        Self::from_inner(inner, log_chunk_size)
    }

    pub fn alloc<T>(&self, len: usize) -> CudaResult<StaticAllocation<T, B, W>> {
        self.inner
            .execute(|inner| inner.alloc(len))
            .map(|data| StaticAllocation {
                allocator: self.clone(),
                data,
            })
    }

    pub fn free<T>(&self, allocation: StaticAllocation<T, B, W>) {
        let data = StaticAllocationData::new(allocation.data.ptr, allocation.data.len);
        forget(allocation);
        unsafe { self.free_using_data(data) };
    }

    unsafe fn free_using_data<T>(&self, data: StaticAllocationData<T>) {
        self.inner.execute(|inner| inner.free(data))
    }

    pub fn log_chunk_size(&self) -> u32 {
        self.log_chunk_size
    }
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> Clone
    for StaticAllocator<B, W>
{
    fn clone(&self) -> Self {
        Self::from_inner(self.inner.clone(), self.log_chunk_size)
    }
}
