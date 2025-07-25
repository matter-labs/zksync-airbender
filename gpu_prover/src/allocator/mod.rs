mod allocation_data;
pub mod device;
pub mod host;
pub mod tracker;

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
use tracker::{AllocationPlacement, AllocationsTracker};

pub trait StaticAllocationBackend: Sized {
    fn as_non_null(&mut self) -> NonNull<u8>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}

pub struct InnerStaticAllocator<B: StaticAllocationBackend> {
    _backends: Vec<B>,
    tracker: AllocationsTracker,
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
        let tracker = AllocationsTracker::new(&ptrs_and_lens);
        Self {
            _backends: backends,
            tracker,
            log_chunk_size,
        }
    }

    pub(crate) fn alloc<T>(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocationData<T>> {
        let size_of_t = size_of::<T>();
        let lcs = self.log_chunk_size;
        let alloc_len = (len * size_of_t).next_multiple_of(1 << lcs);
        match self.tracker.alloc(alloc_len, placement) {
            Ok(ptr) => {
                assert!(ptr.is_aligned_to(align_of::<T>()));
                let ptr = ptr.cast::<T>();
                let data = StaticAllocationData::new(ptr, len, alloc_len);
                Ok(data)
            }
            Err(_) => Err(CudaError::ErrorMemoryAllocation),
        }
    }

    pub(crate) fn free<T>(&mut self, data: StaticAllocationData<T>) {
        let lcs = self.log_chunk_size;
        let ptr = data.ptr.cast::<u8>();
        let len = data.alloc_len;
        assert_eq!(len & ((1 << lcs) - 1), 0);
        self.tracker.free(ptr, len);
    }
}

pub struct StaticAllocation<T, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> {
    allocator: StaticAllocator<B, W>,
    data: StaticAllocationData<T>,
}

impl<T, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> StaticAllocation<T, B, W> {
    pub fn alloc(
        len: usize,
        placement: AllocationPlacement,
        allocator: &mut StaticAllocator<B, W>,
    ) -> CudaResult<Self> {
        allocator.alloc(len, placement)
    }

    pub fn free(self) {
        drop(self)
    }
}

impl<T, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> Drop
    for StaticAllocation<T, B, W>
{
    fn drop(&mut self) {
        unsafe { self.allocator.free_using_data(self.data) }
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

    pub fn alloc<T>(
        &self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        self.inner
            .execute(|inner| inner.alloc(len, placement))
            .map(|data| StaticAllocation {
                allocator: self.clone(),
                data,
            })
    }

    pub fn free<T>(&self, allocation: StaticAllocation<T, B, W>) {
        unsafe { self.free_using_data(allocation.data) };
        forget(allocation);
    }

    unsafe fn free_using_data<T>(&self, data: StaticAllocationData<T>) {
        self.inner.execute(|inner| inner.free(data))
    }

    pub fn log_chunk_size(&self) -> u32 {
        self.log_chunk_size
    }

    pub fn get_used_mem_current(&self) -> usize {
        self.inner
            .execute(|inner| inner.tracker.get_used_mem_current())
    }

    pub(crate) fn get_used_mem_peak(&self) -> usize {
        self.inner
            .execute(|inner| inner.tracker.get_used_mem_peak())
    }

    pub(crate) fn reset_used_mem_peak(&self) {
        self.inner
            .execute(|inner| inner.tracker.reset_used_mem_peak())
    }
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> Clone
    for StaticAllocator<B, W>
{
    fn clone(&self) -> Self {
        Self::from_inner(self.inner.clone(), self.log_chunk_size)
    }
}
