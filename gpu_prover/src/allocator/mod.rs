mod allocation_data;
pub(crate) mod device;
pub(crate) mod host;
pub(crate) mod tracker;

use allocation_data::StaticAllocationData;
use era_cudart::result::CudaResult;
use era_cudart_sys::CudaError;
use itertools::Itertools;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use tracker::{AllocationPlacement, AllocationsTracker};

pub(crate) trait StaticAllocationBackend: Sized {
    fn as_non_null(&mut self) -> NonNull<u8>;
    fn len(&self) -> usize;
    #[allow(dead_code)]
    fn is_empty(&self) -> bool;
}

struct SmallAllocator {
    tracker: AllocationsTracker,
    log_chunk_size: u32,
    small_threshold: usize,
    backing_addr: usize,
    backing_len: usize,
}

impl SmallAllocator {
    fn owns(&self, addr: usize) -> bool {
        addr >= self.backing_addr && addr < self.backing_addr + self.backing_len
    }
}

pub(crate) struct InnerStaticAllocator<B: StaticAllocationBackend> {
    _backends: Vec<B>,
    tracker: AllocationsTracker,
    log_chunk_size: u32,
    small: Option<SmallAllocator>,
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
            small: None,
        }
    }

    pub(crate) fn new_with_small_allocator(
        backends: impl IntoIterator<Item = B>,
        log_chunk_size: u32,
        small_log_chunk_size: u32,
        small_pool_size: usize,
    ) -> Self {
        assert!(
            small_log_chunk_size < log_chunk_size,
            "small chunk size must be smaller than big chunk size"
        );
        assert!(
            small_pool_size > 0 && small_pool_size & ((1 << log_chunk_size) - 1) == 0,
            "small pool size must be a positive multiple of the big chunk size"
        );
        let mut alloc = Self::new(backends, log_chunk_size);
        let small_threshold = 1usize << (log_chunk_size - 2);
        let backing_ptr = alloc
            .tracker
            .alloc_aligned(small_pool_size, AllocationPlacement::Bottom, 1)
            .expect("not enough memory to carve out the small allocator pool");
        let backing_addr = backing_ptr.as_ptr() as usize;
        let small_tracker = AllocationsTracker::new(&[(backing_ptr, small_pool_size)]);
        alloc.small = Some(SmallAllocator {
            tracker: small_tracker,
            log_chunk_size: small_log_chunk_size,
            small_threshold,
            backing_addr,
            backing_len: small_pool_size,
        });
        alloc
    }

    fn alloc_impl<T>(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
        alignment: usize,
    ) -> CudaResult<StaticAllocationData<T>> {
        let size_of_t = size_of::<T>();
        let byte_len = len * size_of_t;
        assert!(alignment.is_power_of_two());
        assert!(alignment >= align_of::<T>());

        if let Some(ref mut small) = self.small {
            if byte_len > 0 && byte_len <= small.small_threshold {
                let slcs = small.log_chunk_size;
                let alloc_granularity = (1usize << slcs).max(alignment);
                let alloc_len = byte_len.next_multiple_of(alloc_granularity);
                match small.tracker.alloc_aligned(alloc_len, placement, alignment) {
                    Ok(ptr) => {
                        assert!(ptr.is_aligned_to(alignment));
                        let ptr = ptr.cast::<T>();
                        return Ok(StaticAllocationData::new(ptr, len, alloc_len));
                    }
                    Err(_) => return Err(CudaError::ErrorMemoryAllocation),
                }
            }
        }

        let lcs = self.log_chunk_size;
        let alloc_granularity = (1 << lcs).max(alignment);
        let alloc_len = byte_len.next_multiple_of(alloc_granularity);
        match self.tracker.alloc_aligned(alloc_len, placement, alignment) {
            Ok(ptr) => {
                assert!(ptr.is_aligned_to(alignment));
                let ptr = ptr.cast::<T>();
                let data = StaticAllocationData::new(ptr, len, alloc_len);
                Ok(data)
            }
            Err(_) => Err(CudaError::ErrorMemoryAllocation),
        }
    }

    pub(crate) fn alloc<T>(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocationData<T>> {
        self.alloc_impl::<T>(len, placement, align_of::<T>())
    }

    pub(crate) fn alloc_with_extra_alignment<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocationData<T>> {
        let extra_alignment = 1usize << EXTRA_ALIGNMENT_LOG2;
        let alignment = align_of::<T>().max(extra_alignment);
        self.alloc_impl::<T>(len, placement, alignment)
    }

    pub(crate) fn free<T>(&mut self, data: StaticAllocationData<T>) {
        let ptr = data.ptr.cast::<u8>();
        let len = data.alloc_len;
        let addr = ptr.as_ptr() as usize;

        if let Some(ref mut small) = self.small {
            if small.owns(addr) {
                let slcs = small.log_chunk_size;
                assert_eq!(len & ((1 << slcs) - 1), 0);
                small.tracker.free(ptr, len);
                return;
            }
        }

        let lcs = self.log_chunk_size;
        assert_eq!(len & ((1 << lcs) - 1), 0);
        self.tracker.free(ptr, len);
    }
}

pub(crate) struct StaticAllocation<T, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>>
{
    allocator: StaticAllocator<B, W>,
    data: StaticAllocationData<T>,
}

impl<T, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> Drop
    for StaticAllocation<T, B, W>
{
    fn drop(&mut self) {
        unsafe { self.allocator.free_using_data(self.data) }
    }
}

pub(crate) trait InnerStaticAllocatorWrapper<B: StaticAllocationBackend>: Clone {
    fn new(inner_static_allocator: InnerStaticAllocator<B>) -> Self;
    fn execute<R>(&self, f: impl FnOnce(&mut InnerStaticAllocator<B>) -> R) -> R;
}

pub(crate) type ConcurrentInnerStaticAllocatorWrapper<B> = Arc<Mutex<InnerStaticAllocator<B>>>;

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

pub(crate) type NonConcurrentInnerStaticAllocatorWrapper<B> = Rc<RefCell<InnerStaticAllocator<B>>>;

impl<B: StaticAllocationBackend> InnerStaticAllocatorWrapper<B>
    for NonConcurrentInnerStaticAllocatorWrapper<B>
{
    fn new(inner_static_allocator: InnerStaticAllocator<B>) -> Self {
        Rc::new(RefCell::new(inner_static_allocator))
    }

    fn execute<R>(&self, f: impl FnOnce(&mut InnerStaticAllocator<B>) -> R) -> R {
        match self.try_borrow_mut() {
            Ok(mut inner) => f(&mut inner),
            Err(err) => {
                panic!(
                    "non-concurrent allocator re-entered on the wrong thread or from overlapping ownership: {err}\n{}",
                    std::backtrace::Backtrace::force_capture()
                );
            }
        }
    }
}

pub(crate) struct StaticAllocator<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> {
    inner: W,
    log_chunk_size: u32,
    _phantom: PhantomData<B>,
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> StaticAllocator<B, W> {
    fn with_wrapper(inner: W, log_chunk_size: u32) -> Self {
        Self {
            inner,
            log_chunk_size,
            _phantom: Default::default(),
        }
    }

    pub fn new(backends: impl IntoIterator<Item = B>, log_chunk_size: u32) -> Self {
        let allocator = InnerStaticAllocator::new(backends, log_chunk_size);
        let inner = W::new(allocator);
        Self::with_wrapper(inner, log_chunk_size)
    }

    pub fn new_with_small_allocator(
        backends: impl IntoIterator<Item = B>,
        log_chunk_size: u32,
        small_log_chunk_size: u32,
        small_pool_size: usize,
    ) -> Self {
        let allocator = InnerStaticAllocator::new_with_small_allocator(
            backends,
            log_chunk_size,
            small_log_chunk_size,
            small_pool_size,
        );
        let inner = W::new(allocator);
        Self::with_wrapper(inner, log_chunk_size)
    }

    pub fn capacity(&self) -> usize {
        self.inner.execute(|inner| inner.tracker.capacity())
    }

    pub fn alloc<T>(
        &self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        self.inner
            .execute(|inner| inner.alloc::<T>(len, placement))
            .map(|data| StaticAllocation {
                allocator: self.clone(),
                data,
            })
    }

    pub fn alloc_with_extra_alignment<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        self.inner
            .execute(|inner| {
                inner.alloc_with_extra_alignment::<T, EXTRA_ALIGNMENT_LOG2>(len, placement)
            })
            .map(|data| StaticAllocation {
                allocator: self.clone(),
                data,
            })
    }

    unsafe fn free_using_data<T>(&self, data: StaticAllocationData<T>) {
        self.inner.execute(|inner| inner.free(data))
    }

    pub fn get_used_mem_current(&self) -> usize {
        self.inner.execute(|inner| {
            let big_used = inner.tracker.get_used_mem_current();
            match &inner.small {
                Some(small) => {
                    // big_used includes the backing pool as "used".
                    // Correct by replacing the pool's total size with its actual usage.
                    big_used - small.backing_len + small.tracker.get_used_mem_current()
                }
                None => big_used,
            }
        })
    }

    pub(crate) fn reset_used_mem_peak(&self) {
        self.inner
            .execute(|inner| inner.tracker.reset_used_mem_peak())
    }
}

#[cfg(test)]
impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> StaticAllocator<B, W> {
    pub(crate) fn get_used_mem_peak(&self) -> usize {
        // Conservative: the big tracker's peak reflects worst-case physical usage.
        self.inner
            .execute(|inner| inner.tracker.get_used_mem_peak())
    }
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> Clone
    for StaticAllocator<B, W>
{
    fn clone(&self) -> Self {
        Self::with_wrapper(self.inner.clone(), self.log_chunk_size)
    }
}

#[cfg(test)]
mod tests;
