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

pub struct InnerStaticAllocator<B: StaticAllocationBackend> {
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
        Self::from_inner(inner, log_chunk_size)
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

    pub(crate) fn get_used_mem_peak(&self) -> usize {
        // Conservative: the big tracker's peak reflects worst-case physical usage.
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

#[cfg(test)]
mod tests {
    use super::*;

    struct TestBackend(Vec<u8>);

    impl StaticAllocationBackend for TestBackend {
        fn as_non_null(&mut self) -> NonNull<u8> {
            NonNull::new(self.0.as_mut_ptr()).unwrap()
        }
        fn len(&self) -> usize {
            self.0.len()
        }
        fn is_empty(&self) -> bool {
            self.0.is_empty()
        }
    }

    // big log_chunk_size = 10 (1024 bytes), small = 4 (16 bytes)
    const BIG_LCS: u32 = 10;
    const SMALL_LCS: u32 = 4;
    const BIG_CHUNK: usize = 1 << BIG_LCS; // 1024
    const SMALL_CHUNK: usize = 1 << SMALL_LCS; // 16
                                               // threshold = 1 << (10 - 2) = 256
    const THRESHOLD: usize = 1 << (BIG_LCS - 2);

    fn make_allocator(
        num_big_chunks: usize,
        small_pool_chunks: usize,
    ) -> InnerStaticAllocator<TestBackend> {
        let total = num_big_chunks * BIG_CHUNK;
        let backend = TestBackend(vec![0u8; total]);
        let pool_size = small_pool_chunks * BIG_CHUNK;
        InnerStaticAllocator::new_with_small_allocator([backend], BIG_LCS, SMALL_LCS, pool_size)
    }

    fn make_allocator_no_small(num_big_chunks: usize) -> InnerStaticAllocator<TestBackend> {
        let total = num_big_chunks * BIG_CHUNK;
        let backend = TestBackend(vec![0u8; total]);
        InnerStaticAllocator::new([backend], BIG_LCS)
    }

    #[test]
    fn small_alloc_basic_roundtrip() {
        let mut alloc = make_allocator(4, 1);
        // Allocate 1 u64 = 8 bytes, below threshold (256), should go to small allocator
        let data = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
        assert_eq!(data.len, 1);
        // alloc_len should be rounded to small chunk size (16), not big (1024)
        assert_eq!(data.alloc_len, SMALL_CHUNK);
        alloc.free(data);
    }

    #[test]
    fn small_alloc_reuse_after_free() {
        let mut alloc = make_allocator(4, 1);
        let data1 = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
        let ptr1 = data1.ptr;
        alloc.free(data1);
        let data2 = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
        let ptr2 = data2.ptr;
        // Should reuse the same address after free
        assert_eq!(ptr1, ptr2);
        alloc.free(data2);
    }

    #[test]
    fn big_alloc_bypasses_small() {
        let mut alloc = make_allocator(4, 1);
        // Allocate above threshold: 33 u64s = 264 bytes > 256 threshold
        let data = alloc
            .alloc::<u64>(33, AllocationPlacement::BestFit)
            .unwrap();
        // alloc_len should be rounded to big chunk size (1024)
        assert_eq!(data.alloc_len, BIG_CHUNK);
        alloc.free(data);
    }

    #[test]
    fn free_routes_correctly_mixed() {
        let mut alloc = make_allocator(4, 1);
        // Small allocation
        let small = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
        // Big allocation
        let big = alloc
            .alloc::<u64>(33, AllocationPlacement::BestFit)
            .unwrap();
        // Free in reverse order — should not panic
        alloc.free(big);
        alloc.free(small);
    }

    #[test]
    fn usage_counters_correct() {
        let mut alloc = make_allocator(4, 1);
        // 1 big chunk is reserved for small pool, so big tracker has 4 chunks used (pool=1)
        // Initial: big_used = 1 chunk (pool), small_used = 0
        // get_used_mem_current = big_used - backing_len + small_used = 1024 - 1024 + 0 = 0
        assert_eq!(
            alloc.tracker.get_used_mem_current() - BIG_CHUNK
                + alloc.small.as_ref().unwrap().tracker.get_used_mem_current(),
            0
        );

        // Allocate a small item (8 bytes → 16 bytes rounded)
        let small = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
        let big_used = alloc.tracker.get_used_mem_current();
        let small_used = alloc.small.as_ref().unwrap().tracker.get_used_mem_current();
        // big_used still = 1024 (the pool chunk), small_used = 16
        assert_eq!(big_used, BIG_CHUNK);
        assert_eq!(small_used, SMALL_CHUNK);
        // Effective = 1024 - 1024 + 16 = 16
        assert_eq!(big_used - BIG_CHUNK + small_used, SMALL_CHUNK);

        alloc.free(small);
    }

    #[test]
    fn threshold_boundary() {
        let mut alloc = make_allocator(4, 1);
        // Exactly at threshold: 32 u64s = 256 bytes = threshold → small
        let at = alloc
            .alloc::<u64>(32, AllocationPlacement::BestFit)
            .unwrap();
        assert!(at.alloc_len < BIG_CHUNK); // went to small allocator
        alloc.free(at);

        // One byte over: 33 u64s = 264 bytes > threshold → big
        let over = alloc
            .alloc::<u64>(33, AllocationPlacement::BestFit)
            .unwrap();
        assert_eq!(over.alloc_len, BIG_CHUNK); // went to big allocator
        alloc.free(over);
    }

    #[test]
    fn small_pool_oom() {
        // 1 big chunk = 1024 bytes for small pool, small chunk = 16 bytes → 64 small slots
        let mut alloc = make_allocator(4, 1);
        let mut allocs = Vec::new();
        // Fill the pool
        for _ in 0..64 {
            allocs.push(alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap());
        }
        // Next small alloc should fail
        let result = alloc.alloc::<u64>(1, AllocationPlacement::BestFit);
        assert!(result.is_err());
        // Free all
        for a in allocs {
            alloc.free(a);
        }
    }

    #[test]
    fn disabled_small_allocator_identical_behavior() {
        let mut alloc = make_allocator_no_small(4);
        assert!(alloc.small.is_none());
        // Small allocation goes to big tracker, rounded to 1024
        let data = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
        assert_eq!(data.alloc_len, BIG_CHUNK);
        alloc.free(data);
    }

    #[test]
    fn zero_length_alloc_goes_to_big() {
        let mut alloc = make_allocator(4, 1);
        // Zero-length allocs bypass the small allocator (byte_len == 0)
        let data = alloc.alloc::<u64>(0, AllocationPlacement::BestFit).unwrap();
        assert_eq!(data.alloc_len, 0);
        alloc.free(data);
    }

    #[test]
    fn many_small_allocs_different_placements() {
        let mut alloc = make_allocator(4, 1);
        let bottom = alloc.alloc::<u64>(1, AllocationPlacement::Bottom).unwrap();
        let top = alloc.alloc::<u64>(1, AllocationPlacement::Top).unwrap();
        let best = alloc.alloc::<u64>(1, AllocationPlacement::BestFit).unwrap();
        // All should be in small allocator range, with distinct addresses
        let small = alloc.small.as_ref().unwrap();
        assert!(small.owns(bottom.ptr.as_ptr() as usize));
        assert!(small.owns(top.ptr.as_ptr() as usize));
        assert!(small.owns(best.ptr.as_ptr() as usize));
        assert_ne!(bottom.ptr, top.ptr);
        assert_ne!(bottom.ptr, best.ptr);
        alloc.free(bottom);
        alloc.free(top);
        alloc.free(best);
    }

    #[test]
    #[should_panic(expected = "small chunk size must be smaller than big chunk size")]
    fn small_chunk_size_must_be_smaller() {
        let backend = TestBackend(vec![0u8; 4 * BIG_CHUNK]);
        InnerStaticAllocator::new_with_small_allocator([backend], BIG_LCS, BIG_LCS, BIG_CHUNK);
    }

    #[test]
    #[should_panic(expected = "small pool size must be a positive multiple of the big chunk size")]
    fn pool_size_must_be_multiple() {
        let backend = TestBackend(vec![0u8; 4 * BIG_CHUNK]);
        InnerStaticAllocator::new_with_small_allocator(
            [backend],
            BIG_LCS,
            SMALL_LCS,
            BIG_CHUNK + 1,
        );
    }
}
