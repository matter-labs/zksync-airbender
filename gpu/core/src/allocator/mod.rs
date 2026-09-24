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
use std::ops::Range;
use std::panic::Location;
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use tracker::{AllocationDirection, AllocationPlacement, AllocationsTracker, UNBOUNDED};

use crate::primitives::nvtx;

fn placement_tag(placement: AllocationPlacement) -> u8 {
    match placement {
        AllocationPlacement::BestFit => 0,
        AllocationPlacement::Bottom => 1,
        AllocationPlacement::Top => 2,
    }
}

/// Correlation id shared by an allocation's alloc and free marks; the pool
/// reuses addresses, so pairing needs an id that never does.
static NEXT_MEM_ALLOCATION_ID: AtomicU64 = AtomicU64::new(1);

pub trait StaticAllocationBackend: Sized {
    fn as_non_null(&mut self) -> NonNull<u8>;
    fn len(&self) -> usize;
    #[allow(dead_code)]
    fn is_empty(&self) -> bool;
    /// NVTX memory-extension heap name for pools over this backend, or `None`
    /// to skip heap/region registration entirely. Only device pools opt in:
    /// memory tools reject (compute-sanitizer) or crash on (no CUDA context)
    /// non-device ranges.
    fn nvtx_mem_heap_name() -> Option<&'static str> {
        None
    }
}

pub struct InnerStaticAllocator<B: StaticAllocationBackend> {
    backends: Vec<B>,
    tracker: AllocationsTracker,
    log_chunk_size: u32,
    heaps: Vec<(usize, usize, nvtx::MemHeapHandle)>,
    used_counter: u64,
}

impl<B: StaticAllocationBackend> Drop for InnerStaticAllocator<B> {
    fn drop(&mut self) {
        // A carved pool owns no backend and borrows its parent's heap.
        if !self.backends.is_empty() {
            for &(_, _, heap) in &self.heaps {
                nvtx::mem_heap_unregister(heap);
            }
        }
    }
}

impl<B: StaticAllocationBackend> InnerStaticAllocator<B> {
    pub fn new(backends: impl IntoIterator<Item = B>, log_chunk_size: u32) -> Self {
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
        let used_counter = match B::nvtx_mem_heap_name() {
            Some(name) => nvtx::mem_counter_register(&format!("{name} used bytes")),
            None => 0,
        };
        let heaps = match B::nvtx_mem_heap_name() {
            Some(name) => ptrs_and_lens
                .iter()
                .map(|&(ptr, len)| {
                    let heap = nvtx::mem_heap_register(ptr.as_ptr(), len, name);
                    (ptr.as_ptr() as usize, len, heap)
                })
                .collect_vec(),
            None => Vec::new(),
        };
        Self {
            backends,
            tracker,
            log_chunk_size,
            heaps,
            used_counter,
        }
    }

    fn alloc_impl<T>(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
        alignment: usize,
        bounds: Range<usize>,
        direction: AllocationDirection,
    ) -> CudaResult<StaticAllocationData<T>> {
        let byte_len = len * size_of::<T>();
        assert!(alignment.is_power_of_two());
        assert!(alignment >= align_of::<T>());
        let alloc_granularity = (1usize << self.log_chunk_size).max(alignment);
        let alloc_len = byte_len.next_multiple_of(alloc_granularity);
        match self
            .tracker
            .alloc_aligned(alloc_len, placement, alignment, bounds, direction)
        {
            Ok(ptr) => {
                assert!(ptr.is_aligned_to(alignment));
                Ok(StaticAllocationData::new(ptr.cast::<T>(), len, alloc_len))
            }
            Err(_) => Err(CudaError::ErrorMemoryAllocation),
        }
    }

    pub fn alloc<T>(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocationData<T>> {
        self.alloc_impl::<T>(
            len,
            placement,
            align_of::<T>(),
            UNBOUNDED,
            AllocationDirection::Ascending,
        )
    }

    pub fn alloc_with_extra_alignment<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocationData<T>> {
        let extra_alignment = 1usize << EXTRA_ALIGNMENT_LOG2;
        let alignment = align_of::<T>().max(extra_alignment);
        self.alloc_impl::<T>(
            len,
            placement,
            alignment,
            UNBOUNDED,
            AllocationDirection::Ascending,
        )
    }

    pub fn free<T>(&mut self, data: StaticAllocationData<T>) {
        let ptr = data.ptr.cast::<u8>();
        let len = data.alloc_len;
        if len != 0 && self.nvtx_mem_regions_enabled() {
            nvtx::mem_region_unregister(ptr.as_ptr());
        }
        let lcs = self.log_chunk_size;
        assert_eq!(len & ((1 << lcs) - 1), 0);
        self.tracker.free(ptr, len);
    }

    fn nvtx_mem_regions_enabled(&self) -> bool {
        !self.heaps.is_empty()
    }

    // A carved pool lies inside its parent's backend range, so its
    // allocations resolve to the parent's device heap (a nested NVTX heap
    // would be rejected as overlapping).
    fn nvtx_heap_for(&self, addr: usize) -> nvtx::MemHeapHandle {
        self.heaps
            .iter()
            .find(|&&(base, len, _)| addr >= base && addr < base + len)
            .map(|&(_, _, heap)| heap)
            .unwrap_or_else(nvtx::MemHeapHandle::process_wide)
    }

    /// Reads the bytes-in-use and, when the counter series is registered,
    /// emits one sample of it.
    fn used_mem_current_sampled(&self) -> usize {
        let used = self.used_mem_current();
        if self.used_counter != 0 {
            nvtx::mem_counter_sample(self.used_counter, used as i64);
        }
        used
    }

    fn used_mem_current(&self) -> usize {
        self.tracker.get_used_mem_current()
    }
}

pub struct StaticAllocation<T, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> {
    allocator: StaticAllocator<B, W>,
    data: StaticAllocationData<T>,
    nvtx_id: u64,
    nvtx_site: &'static Location<'static>,
    nvtx_placement: u8,
    nvtx_span: nvtx::MemSpanId,
}

impl<T, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> StaticAllocation<T, B, W> {
    /// Bytes reserved from the pool, including allocator rounding. Unlike the
    /// visible element count, this is unchanged by `shrink_len_to`.
    #[doc(hidden)]
    pub fn allocated_bytes(&self) -> usize {
        self.data.alloc_len
    }

    /// Shrinks the visible element count without changing the owned allocation.
    pub fn shrink_len_to(&mut self, len: usize) {
        assert!(
            len <= self.data.len,
            "StaticAllocation::shrink_len_to cannot grow"
        );
        self.data.len = len;
    }
}

impl<T, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> Drop
    for StaticAllocation<T, B, W>
{
    fn drop(&mut self) {
        let address = self.data.ptr.cast::<u8>().as_ptr() as usize;
        let bytes = self.data.alloc_len;
        nvtx::mem_span_end(self.nvtx_span);
        let used_after = unsafe { self.allocator.free_using_data(self.data) };
        if bytes != 0 {
            nvtx::mem_mark(
                nvtx::MEM_MARK_CATEGORY_FREE,
                self.nvtx_site,
                self.nvtx_id,
                address as u64,
                bytes,
                used_after,
                self.nvtx_placement,
            );
        }
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
        f(&mut self
            .lock()
            .expect("concurrent static allocator mutex poisoned"))
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
    _parent: Option<W>,
    _phantom: PhantomData<B>,
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> StaticAllocator<B, W> {
    pub fn new(backends: impl IntoIterator<Item = B>, log_chunk_size: u32) -> Self {
        Self {
            inner: W::new(InnerStaticAllocator::new(backends, log_chunk_size)),
            log_chunk_size,
            _parent: None,
            _phantom: PhantomData,
        }
    }

    /// A pool over `byte_len` bytes taken from this allocator for as long as
    /// the pool or any of its allocations lives.
    pub fn carve(
        &self,
        byte_len: usize,
        placement: AllocationPlacement,
        log_chunk_size: u32,
    ) -> CudaResult<Self> {
        let pool = self.inner.execute(|inner| {
            let data = inner.alloc::<u8>(byte_len, placement)?;
            let addr = data.ptr.as_ptr() as usize;
            let heaps = inner
                .nvtx_mem_regions_enabled()
                .then(|| (addr, data.alloc_len, inner.nvtx_heap_for(addr)))
                .into_iter()
                .collect();
            CudaResult::Ok(InnerStaticAllocator {
                backends: Vec::new(),
                tracker: AllocationsTracker::new(&[(data.ptr, data.alloc_len)]),
                log_chunk_size,
                heaps,
                used_counter: 0,
            })
        })?;
        Ok(Self {
            inner: W::new(pool),
            log_chunk_size,
            _parent: Some(self.inner.clone()),
            _phantom: PhantomData,
        })
    }

    pub fn capacity(&self) -> usize {
        self.inner.execute(|inner| inner.tracker.capacity())
    }

    #[track_caller]
    pub fn alloc<T>(
        &self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        self.alloc_in(
            len,
            placement,
            align_of::<T>(),
            UNBOUNDED,
            AllocationDirection::Ascending,
        )
    }

    #[track_caller]
    pub fn alloc_with_extra_alignment<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        self.alloc_in(
            len,
            placement,
            align_of::<T>().max(1usize << EXTRA_ALIGNMENT_LOG2),
            UNBOUNDED,
            AllocationDirection::Ascending,
        )
    }

    #[track_caller]
    pub fn alloc_in<T>(
        &self,
        len: usize,
        placement: AllocationPlacement,
        alignment: usize,
        bounds: Range<usize>,
        direction: AllocationDirection,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        let site = Location::caller();
        let (data, used_after) = self.inner.execute(|inner| {
            let data = inner.alloc_impl::<T>(len, placement, alignment, bounds, direction)?;
            if data.alloc_len != 0 && inner.nvtx_mem_regions_enabled() {
                let ptr = data.ptr.cast::<u8>().as_ptr();
                nvtx::mem_region_register(inner.nvtx_heap_for(ptr as usize), ptr, data.alloc_len);
            }
            CudaResult::Ok((data, inner.used_mem_current_sampled()))
        })?;
        let nvtx_placement = placement_tag(placement);
        let nvtx_id = NEXT_MEM_ALLOCATION_ID.fetch_add(1, Ordering::Relaxed);
        let nvtx_span = if data.alloc_len != 0 {
            nvtx::mem_span_start(
                site,
                nvtx_id,
                data.ptr.cast::<u8>().as_ptr() as usize as u64,
                data.alloc_len,
                used_after,
                nvtx_placement,
            )
        } else {
            nvtx::MemSpanId::default()
        };
        Ok(StaticAllocation {
            allocator: self.clone(),
            data,
            nvtx_id,
            nvtx_site: site,
            nvtx_placement,
            nvtx_span,
        })
    }

    unsafe fn free_using_data<T>(&self, data: StaticAllocationData<T>) -> usize {
        self.inner.execute(|inner| {
            inner.free(data);
            inner.used_mem_current_sampled()
        })
    }

    pub fn get_used_mem_current(&self) -> usize {
        self.inner.execute(|inner| inner.used_mem_current())
    }

    pub fn reset_used_mem_peak(&self) {
        self.inner
            .execute(|inner| inner.tracker.reset_used_mem_peak())
    }
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> StaticAllocator<B, W> {
    pub fn get_used_mem_peak(&self) -> usize {
        // Conservative: the big tracker's peak reflects worst-case physical usage.
        self.inner
            .execute(|inner| inner.tracker.get_used_mem_peak())
    }
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> Clone
    for StaticAllocator<B, W>
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            log_chunk_size: self.log_chunk_size,
            _parent: self._parent.clone(),
            _phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod cpu_tests;
