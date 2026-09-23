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
use tracker::{AllocationPlacement, AllocationsTracker};

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

pub fn is_small_allocation(byte_len: usize, log_chunk_size: u32) -> bool {
    byte_len > 0 && byte_len <= 1usize << (log_chunk_size - 2)
}

pub struct InnerStaticAllocator<B: StaticAllocationBackend> {
    _backends: Vec<B>,
    tracker: AllocationsTracker,
    log_chunk_size: u32,
    heaps: Vec<(usize, usize, nvtx::MemHeapHandle)>,
    owns_heaps: bool,
    used_counter: u64,
}

impl<B: StaticAllocationBackend> Drop for InnerStaticAllocator<B> {
    fn drop(&mut self) {
        if self.owns_heaps {
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
            _backends: backends,
            tracker,
            log_chunk_size,
            heaps,
            owns_heaps: true,
            used_counter,
        }
    }

    fn new_carved(
        region: NonNull<u8>,
        len: usize,
        log_chunk_size: u32,
        parent_heap: Option<nvtx::MemHeapHandle>,
    ) -> Self {
        assert!(
            len > 0 && len.trailing_zeros() >= log_chunk_size,
            "carved pool must be a positive multiple of its chunk size"
        );
        let tracker = AllocationsTracker::new(&[(region, len)]);
        let heaps = parent_heap
            .map(|heap| vec![(region.as_ptr() as usize, len, heap)])
            .unwrap_or_default();
        Self {
            _backends: Vec::new(),
            tracker,
            log_chunk_size,
            heaps,
            owns_heaps: false,
            used_counter: 0,
        }
    }

    fn alloc_impl<T>(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
        alignment: usize,
        bounds: Option<Range<usize>>,
    ) -> CudaResult<StaticAllocationData<T>> {
        let byte_len = len * size_of::<T>();
        assert!(alignment.is_power_of_two());
        assert!(alignment >= align_of::<T>());
        let alloc_granularity = (1usize << self.log_chunk_size).max(alignment);
        let alloc_len = byte_len.next_multiple_of(alloc_granularity);
        let result = match bounds {
            Some(bounds) => self
                .tracker
                .alloc_aligned_in(alloc_len, placement, alignment, bounds),
            None => self.tracker.alloc_aligned(alloc_len, placement, alignment),
        };
        match result {
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
        self.alloc_impl::<T>(len, placement, align_of::<T>(), None)
    }

    pub fn alloc_with_extra_alignment<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocationData<T>> {
        let extra_alignment = 1usize << EXTRA_ALIGNMENT_LOG2;
        let alignment = align_of::<T>().max(extra_alignment);
        self.alloc_impl::<T>(len, placement, alignment, None)
    }

    pub fn free<T>(&mut self, data: StaticAllocationData<T>) {
        let ptr = data.ptr.cast::<u8>();
        let len = data.alloc_len;
        if len != 0 && self.nvtx_mem_regions_enabled() {
            nvtx::mem_region_unregister(ptr.as_ptr());
        }
        self.release(ptr, len);
    }

    fn release(&mut self, ptr: NonNull<u8>, len: usize) {
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

struct CarvedRegion<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> {
    parent: StaticAllocator<B, W>,
    addr: usize,
    len: usize,
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> Drop for CarvedRegion<B, W> {
    fn drop(&mut self) {
        let ptr = NonNull::new(self.addr as *mut u8).expect("carved region must be non-null");
        let len = self.len;
        self.parent.inner.execute(|inner| inner.release(ptr, len));
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
    carved_from: Option<Arc<CarvedRegion<B, W>>>,
    _phantom: PhantomData<B>,
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> StaticAllocator<B, W> {
    fn with_wrapper(
        inner: W,
        log_chunk_size: u32,
        carved_from: Option<Arc<CarvedRegion<B, W>>>,
    ) -> Self {
        Self {
            inner,
            log_chunk_size,
            carved_from,
            _phantom: Default::default(),
        }
    }

    pub fn new(backends: impl IntoIterator<Item = B>, log_chunk_size: u32) -> Self {
        let allocator = InnerStaticAllocator::new(backends, log_chunk_size);
        let inner = W::new(allocator);
        Self::with_wrapper(inner, log_chunk_size, None)
    }

    /// A pool over `byte_len` bytes cut out of this one; the range returns
    /// here once the carved pool and all of its allocations are dropped.
    pub fn carve(
        &self,
        byte_len: usize,
        placement: AllocationPlacement,
        log_chunk_size: u32,
    ) -> CudaResult<Self> {
        let (data, parent_heap) = self.inner.execute(|inner| {
            let data = inner.alloc::<u8>(byte_len, placement)?;
            let addr = data.ptr.as_ptr() as usize;
            let heap = inner
                .nvtx_mem_regions_enabled()
                .then(|| inner.nvtx_heap_for(addr));
            inner.used_mem_current_sampled();
            Ok::<_, CudaError>((data, heap))
        })?;
        let carved_from = Arc::new(CarvedRegion {
            parent: self.clone(),
            addr: data.ptr.as_ptr() as usize,
            len: data.alloc_len,
        });
        let allocator =
            InnerStaticAllocator::new_carved(data.ptr, data.alloc_len, log_chunk_size, parent_heap);
        Ok(Self::with_wrapper(
            W::new(allocator),
            log_chunk_size,
            Some(carved_from),
        ))
    }

    pub fn capacity(&self) -> usize {
        self.inner.execute(|inner| inner.tracker.capacity())
    }

    fn finish_alloc<T>(
        &self,
        result: CudaResult<(StaticAllocationData<T>, usize)>,
        site: &'static Location<'static>,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        result.map(|(data, used_after)| {
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
            StaticAllocation {
                allocator: self.clone(),
                data,
                nvtx_id,
                nvtx_site: site,
                nvtx_placement,
                nvtx_span,
            }
        })
    }

    fn alloc_placed<T>(
        &self,
        len: usize,
        placement: AllocationPlacement,
        alignment: usize,
        bounds: Option<Range<usize>>,
        site: &'static Location<'static>,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        let result = self.inner.execute(|inner| {
            inner
                .alloc_impl::<T>(len, placement, alignment, bounds)
                .map(|data| {
                    if data.alloc_len != 0 && inner.nvtx_mem_regions_enabled() {
                        let ptr = data.ptr.cast::<u8>().as_ptr();
                        nvtx::mem_region_register(
                            inner.nvtx_heap_for(ptr as usize),
                            ptr,
                            data.alloc_len,
                        );
                    }
                    (data, inner.used_mem_current_sampled())
                })
        });
        self.finish_alloc(result, site, placement)
    }

    #[track_caller]
    pub fn alloc<T>(
        &self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        self.alloc_placed(len, placement, align_of::<T>(), None, Location::caller())
    }

    #[track_caller]
    pub fn alloc_in<T>(
        &self,
        len: usize,
        placement: AllocationPlacement,
        bounds: Range<usize>,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        self.alloc_placed(
            len,
            placement,
            align_of::<T>(),
            Some(bounds),
            Location::caller(),
        )
    }

    #[track_caller]
    pub fn alloc_with_extra_alignment<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        let alignment = align_of::<T>().max(1usize << EXTRA_ALIGNMENT_LOG2);
        self.alloc_placed(len, placement, alignment, None, Location::caller())
    }

    #[track_caller]
    pub fn alloc_with_extra_alignment_in<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &self,
        len: usize,
        placement: AllocationPlacement,
        bounds: Range<usize>,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        let alignment = align_of::<T>().max(1usize << EXTRA_ALIGNMENT_LOG2);
        self.alloc_placed(len, placement, alignment, Some(bounds), Location::caller())
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
        Self::with_wrapper(
            self.inner.clone(),
            self.log_chunk_size,
            self.carved_from.clone(),
        )
    }
}

#[cfg(test)]
mod cpu_tests;
