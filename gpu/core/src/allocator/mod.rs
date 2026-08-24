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

const MEMORY_HIGH_WATER_OBSERVER_SLOTS: usize = 2;

/// Exact current usage of one static allocator pool.
///
/// Physical backing counts bytes occupied in the outer tracker, including a
/// carved small-allocation pool in full. Logical live bytes replace that
/// reservation with the small pool's currently live suballocations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolMemoryUsage {
    pub physical_backing_bytes: usize,
    pub logical_live_bytes: usize,
}

/// Frozen high-water state for an observation whose peak window was sealed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolMemoryHighWaterSnapshot {
    pub start: PoolMemoryUsage,
    pub physical_backing_peak_bytes: usize,
    pub logical_live_peak_bytes: usize,
    pub summed_requested_bytes: usize,
    pub peak_window_end: PoolMemoryUsage,
}

/// Completed high-water observation, including the current usage at finish.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolMemoryHighWaterReport {
    pub start: PoolMemoryUsage,
    pub physical_backing_peak_bytes: usize,
    pub logical_live_peak_bytes: usize,
    /// Sum of successful allocation requests before chunk/alignment rounding.
    pub summed_requested_bytes: usize,
    pub peak_window_end: PoolMemoryUsage,
    pub return_to_entry: PoolMemoryUsage,
}

/// Opaque handle for one scoped observation slot.
#[must_use = "finish or cancel the memory high-water observation"]
#[derive(Debug)]
pub struct MemoryHighWaterToken {
    slot: usize,
    generation: u64,
}

struct MemoryHighWaterObservation {
    generation: u64,
    start: PoolMemoryUsage,
    physical_backing_peak_bytes: usize,
    logical_live_peak_bytes: usize,
    summed_requested_bytes: usize,
    peak_window_end: Option<PoolMemoryUsage>,
}

impl MemoryHighWaterObservation {
    fn new(generation: u64, start: PoolMemoryUsage) -> Self {
        Self {
            generation,
            start,
            physical_backing_peak_bytes: start.physical_backing_bytes,
            logical_live_peak_bytes: start.logical_live_bytes,
            summed_requested_bytes: 0,
            peak_window_end: None,
        }
    }

    fn sample(&mut self, usage: PoolMemoryUsage, requested_bytes: Option<usize>) {
        if self.peak_window_end.is_some() {
            return;
        }
        self.physical_backing_peak_bytes = self
            .physical_backing_peak_bytes
            .max(usage.physical_backing_bytes);
        self.logical_live_peak_bytes = self.logical_live_peak_bytes.max(usage.logical_live_bytes);
        if let Some(requested_bytes) = requested_bytes {
            self.summed_requested_bytes = self
                .summed_requested_bytes
                .checked_add(requested_bytes)
                .expect("memory high-water requested-byte sum overflowed usize");
        }
    }

    fn snapshot(&self) -> PoolMemoryHighWaterSnapshot {
        PoolMemoryHighWaterSnapshot {
            start: self.start,
            physical_backing_peak_bytes: self.physical_backing_peak_bytes,
            logical_live_peak_bytes: self.logical_live_peak_bytes,
            summed_requested_bytes: self.summed_requested_bytes,
            peak_window_end: self
                .peak_window_end
                .expect("memory high-water observation was not sealed"),
        }
    }
}

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
    heaps: Vec<(usize, usize, nvtx::MemHeapHandle)>,
    used_counter: u64,
    memory_high_water_observers:
        [Option<MemoryHighWaterObservation>; MEMORY_HIGH_WATER_OBSERVER_SLOTS],
    occupied_memory_high_water_observers: u8,
    next_memory_high_water_generation: u64,
}

impl<B: StaticAllocationBackend> Drop for InnerStaticAllocator<B> {
    fn drop(&mut self) {
        for &(_, _, heap) in &self.heaps {
            nvtx::mem_heap_unregister(heap);
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
            small: None,
            heaps,
            used_counter,
            memory_high_water_observers: [None, None],
            occupied_memory_high_water_observers: 0,
            next_memory_high_water_generation: 0,
        }
    }

    pub fn new_with_small_allocator(
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

    fn alloc_from_tracker<T>(
        tracker: &mut AllocationsTracker,
        log_chunk_size: u32,
        len: usize,
        byte_len: usize,
        placement: AllocationPlacement,
        alignment: usize,
    ) -> CudaResult<StaticAllocationData<T>> {
        let alloc_granularity = (1usize << log_chunk_size).max(alignment);
        let alloc_len = byte_len.next_multiple_of(alloc_granularity);
        match tracker.alloc_aligned(alloc_len, placement, alignment) {
            Ok(ptr) => {
                assert!(ptr.is_aligned_to(alignment));
                let ptr = ptr.cast::<T>();
                Ok(StaticAllocationData::new(ptr, len, alloc_len))
            }
            Err(_) => Err(CudaError::ErrorMemoryAllocation),
        }
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
                return Self::alloc_from_tracker(
                    &mut small.tracker,
                    small.log_chunk_size,
                    len,
                    byte_len,
                    placement,
                    alignment,
                );
            }
        }

        Self::alloc_from_tracker(
            &mut self.tracker,
            self.log_chunk_size,
            len,
            byte_len,
            placement,
            alignment,
        )
    }

    pub fn alloc<T>(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocationData<T>> {
        self.alloc_impl::<T>(len, placement, align_of::<T>())
    }

    pub fn alloc_with_extra_alignment<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &mut self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocationData<T>> {
        let extra_alignment = 1usize << EXTRA_ALIGNMENT_LOG2;
        let alignment = align_of::<T>().max(extra_alignment);
        self.alloc_impl::<T>(len, placement, alignment)
    }

    pub fn free<T>(&mut self, data: StaticAllocationData<T>) {
        let ptr = data.ptr.cast::<u8>();
        let len = data.alloc_len;
        let addr = ptr.as_ptr() as usize;
        if len != 0 && self.nvtx_mem_regions_enabled() {
            nvtx::mem_region_unregister(ptr.as_ptr());
        }

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

    fn nvtx_mem_regions_enabled(&self) -> bool {
        !self.heaps.is_empty()
    }

    // The small pool's backing is carved from a backend range, so its
    // allocations resolve to the containing device heap (a nested NVTX heap
    // would be rejected as overlapping).
    fn nvtx_heap_for(&self, addr: usize) -> nvtx::MemHeapHandle {
        self.heaps
            .iter()
            .find(|&&(base, len, _)| addr >= base && addr < base + len)
            .map(|&(_, _, heap)| heap)
            .unwrap_or_else(nvtx::MemHeapHandle::process_wide)
    }

    /// Samples both scoped high-water observers and the diagnostic NVTX
    /// corrected-logical counter after one successful allocation/free.
    fn used_mem_current_sampled(&mut self, requested_bytes: Option<usize>) -> usize {
        let usage = self.memory_usage();
        if self.occupied_memory_high_water_observers != 0 {
            self.sample_occupied_memory_high_water_observers(usage, requested_bytes);
        }
        if self.used_counter != 0 {
            nvtx::mem_counter_sample(self.used_counter, usage.logical_live_bytes as i64);
        }
        usage.logical_live_bytes
    }

    #[cold]
    #[inline(never)]
    fn sample_occupied_memory_high_water_observers(
        &mut self,
        usage: PoolMemoryUsage,
        requested_bytes: Option<usize>,
    ) {
        debug_assert_ne!(self.occupied_memory_high_water_observers, 0);
        for observation in self.memory_high_water_observers.iter_mut().flatten() {
            observation.sample(usage, requested_bytes);
        }
    }

    fn used_mem_current(&self) -> usize {
        self.memory_usage().logical_live_bytes
    }

    fn memory_usage(&self) -> PoolMemoryUsage {
        let big_used = self.tracker.get_used_mem_current();
        let logical_live_bytes = match &self.small {
            // big_used includes the backing pool as "used".
            // Correct by replacing the pool's total size with its actual usage.
            Some(small) => big_used
                .checked_sub(small.backing_len)
                .and_then(|outside_small| {
                    outside_small.checked_add(small.tracker.get_used_mem_current())
                })
                .expect("corrected logical allocator usage overflowed or underflowed usize"),
            None => big_used,
        };
        PoolMemoryUsage {
            physical_backing_bytes: big_used,
            logical_live_bytes,
        }
    }

    fn start_memory_high_water_observation(&mut self) -> MemoryHighWaterToken {
        let slot = self
            .memory_high_water_observers
            .iter()
            .position(Option::is_none)
            .expect("all two memory high-water observer slots are occupied");
        self.next_memory_high_water_generation = self
            .next_memory_high_water_generation
            .checked_add(1)
            .expect("memory high-water observer generation overflowed u64");
        let generation = self.next_memory_high_water_generation;
        let start = self.memory_usage();
        self.memory_high_water_observers[slot] =
            Some(MemoryHighWaterObservation::new(generation, start));
        self.occupied_memory_high_water_observers = self
            .occupied_memory_high_water_observers
            .checked_add(1)
            .expect("memory high-water observer count overflowed u8");
        MemoryHighWaterToken { slot, generation }
    }

    fn observation_mut(&mut self, token: &MemoryHighWaterToken) -> &mut MemoryHighWaterObservation {
        let observation = self
            .memory_high_water_observers
            .get_mut(token.slot)
            .and_then(Option::as_mut)
            .unwrap_or_else(|| panic!("memory high-water observer token references an empty slot"));
        assert_eq!(
            observation.generation, token.generation,
            "memory high-water observer token generation is stale"
        );
        observation
    }

    fn seal_memory_high_water_observation(
        &mut self,
        token: &MemoryHighWaterToken,
    ) -> PoolMemoryHighWaterSnapshot {
        let current = self.memory_usage();
        let observation = self.observation_mut(token);
        if observation.peak_window_end.is_none() {
            observation.sample(current, None);
            observation.peak_window_end = Some(current);
        }
        observation.snapshot()
    }

    fn finish_memory_high_water_observation(
        &mut self,
        token: MemoryHighWaterToken,
    ) -> PoolMemoryHighWaterReport {
        let current = self.memory_usage();
        self.observation_mut(&token);
        let mut observation = self.memory_high_water_observers[token.slot]
            .take()
            .expect("validated memory high-water observer slot disappeared");
        self.occupied_memory_high_water_observers = self
            .occupied_memory_high_water_observers
            .checked_sub(1)
            .expect("memory high-water observer count underflowed u8");
        if observation.peak_window_end.is_none() {
            observation.sample(current, None);
            observation.peak_window_end = Some(current);
        }
        PoolMemoryHighWaterReport {
            start: observation.start,
            physical_backing_peak_bytes: observation.physical_backing_peak_bytes,
            logical_live_peak_bytes: observation.logical_live_peak_bytes,
            summed_requested_bytes: observation.summed_requested_bytes,
            peak_window_end: observation
                .peak_window_end
                .expect("finished memory high-water observation was not sealed"),
            return_to_entry: current,
        }
    }

    fn cancel_memory_high_water_observation(&mut self, token: MemoryHighWaterToken) {
        self.observation_mut(&token);
        self.memory_high_water_observers[token.slot] = None;
        self.occupied_memory_high_water_observers = self
            .occupied_memory_high_water_observers
            .checked_sub(1)
            .expect("memory high-water observer count underflowed u8");
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
    /// Shrinks the exposed element count without changing physical ownership.
    ///
    /// `len` and `data.len` count `T` elements. `data.alloc_len` remains the
    /// originally reserved byte count used when this allocation is dropped.
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
    _phantom: PhantomData<B>,
}

/// RAII wrapper for one scoped allocator high-water observation.
///
/// Dropping it before `finish` cancels the observation and releases its slot.
#[doc(hidden)]
#[must_use = "finish, cancel, or drop the memory high-water observer"]
pub struct MemoryHighWaterObserver<
    'a,
    B: StaticAllocationBackend,
    W: InnerStaticAllocatorWrapper<B>,
> {
    allocator: &'a StaticAllocator<B, W>,
    token: Option<MemoryHighWaterToken>,
}

impl<'a, B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>>
    MemoryHighWaterObserver<'a, B, W>
{
    fn new(allocator: &'a StaticAllocator<B, W>) -> Self {
        Self {
            allocator,
            token: Some(allocator.start_memory_high_water_observation()),
        }
    }

    pub fn seal(&mut self) -> PoolMemoryHighWaterSnapshot {
        self.allocator.seal_memory_high_water_observation(
            self.token
                .as_ref()
                .expect("memory high-water observer was already finished or cancelled"),
        )
    }

    pub fn finish(mut self) -> PoolMemoryHighWaterReport {
        let token = self
            .token
            .take()
            .expect("memory high-water observer was already finished or cancelled");
        self.allocator.finish_memory_high_water_observation(token)
    }

    pub fn cancel(mut self) {
        let token = self
            .token
            .take()
            .expect("memory high-water observer was already finished or cancelled");
        self.allocator.cancel_memory_high_water_observation(token);
    }
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> Drop
    for MemoryHighWaterObserver<'_, B, W>
{
    fn drop(&mut self) {
        if let Some(token) = self.token.take() {
            self.allocator.cancel_memory_high_water_observation(token);
        }
    }
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

    #[track_caller]
    pub fn alloc<T>(
        &self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        let site = Location::caller();
        let requested_bytes = len
            .checked_mul(size_of::<T>())
            .expect("allocation byte length overflowed usize");
        let result = self.inner.execute(|inner| {
            inner.alloc::<T>(len, placement).map(|data| {
                if data.alloc_len != 0 && inner.nvtx_mem_regions_enabled() {
                    let ptr = data.ptr.cast::<u8>().as_ptr();
                    nvtx::mem_region_register(
                        inner.nvtx_heap_for(ptr as usize),
                        ptr,
                        data.alloc_len,
                    );
                }
                (data, inner.used_mem_current_sampled(Some(requested_bytes)))
            })
        });
        self.finish_alloc(result, site, placement)
    }

    #[track_caller]
    pub fn alloc_with_extra_alignment<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &self,
        len: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<StaticAllocation<T, B, W>> {
        let site = Location::caller();
        let requested_bytes = len
            .checked_mul(size_of::<T>())
            .expect("allocation byte length overflowed usize");
        let result = self.inner.execute(|inner| {
            inner
                .alloc_with_extra_alignment::<T, EXTRA_ALIGNMENT_LOG2>(len, placement)
                .map(|data| {
                    if data.alloc_len != 0 && inner.nvtx_mem_regions_enabled() {
                        let ptr = data.ptr.cast::<u8>().as_ptr();
                        nvtx::mem_region_register(
                            inner.nvtx_heap_for(ptr as usize),
                            ptr,
                            data.alloc_len,
                        );
                    }
                    (data, inner.used_mem_current_sampled(Some(requested_bytes)))
                })
        });
        self.finish_alloc(result, site, placement)
    }

    unsafe fn free_using_data<T>(&self, data: StaticAllocationData<T>) -> usize {
        self.inner.execute(|inner| {
            inner.free(data);
            inner.used_mem_current_sampled(None)
        })
    }

    /// Returns corrected logical live bytes, excluding unused capacity in a
    /// carved small-allocation pool.
    pub fn get_used_mem_current(&self) -> usize {
        self.inner.execute(|inner| inner.used_mem_current())
    }

    /// Resets the legacy physical-backing peak to the current outer-tracker
    /// usage. Scoped high-water observations are deliberately unaffected.
    pub fn reset_used_mem_peak(&self) {
        self.inner
            .execute(|inner| inner.tracker.reset_used_mem_peak())
    }

    /// Returns both physical backing and corrected logical live bytes now.
    pub fn get_memory_usage(&self) -> PoolMemoryUsage {
        self.inner.execute(|inner| inner.memory_usage())
    }

    /// Starts one interval-local high-water observation at the current usage.
    ///
    /// Exactly two observations may be live concurrently. The returned token
    /// must be sealed/finished or cancelled; prefer `observe_memory_high_water`
    /// when an RAII guard fits the caller's ownership.
    pub fn start_memory_high_water_observation(&self) -> MemoryHighWaterToken {
        self.inner
            .execute(InnerStaticAllocator::start_memory_high_water_observation)
    }

    /// Freezes peak and requested-byte accumulation while retaining the token
    /// for a later exact return-to-entry sample.
    pub fn seal_memory_high_water_observation(
        &self,
        token: &MemoryHighWaterToken,
    ) -> PoolMemoryHighWaterSnapshot {
        self.inner
            .execute(|inner| inner.seal_memory_high_water_observation(token))
    }

    /// Samples current usage, returns the complete raw-byte report, and frees
    /// the observation slot. An unsealed observation is sealed at finish.
    pub fn finish_memory_high_water_observation(
        &self,
        token: MemoryHighWaterToken,
    ) -> PoolMemoryHighWaterReport {
        self.inner
            .execute(|inner| inner.finish_memory_high_water_observation(token))
    }

    /// Cancels an active or sealed observation without producing a report.
    pub fn cancel_memory_high_water_observation(&self, token: MemoryHighWaterToken) {
        self.inner
            .execute(|inner| inner.cancel_memory_high_water_observation(token));
    }

    #[doc(hidden)]
    pub fn observe_memory_high_water(&self) -> MemoryHighWaterObserver<'_, B, W> {
        MemoryHighWaterObserver::new(self)
    }
}

impl<B: StaticAllocationBackend, W: InnerStaticAllocatorWrapper<B>> StaticAllocator<B, W> {
    /// Returns the legacy outer-tracker high-water. This is physical backing
    /// usage and includes a carved small-allocation pool in full.
    pub fn get_used_mem_peak(&self) -> usize {
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
mod cpu_tests;
