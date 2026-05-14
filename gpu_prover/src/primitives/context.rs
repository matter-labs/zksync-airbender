use crate::allocator::device::{
    NonConcurrentStaticDeviceAllocation, NonConcurrentStaticDeviceAllocator,
    StaticDeviceAllocationBackend,
};
use crate::allocator::host::{ConcurrentStaticHostAllocator, NonConcurrentStaticHostAllocator};
// `ConcurrentStaticHostAllocator` is consumed via the `SchedulerHostAllocator`
// alias below — the explicit import keeps `pub(crate) type` resolution short.
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::ntt_twiddles::DeviceContext;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::memory::{memory_get_info, CudaHostAllocFlags};
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSlice, CudaSliceMut};
use era_cudart::stream::CudaStream;
use era_cudart_sys::{CudaDeviceAttr, CudaError};
use log::error;

pub(crate) struct DeviceProperties {
    pub l2_cache_size_bytes: usize,
    pub sm_count: usize,
}

impl DeviceProperties {
    pub fn new() -> CudaResult<Self> {
        let device_id = get_device()?;
        let l2_cache_size_bytes =
            device_get_attribute(CudaDeviceAttr::L2CacheSize, device_id)? as usize;
        let sm_count =
            device_get_attribute(CudaDeviceAttr::MultiProcessorCount, device_id)? as usize;
        Ok(Self {
            l2_cache_size_bytes,
            sm_count,
        })
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ProverContextConfig {
    pub powers_of_w_coarse_log_count: u32,
    pub allocator_block_log_size: u32,
    pub device_slack_static_bytes: usize,
    pub device_slack_per_thread_bytes: usize,
    pub max_device_allocation_blocks_count: Option<usize>,
    pub host_allocator_block_log_size: u32,
    pub host_allocator_blocks_count: usize,
    pub scheduler_host_allocator_block_log_size: u32,
    pub scheduler_host_allocator_blocks_count: usize,
    pub small_allocator_log_chunk_size: Option<u32>,
    pub small_allocator_pool_blocks: usize,
}

impl Default for ProverContextConfig {
    fn default() -> Self {
        Self {
            powers_of_w_coarse_log_count: 12,
            allocator_block_log_size: 20,                // 1 MB blocks
            device_slack_static_bytes: 1 << 27,          // 128 MB static slack
            device_slack_per_thread_bytes: 1 << 11,      // 2 KB per thread slack
            max_device_allocation_blocks_count: None,    // use all available memory
            host_allocator_block_log_size: 13, // 8 KB host blocks (small to avoid waste on tiny staging buffers)
            host_allocator_blocks_count: 163840, // 1.25 GB host allocator pool (163840 × 8 KB)
            scheduler_host_allocator_block_log_size: 13, // 8 KB scheduler-host blocks
            scheduler_host_allocator_blocks_count: 8192, // 64 MB scheduler-host allocator pool
            small_allocator_log_chunk_size: Some(8), // 256-byte granularity for small device allocations
            small_allocator_pool_blocks: 16, // 16 blocks × 1 MB = 16 MB small allocation pool
        }
    }
}

pub(crate) type DeviceAllocator = NonConcurrentStaticDeviceAllocator;
pub(crate) type DeviceAllocation<T> = NonConcurrentStaticDeviceAllocation<T>;
pub(crate) type HostAllocator = NonConcurrentStaticHostAllocator;
pub(crate) type SchedulerHostAllocator = ConcurrentStaticHostAllocator;

pub(crate) struct ProverContext {
    // Own the device-resident twiddle tables for the full lifetime of the prover context.
    _device_context: DeviceContext,
    device_allocator: DeviceAllocator,
    host_allocator: HostAllocator,
    #[allow(dead_code)]
    scheduler_host_allocator: SchedulerHostAllocator,
    exec_stream: CudaStream,
    h2d_stream: CudaStream,
    d2h_stream: CudaStream,
    device_allocator_mem_size: usize,
    device_id: i32,
    device_properties: DeviceProperties,
    reversed_allocation_placement: bool,
}

impl ProverContext {
    pub fn new(config: &ProverContextConfig) -> CudaResult<Self> {
        // host_typed allocations rely on the host pool's block size being at
        // least 16 bytes so any `T` whose alignment is ≤16 is satisfied by the
        // block address. See `proof/layout/mod.rs` for the consumers.
        assert!(
            config.host_allocator_block_log_size >= 4,
            "host_allocator_block_log_size must be >= 4 (16-byte blocks) for host_typed alignment"
        );
        let device_id = get_device()?;
        let mpc = device_get_attribute(CudaDeviceAttr::MultiProcessorCount, device_id)? as usize;
        let max_threads_per_mpc =
            device_get_attribute(CudaDeviceAttr::MaxThreadsPerMultiProcessor, device_id)? as usize;
        let max_threads_count = mpc * max_threads_per_mpc;
        let device_slack_threads_bytes = config.device_slack_per_thread_bytes * max_threads_count;
        let slack_size = config.device_slack_static_bytes + device_slack_threads_bytes;
        let slack = era_cudart::memory::DeviceAllocation::<u8>::alloc(slack_size)?;
        let allocator_block_log_size = config.allocator_block_log_size;
        let device_context = DeviceContext::create(config.powers_of_w_coarse_log_count)?;
        let exec_stream = CudaStream::create()?;
        let h2d_stream = CudaStream::create()?;
        let d2h_stream = CudaStream::create()?;
        let mut device_blocks_count =
            if let Some(max_blocks_count) = config.max_device_allocation_blocks_count {
                max_blocks_count
            } else {
                let (free, _) = memory_get_info()?;
                free >> allocator_block_log_size
            };
        let device_allocation = loop {
            let result = era_cudart::memory::DeviceAllocation::<u8>::alloc(
                device_blocks_count << allocator_block_log_size,
            );
            match result {
                Ok(allocation) => break allocation,
                Err(CudaError::ErrorMemoryAllocation) => {
                    let last_error = era_cudart::error::get_last_error();
                    if last_error != CudaError::ErrorMemoryAllocation {
                        return Err(last_error);
                    }
                    device_blocks_count -= 1;
                    continue;
                }
                Err(e) => return Err(e),
            };
        };
        slack.free()?;
        let device_allocation_backend = StaticDeviceAllocationBackend(device_allocation);
        let device_allocator = if let Some(small_log_chunk_size) =
            config.small_allocator_log_chunk_size
        {
            let small_pool_size = config.small_allocator_pool_blocks << allocator_block_log_size;
            NonConcurrentStaticDeviceAllocator::new_with_small_allocator(
                [device_allocation_backend],
                allocator_block_log_size,
                small_log_chunk_size,
                small_pool_size,
            )
        } else {
            NonConcurrentStaticDeviceAllocator::new(
                [device_allocation_backend],
                allocator_block_log_size,
            )
        };
        let device_allocator_mem_size = device_blocks_count << allocator_block_log_size;
        let host_block_log_size = config.host_allocator_block_log_size;
        let host_allocation_size = config.host_allocator_blocks_count << host_block_log_size;
        let host_allocation = era_cudart::memory::HostAllocation::alloc(
            host_allocation_size,
            CudaHostAllocFlags::DEFAULT,
        )?;
        let host_allocator =
            NonConcurrentStaticHostAllocator::new([host_allocation], host_block_log_size);
        let scheduler_host_block_log_size = config.scheduler_host_allocator_block_log_size;
        let scheduler_host_allocation_size =
            config.scheduler_host_allocator_blocks_count << scheduler_host_block_log_size;
        let scheduler_host_allocation = era_cudart::memory::HostAllocation::alloc(
            scheduler_host_allocation_size,
            CudaHostAllocFlags::DEFAULT,
        )?;
        let scheduler_host_allocator =
            SchedulerHostAllocator::new([scheduler_host_allocation], scheduler_host_block_log_size);
        let device_properties = DeviceProperties::new()?;
        let context = Self {
            _device_context: device_context,
            device_allocator,
            host_allocator,
            scheduler_host_allocator,
            exec_stream,
            h2d_stream,
            d2h_stream,
            device_allocator_mem_size,
            device_id,
            device_properties,
            reversed_allocation_placement: false,
        };
        Ok(context)
    }

    pub fn get_host_allocator(&self) -> HostAllocator {
        self.host_allocator.clone()
    }

    pub fn get_exec_stream(&self) -> &CudaStream {
        &self.exec_stream
    }

    pub fn get_h2d_stream(&self) -> &CudaStream {
        &self.h2d_stream
    }

    /// Device-to-host transfer stream. Use for D2H copies (and their consumer callbacks) that
    /// would otherwise serialize on `exec_stream`. Producers on `exec_stream` hand off to
    /// `d2h_stream` via a fork event; `d2h_stream` joins back via a second event before the next
    /// exec-stream op that reads what d2h wrote or frees a pool-backed source. See
    /// `docs/gpu_scheduling_contract.md` for the fork/join/drop ownership rules.
    pub fn get_d2h_stream(&self) -> &CudaStream {
        &self.d2h_stream
    }

    pub fn alloc<T>(
        &self,
        size: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<DeviceAllocation<T>> {
        let placement = if self.reversed_allocation_placement {
            match placement {
                AllocationPlacement::BestFit => AllocationPlacement::BestFit,
                AllocationPlacement::Bottom => AllocationPlacement::Top,
                AllocationPlacement::Top => AllocationPlacement::Bottom,
            }
        } else {
            placement
        };
        let result = self.device_allocator.alloc::<T>(size, placement);
        if result.is_err() {
            error!(
                "failed to allocate {} bytes from GPU memory allocator of device ID {}, currently allocated {} bytes",
                size * size_of::<T>(),
                self.device_id,
                self.get_used_mem_current()
            );
        }
        result
    }

    pub fn alloc_with_extra_alignment<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &self,
        size: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<DeviceAllocation<T>> {
        let placement = if self.reversed_allocation_placement {
            match placement {
                AllocationPlacement::BestFit => AllocationPlacement::BestFit,
                AllocationPlacement::Bottom => AllocationPlacement::Top,
                AllocationPlacement::Top => AllocationPlacement::Bottom,
            }
        } else {
            placement
        };
        let result = self
            .device_allocator
            .alloc_with_extra_alignment::<T, EXTRA_ALIGNMENT_LOG2>(size, placement);
        if result.is_err() {
            error!(
                "failed to allocate {} bytes from GPU memory allocator of device ID {}, currently allocated {} bytes",
                size * size_of::<T>(),
                self.device_id,
                self.get_used_mem_current()
            );
        }
        result
    }

    /// # Safety
    ///
    /// Returns a pinned host allocation whose contents are **uninitialized**.
    /// The scheduling thread must NOT dereference the returned buffer: per the
    /// inverted-access rule in `docs/gpu_scheduling_contract.md`, every read
    /// and write must come from a stream-scheduled op (host callback or
    /// `memory_copy_async`). The first stream op touching the buffer must be a
    /// write (an H2D from a callback-populated source, or a D2H of fresh
    /// device contents); reading from it before that is UB on the uninit
    /// memory.
    pub(crate) unsafe fn alloc_host_uninit<T: Sized>(&self) -> HostAllocation<T> {
        HostAllocation::new_uninit_in(self.get_host_allocator())
    }

    /// # Safety
    ///
    /// Same contract as [`Self::alloc_host_uninit`]; see that method's safety
    /// note. The pool may have just recycled this block from a prior owner
    /// whose DMA is not yet complete — every access must be stream-ordered.
    pub(crate) unsafe fn alloc_host_uninit_slice<T: Sized>(
        &self,
        len: usize,
    ) -> HostAllocation<[T]> {
        HostAllocation::new_uninit_slice_in(len, self.get_host_allocator())
    }

    pub fn get_mem_size(&self) -> usize {
        self.device_allocator_mem_size
    }

    pub fn get_used_mem_current(&self) -> usize {
        self.device_allocator.get_used_mem_current()
    }

    #[cfg(test)]
    pub fn get_used_mem_peak(&self) -> usize {
        self.device_allocator.get_used_mem_peak()
    }

    #[cfg(test)]
    pub fn get_host_used_mem_current(&self) -> usize {
        self.host_allocator.get_used_mem_current()
    }

    #[cfg(test)]
    pub fn get_host_used_mem_peak(&self) -> usize {
        self.host_allocator.get_used_mem_peak()
    }

    #[cfg(test)]
    pub fn reset_host_used_mem_peak(&self) {
        self.host_allocator.reset_used_mem_peak();
    }

    #[cfg(test)]
    pub fn get_scheduler_host_used_mem_current(&self) -> usize {
        self.scheduler_host_allocator.get_used_mem_current()
    }

    #[cfg(test)]
    pub fn get_scheduler_host_used_mem_peak(&self) -> usize {
        self.scheduler_host_allocator.get_used_mem_peak()
    }

    #[cfg(test)]
    pub fn reset_scheduler_host_used_mem_peak(&self) {
        self.scheduler_host_allocator.reset_used_mem_peak();
    }

    pub fn reset_used_mem_peak(&self) {
        self.device_allocator.reset_used_mem_peak();
    }

    #[cfg(feature = "log_gpu_mem_usage")]
    pub fn log_gpu_mem_usage(&self, location: &str) {
        let used_mem_current = self.get_used_mem_current();
        let used_mem_peak = self.get_used_mem_peak();
        log::debug!(
            "GPU memory usage {location} current/peak: {}/{} GB",
            used_mem_current as f64 / ((1 << 30) as f64),
            used_mem_peak as f64 / ((1 << 30) as f64),
        );
    }

    pub fn get_device_properties(&self) -> &DeviceProperties {
        &self.device_properties
    }

    pub fn set_reversed_allocation_placement(&mut self, reversed: bool) {
        self.reversed_allocation_placement = reversed;
    }
}

/// Raw `*const T` wrapper that escapes Rust borrow-checking so a captured
/// reference can travel into a stream-scheduled host callback.
///
/// Only the holder's lifetime is enforced — at call sites the pointee must
/// still outlive every dereference. See
/// [`docs/gpu_scheduling_contract.md`](../../docs/gpu_scheduling_contract.md)
/// for the lifetime and access rules.
#[repr(transparent)]
pub(crate) struct UnsafeAccessor<T: ?Sized>(*const T);

impl<T: ?Sized> UnsafeAccessor<T> {
    pub fn new(value: &T) -> Self {
        UnsafeAccessor(value as *const T)
    }

    /// # Safety
    ///
    /// May only be called from inside a stream-scheduled host callback
    /// (`Callbacks::schedule` / `launch_host_fn`) whose ordering establishes
    /// that the referent has been initialized by prior stream ops and is not
    /// being concurrently mutated. The original holder must remain alive
    /// until that callback has been *scheduled*; see contract doc.
    pub unsafe fn get(&self) -> &T {
        &*self.0
    }
}

impl<T: ?Sized> Clone for UnsafeAccessor<T> {
    fn clone(&self) -> Self {
        UnsafeAccessor(self.0)
    }
}

impl<T: ?Sized> Copy for UnsafeAccessor<T> {}

// SAFETY: `UnsafeAccessor<T>` is a raw pointer wrapper used to thread a
// borrow into a stream-scheduled callback running on a different thread.
// The scheduling contract (see `docs/gpu_scheduling_contract.md`) makes the
// caller responsible for ordering reads/writes; the type itself adds no new
// thread-safety obligations beyond `Sync`/`Send` of `*const T`.
unsafe impl<T: ?Sized> Send for UnsafeAccessor<T> {}
unsafe impl<T: ?Sized> Sync for UnsafeAccessor<T> {}

/// Raw `*mut T` wrapper with the same intent as [`UnsafeAccessor`] but for
/// mutable borrows.
///
/// See [`docs/gpu_scheduling_contract.md`](../../docs/gpu_scheduling_contract.md)
/// for the write-exclusivity and lifetime rules.
#[repr(transparent)]
pub(crate) struct UnsafeMutAccessor<T: ?Sized>(*mut T);

impl<T: ?Sized> UnsafeMutAccessor<T> {
    pub fn new(value: &mut T) -> Self {
        UnsafeMutAccessor(value as *mut T)
    }

    /// # Safety
    ///
    /// May only be called from inside a stream-scheduled host callback whose
    /// ordering guarantees the referent has been initialized and is not being
    /// concurrently mutated by another stream op. See contract doc.
    pub unsafe fn get(&self) -> &T {
        &*self.0
    }

    /// # Safety
    ///
    /// Only valid inside a stream-scheduled host callback. Write-exclusivity
    /// is enforced by scheduling order, not by the type: at most one stream
    /// op (callback or kernel) may write the referent at a time, per the
    /// fork/join window rules in `docs/gpu_scheduling_contract.md`.
    pub unsafe fn get_mut(&self) -> &mut T {
        &mut *(self.0)
    }

    /// # Safety
    ///
    /// Same as [`Self::get_mut`]; writes go through `std::ptr::write`, so
    /// the referent must be aligned and writable, and no concurrent stream
    /// op may be reading or writing it.
    pub unsafe fn write(&self, value: T)
    where
        T: Sized,
    {
        std::ptr::write(self.0, value);
    }
}

impl<T: ?Sized> Clone for UnsafeMutAccessor<T> {
    fn clone(&self) -> Self {
        UnsafeMutAccessor(self.0)
    }
}

impl<T: ?Sized> Copy for UnsafeMutAccessor<T> {}

// SAFETY: see `UnsafeAccessor` Send/Sync note above; the scheduling contract
// governs write-exclusivity and lifetime.
unsafe impl<T: ?Sized> Send for UnsafeMutAccessor<T> {}
unsafe impl<T: ?Sized> Sync for UnsafeMutAccessor<T> {}

pub(crate) struct HostAllocation<T: ?Sized>(Box<T, HostAllocator>);

impl<T: ?Sized> HostAllocation<T> {
    unsafe fn new_uninit_in(allocator: HostAllocator) -> Self
    where
        T: Sized,
    {
        Self(Box::new_uninit_in(allocator).assume_init())
    }

    pub fn get_accessor(&self) -> UnsafeAccessor<T> {
        UnsafeAccessor::new(&self.0)
    }

    pub fn get_mut_accessor(&mut self) -> UnsafeMutAccessor<T> {
        UnsafeMutAccessor::new(&mut self.0)
    }
}

impl<T> HostAllocation<[T]> {
    unsafe fn new_uninit_slice_in(len: usize, allocator: HostAllocator) -> Self {
        Self(Box::new_uninit_slice_in(len, allocator).assume_init())
    }
}

impl<T> CudaSlice<T> for HostAllocation<[T]> {
    unsafe fn as_slice(&self) -> &[T] {
        self.0.as_slice()
    }
}

impl<T> CudaSliceMut<T> for HostAllocation<[T]> {
    unsafe fn as_mut_slice(&mut self) -> &mut [T] {
        self.0.as_mut_slice()
    }
}
