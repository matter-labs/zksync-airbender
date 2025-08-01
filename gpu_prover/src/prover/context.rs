use crate::allocator::device::{
    NonConcurrentStaticDeviceAllocation, NonConcurrentStaticDeviceAllocator,
    StaticDeviceAllocationBackend,
};
use crate::allocator::host::{ConcurrentStaticHostAllocator, NonConcurrentStaticHostAllocator};
use crate::allocator::tracker::AllocationPlacement;
use crate::device_context::DeviceContext;
use era_cudart::device::{device_get_attribute, get_device, set_device};
use era_cudart::memory::{memory_get_info, CudaHostAllocFlags};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart_sys::{CudaDeviceAttr, CudaError};
use log::error;

pub struct DeviceProperties {
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
    pub allocation_block_log_size: u32,
    pub device_slack_blocks_count: usize,
    pub host_allocator_blocks_count: usize,
}

impl Default for ProverContextConfig {
    fn default() -> Self {
        Self {
            powers_of_w_coarse_log_count: 12,
            allocation_block_log_size: 22,    // 4 MB blocks
            device_slack_blocks_count: 64,    // 256 MB slack
            host_allocator_blocks_count: 128, // 512 MB host allocator pool
        }
    }
}

pub type DeviceAllocator = NonConcurrentStaticDeviceAllocator;
pub type DeviceAllocation<T> = NonConcurrentStaticDeviceAllocation<T>;
pub type HostAllocator = NonConcurrentStaticHostAllocator;

pub struct ProverContext {
    _device_context: DeviceContext,
    device_allocator: DeviceAllocator,
    host_allocator: HostAllocator,
    exec_stream: CudaStream,
    aux_stream: CudaStream,
    h2d_stream: CudaStream,
    device_allocator_mem_size: usize,
    device_id: i32,
    device_properties: DeviceProperties,
    reversed_allocation_placement: bool,
}

impl ProverContext {
    pub fn is_concurrent_host_allocator_initialized() -> bool {
        ConcurrentStaticHostAllocator::is_initialized_global()
    }

    pub fn initialize_concurrent_host_allocator(
        host_allocations_count: usize,
        blocks_per_allocation_count: usize,
        block_log_size: u32,
    ) -> CudaResult<()> {
        assert!(
            !ConcurrentStaticHostAllocator::is_initialized_global(),
            "ConcurrentStaticHostAllocator can only be initialized once"
        );
        let host_allocation_size = blocks_per_allocation_count << block_log_size;
        let mut allocations = vec![];
        for _ in 0..host_allocations_count {
            allocations.push(era_cudart::memory::HostAllocation::alloc(
                host_allocation_size,
                CudaHostAllocFlags::DEFAULT,
            )?);
        }
        ConcurrentStaticHostAllocator::initialize_global(allocations, block_log_size);
        Ok(())
    }

    pub fn new(config: &ProverContextConfig) -> CudaResult<Self> {
        let slack_size = config.device_slack_blocks_count << config.allocation_block_log_size;
        let slack = era_cudart::memory::DeviceAllocation::<u8>::alloc(slack_size)?;
        let device_id = get_device()?;
        let device_context = DeviceContext::create(config.powers_of_w_coarse_log_count)?;
        let exec_stream = CudaStream::create()?;
        let aux_stream = CudaStream::create()?;
        let h2d_stream = CudaStream::create()?;
        let (free, _) = memory_get_info()?;
        let mut device_blocks_count = free >> config.allocation_block_log_size;
        let device_allocation = loop {
            let result = era_cudart::memory::DeviceAllocation::<u8>::alloc(
                device_blocks_count << config.allocation_block_log_size,
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
        let device_allocation_backend =
            StaticDeviceAllocationBackend::DeviceAllocation(device_allocation);
        let device_allocator = NonConcurrentStaticDeviceAllocator::new(
            [device_allocation_backend],
            config.allocation_block_log_size,
        );
        let device_allocator_mem_size = device_blocks_count << config.allocation_block_log_size;
        let host_allocation_size =
            config.host_allocator_blocks_count << config.allocation_block_log_size;
        let host_allocation = era_cudart::memory::HostAllocation::alloc(
            host_allocation_size,
            CudaHostAllocFlags::DEFAULT,
        )?;
        let host_allocator = NonConcurrentStaticHostAllocator::new(
            [host_allocation],
            config.allocation_block_log_size,
        );
        let device_properties = DeviceProperties::new()?;
        let context = Self {
            _device_context: device_context,
            device_allocator,
            host_allocator,
            exec_stream,
            aux_stream,
            h2d_stream,
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

    pub fn get_device_id(&self) -> i32 {
        self.device_id
    }

    pub fn switch_to_device(&self) -> CudaResult<()> {
        set_device(self.device_id)
    }

    pub fn get_exec_stream(&self) -> &CudaStream {
        &self.exec_stream
    }

    pub fn get_aux_stream(&self) -> &CudaStream {
        &self.aux_stream
    }

    pub fn get_h2d_stream(&self) -> &CudaStream {
        &self.h2d_stream
    }

    pub fn alloc<T>(
        &self,
        size: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<DeviceAllocation<T>> {
        assert_ne!(size, 0);
        let placement = if self.reversed_allocation_placement {
            match placement {
                AllocationPlacement::BestFit => AllocationPlacement::BestFit,
                AllocationPlacement::Bottom => AllocationPlacement::Top,
                AllocationPlacement::Top => AllocationPlacement::Bottom,
            }
        } else {
            placement
        };
        let result = self.device_allocator.alloc(size, placement);
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

    pub(crate) unsafe fn alloc_host_uninit<T: Sized>(&self) -> HostAllocation<T> {
        HostAllocation::new_uninit(self)
    }

    pub(crate) unsafe fn alloc_host_uninit_slice<T: Sized>(
        &self,
        len: usize,
    ) -> HostAllocation<[T]> {
        HostAllocation::new_uninit_slice(len, self)
    }

    pub fn get_mem_size(&self) -> usize {
        self.device_allocator_mem_size
    }

    pub fn get_used_mem_current(&self) -> usize {
        self.device_allocator.get_used_mem_current()
    }

    pub fn get_used_mem_peak(&self) -> usize {
        self.device_allocator.get_used_mem_peak()
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

    pub fn is_reversed_allocation_placement(&self) -> bool {
        self.reversed_allocation_placement
    }

    pub fn set_reversed_allocation_placement(&mut self, reversed: bool) {
        self.reversed_allocation_placement = reversed;
    }
}

#[repr(transparent)]
pub(crate) struct UnsafeAccessor<T: ?Sized>(*const T);

impl<T: ?Sized> UnsafeAccessor<T> {
    pub fn new(value: &T) -> Self {
        UnsafeAccessor(value as *const T)
    }

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

unsafe impl<T: ?Sized> Send for UnsafeAccessor<T> {}
unsafe impl<T: ?Sized> Sync for UnsafeAccessor<T> {}

#[repr(transparent)]
pub(crate) struct UnsafeMutAccessor<T: ?Sized>(*mut T);

impl<T: ?Sized> UnsafeMutAccessor<T> {
    pub fn new(value: &mut T) -> Self {
        UnsafeMutAccessor(value as *mut T)
    }

    pub unsafe fn get(&self) -> &T {
        &*self.0
    }

    pub unsafe fn get_mut(&self) -> &mut T {
        &mut *(self.0)
    }

    pub unsafe fn set(&self, value: T)
    where
        T: Sized,
    {
        *(self.0) = value;
    }
}

impl<T: ?Sized> Clone for UnsafeMutAccessor<T> {
    fn clone(&self) -> Self {
        UnsafeMutAccessor(self.0)
    }
}

impl<T: ?Sized> Copy for UnsafeMutAccessor<T> {}

unsafe impl<T: ?Sized> Send for UnsafeMutAccessor<T> {}
unsafe impl<T: ?Sized> Sync for UnsafeMutAccessor<T> {}

pub(crate) struct HostAllocation<T: ?Sized>(Box<T, HostAllocator>);

impl<T: ?Sized> HostAllocation<T> {
    unsafe fn new_uninit(context: &ProverContext) -> Self
    where
        T: Sized,
    {
        Self(Box::new_uninit_in(context.get_host_allocator()).assume_init())
    }

    pub fn get_accessor(&self) -> UnsafeAccessor<T> {
        UnsafeAccessor::new(&self.0)
    }

    pub fn get_mut_accessor(&mut self) -> UnsafeMutAccessor<T> {
        UnsafeMutAccessor::new(&mut self.0)
    }
}

impl<T> HostAllocation<[T]> {
    unsafe fn new_uninit_slice(len: usize, context: &ProverContext) -> Self {
        Self(Box::new_uninit_slice_in(len, context.get_host_allocator()).assume_init())
    }
}
