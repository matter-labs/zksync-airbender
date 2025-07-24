use crate::allocator::device::{
    NonConcurrentStaticDeviceAllocation, NonConcurrentStaticDeviceAllocator,
    StaticDeviceAllocationBackend,
};
use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::allocator::tracker::AllocationPlacement;
use crate::device_context::DeviceContext;
use era_cudart::device::{device_get_attribute, get_device, set_device};
use era_cudart::memory::{memory_get_info, CudaHostAllocFlags, HostAllocation};
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
    pub device_slack_blocks: usize,
}

impl Default for ProverContextConfig {
    fn default() -> Self {
        Self {
            powers_of_w_coarse_log_count: 12,
            allocation_block_log_size: 22, // 4 MB blocks
            device_slack_blocks: 64,       // 256 MB slack
        }
    }
}

pub struct ProverContext {
    _device_context: DeviceContext,
    pub(crate) device_allocator: NonConcurrentStaticDeviceAllocator,
    pub(crate) exec_stream: CudaStream,
    pub(crate) aux_stream: CudaStream,
    pub(crate) h2d_stream: CudaStream,
    pub(crate) mem_size: usize,
    pub(crate) device_id: i32,
    pub(crate) device_properties: DeviceProperties,
    pub(crate) reversed_allocation_placement: bool,
}

pub type HostAllocator = ConcurrentStaticHostAllocator;

pub type DeviceAllocation<T> = NonConcurrentStaticDeviceAllocation<T>;

impl ProverContext {
    pub fn is_host_allocator_initialized() -> bool {
        ConcurrentStaticHostAllocator::is_initialized_global()
    }

    pub fn initialize_host_allocator(
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
            allocations.push(HostAllocation::alloc(
                host_allocation_size,
                CudaHostAllocFlags::DEFAULT,
            )?);
        }
        ConcurrentStaticHostAllocator::initialize_global(allocations, block_log_size);
        Ok(())
    }

    pub fn new(config: &ProverContextConfig) -> CudaResult<Self> {
        let slack_size = config.device_slack_blocks << config.allocation_block_log_size;
        let slack = era_cudart::memory::DeviceAllocation::<u8>::alloc(slack_size)?;
        let device_id = get_device()?;
        let device_context = DeviceContext::create(config.powers_of_w_coarse_log_count)?;
        let exec_stream = CudaStream::create()?;
        let aux_stream = CudaStream::create()?;
        let h2d_stream = CudaStream::create()?;
        let (free, _) = memory_get_info()?;
        let mut size = free >> config.allocation_block_log_size;
        let allocation = loop {
            let result = era_cudart::memory::DeviceAllocation::<u8>::alloc(
                size << config.allocation_block_log_size,
            );
            match result {
                Ok(allocation) => break allocation,
                Err(CudaError::ErrorMemoryAllocation) => {
                    let last_error = era_cudart::error::get_last_error();
                    if last_error != CudaError::ErrorMemoryAllocation {
                        return Err(last_error);
                    }
                    size -= 1;
                    continue;
                }
                Err(e) => return Err(e),
            };
        };
        slack.free()?;
        let device_allocator = NonConcurrentStaticDeviceAllocator::new(
            [StaticDeviceAllocationBackend::DeviceAllocation(allocation)],
            config.allocation_block_log_size,
        );
        let mem_size = size << config.allocation_block_log_size;
        let device_properties = DeviceProperties::new()?;
        let context = Self {
            _device_context: device_context,
            device_allocator,
            exec_stream,
            aux_stream,
            h2d_stream,
            mem_size,
            device_id,
            device_properties,
            reversed_allocation_placement: false,
        };
        Ok(context)
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

    pub fn get_mem_size(&self) -> usize {
        self.mem_size
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
