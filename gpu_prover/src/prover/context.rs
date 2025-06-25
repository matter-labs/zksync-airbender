use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::context::Context;
use era_cudart::device::{device_get_attribute, get_device, set_device};
use era_cudart::memory::{memory_get_info, CudaHostAllocFlags, HostAllocation};
use era_cudart::memory_pools::{
    AttributeHandler, CudaMemPoolAttributeU64, CudaOwnedMemPool, DevicePoolAllocation,
};
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSliceMut, DeviceSlice};
use era_cudart::stream::CudaStream;
use era_cudart_sys::{CudaDeviceAttr, CudaError};
use fft::GoodAllocator;
use field::Mersenne31Field;
use log::error;
use std::marker::PhantomData;
use std::ops::DerefMut;

static DEFAULT_STREAM: CudaStream = CudaStream::DEFAULT;

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
            allocation_block_log_size: 22,
            device_slack_blocks: 1,
        }
    }
}

pub trait ProverContext {
    type HostAllocator: GoodAllocator + 'static;
    type Allocation<T: Sync>: DerefMut<Target = DeviceSlice<T>> + CudaSliceMut<T> + Sync;
    fn is_host_allocator_initialized() -> bool;
    fn initialize_host_allocator(
        host_allocations_count: usize,
        blocks_per_allocation_count: usize,
        block_log_size: u32,
    ) -> CudaResult<()>;
    fn new(config: &ProverContextConfig) -> CudaResult<Self>
    where
        Self: Sized;
    fn get_device_id(&self) -> i32;
    fn switch_to_device(&self) -> CudaResult<()>;
    fn get_exec_stream(&self) -> &CudaStream;
    fn get_aux_stream(&self) -> &CudaStream;
    fn get_h2d_stream(&self) -> &CudaStream;
    fn alloc<T: Sync>(&self, size: usize) -> CudaResult<Self::Allocation<T>>;
    fn free<T: Sync>(&self, allocation: Self::Allocation<T>) -> CudaResult<()>;
    fn get_mem_size(&self) -> usize;
    fn get_used_mem_current(&self) -> CudaResult<usize>;
    fn get_used_mem_high(&self) -> CudaResult<usize>;
    fn get_reserved_mem_current(&self) -> CudaResult<usize>;
    fn get_reserved_mem_high(&self) -> CudaResult<usize>;
    fn reset_used_mem_high(&self) -> CudaResult<()>;
    fn get_device_properties(&self) -> &DeviceProperties;

    #[cfg(feature = "log_gpu_mem_usage")]
    fn log_mem_pool_stats(&self, location: &str) -> CudaResult<()> {
        let used_mem_current = self.get_used_mem_current()?;
        let used_mem_high = self.get_used_mem_high()?;
        log::debug!(
            "GPU memory usage {location} current/high: {}/{} GB",
            used_mem_current as f64 / ((1 << 30) as f64),
            used_mem_high as f64 / ((1 << 30) as f64),
        );
        Ok(())
    }
}

pub struct MemPoolProverContext<'a> {
    _inner: Context,
    pub(crate) exec_stream: CudaStream,
    pub(crate) aux_stream: CudaStream,
    pub(crate) h2d_stream: CudaStream,
    pub(crate) mem_pool: CudaOwnedMemPool,
    pub(crate) mem_size: usize,
    pub(crate) device_id: i32,
    pub(crate) device_properties: DeviceProperties,
    _phantom: PhantomData<&'a ()>,
}

impl<'a> ProverContext for MemPoolProverContext<'a> {
    type HostAllocator = ConcurrentStaticHostAllocator;
    type Allocation<T: Sync> = DevicePoolAllocation<'a, T>;

    fn is_host_allocator_initialized() -> bool {
        ConcurrentStaticHostAllocator::is_initialized_global()
    }

    fn initialize_host_allocator(
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

    fn new(config: &ProverContextConfig) -> CudaResult<Self> {
        assert!(ConcurrentStaticHostAllocator::is_initialized_global());
        let inner = Context::create(config.powers_of_w_coarse_log_count)?;
        let exec_stream = CudaStream::create()?;
        let aux_stream = CudaStream::create()?;
        let h2d_stream = CudaStream::create()?;
        let device_id = get_device()?;
        let mem_pool = CudaOwnedMemPool::create_for_device(device_id)?;
        mem_pool.set_attribute(CudaMemPoolAttributeU64::AttrReleaseThreshold, u64::MAX)?;
        let (free, _) = memory_get_info()?;
        let mut size = (free >> config.allocation_block_log_size) - config.device_slack_blocks;
        loop {
            match DevicePoolAllocation::<Mersenne31Field>::alloc_from_pool_async(
                size << config.allocation_block_log_size,
                &mem_pool,
                &DEFAULT_STREAM,
            ) {
                Ok(dummy) => {
                    dummy.free_async(&DEFAULT_STREAM)?;
                    break;
                }
                Err(CudaError::ErrorMemoryAllocation) => {
                    let last_error = era_cudart::error::get_last_error();
                    if last_error != CudaError::ErrorMemoryAllocation {
                        return Err(last_error);
                    }
                    size -= 1;
                }
                Err(e) => return Err(e),
            }
            if let Ok(dummy) = DevicePoolAllocation::<u8>::alloc_from_pool_async(
                size << config.allocation_block_log_size,
                &mem_pool,
                &DEFAULT_STREAM,
            ) {
                dummy.free_async(&DEFAULT_STREAM)?;
                break;
            } else {
                size -= 1;
            }
        }
        let mem_size = size << config.allocation_block_log_size;
        mem_pool.set_attribute(CudaMemPoolAttributeU64::AttrUsedMemHigh, 0)?;
        DEFAULT_STREAM.synchronize()?;
        let device_properties = DeviceProperties::new()?;
        let context = Self {
            _inner: inner,
            exec_stream,
            aux_stream,
            h2d_stream,
            mem_pool,
            mem_size,
            device_id,
            device_properties,
            _phantom: PhantomData,
        };
        Ok(context)
    }

    fn get_device_id(&self) -> i32 {
        self.device_id
    }

    fn switch_to_device(&self) -> CudaResult<()> {
        set_device(self.device_id)
    }

    fn get_exec_stream(&self) -> &CudaStream {
        &self.exec_stream
    }

    fn get_aux_stream(&self) -> &CudaStream {
        &self.aux_stream
    }

    fn get_h2d_stream(&self) -> &CudaStream {
        &self.h2d_stream
    }

    fn alloc<T: Sync>(&self, size: usize) -> CudaResult<Self::Allocation<T>> {
        assert_ne!(size, 0);
        let result = DevicePoolAllocation::<T>::alloc_from_pool_async(
            size,
            &self.mem_pool,
            &self.exec_stream,
        );
        let result: CudaResult<Self::Allocation<T>> = unsafe { std::mem::transmute(result) };
        if result.is_err() {
            error!(
                "failed to allocate {} bytes from GPU memory pool of device ID {}, currently allocated {} bytes",
                size * size_of::<T>(),
                self.device_id,
                self.get_used_mem_current()?
            );
        }
        result
    }

    fn free<T: Sync>(&self, allocation: Self::Allocation<T>) -> CudaResult<()> {
        allocation.free_async(&self.exec_stream)
    }

    fn get_mem_size(&self) -> usize {
        self.mem_size
    }

    fn get_used_mem_current(&self) -> CudaResult<usize> {
        self.mem_pool
            .get_attribute(CudaMemPoolAttributeU64::AttrUsedMemCurrent)
            .map(|x| x as usize)
    }

    fn get_used_mem_high(&self) -> CudaResult<usize> {
        self.mem_pool
            .get_attribute(CudaMemPoolAttributeU64::AttrUsedMemHigh)
            .map(|x| x as usize)
    }

    fn get_reserved_mem_current(&self) -> CudaResult<usize> {
        self.mem_pool
            .get_attribute(CudaMemPoolAttributeU64::AttrReservedMemCurrent)
            .map(|x| x as usize)
    }

    fn get_reserved_mem_high(&self) -> CudaResult<usize> {
        self.mem_pool
            .get_attribute(CudaMemPoolAttributeU64::AttrReservedMemHigh)
            .map(|x| x as usize)
    }

    fn reset_used_mem_high(&self) -> CudaResult<()> {
        self.mem_pool
            .set_attribute(CudaMemPoolAttributeU64::AttrUsedMemHigh, 0)
    }

    fn get_device_properties(&self) -> &DeviceProperties {
        &self.device_properties
    }
}
