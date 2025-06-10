use crate::allocator::host::ConcurrentStaticHostAllocator;
use crate::context::Context;
use era_cudart::device::{get_device, set_device};
use era_cudart::memory::{memory_get_info, CudaHostAllocFlags, HostAllocation};
use era_cudart::memory_pools::{
    AttributeHandler, CudaMemPoolAttributeU64, CudaOwnedMemPool, DevicePoolAllocation,
};
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSliceMut, DeviceSlice};
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaError;
use fft::GoodAllocator;
use field::Mersenne31Field;
use std::marker::PhantomData;
use std::ops::DerefMut;

static DEFAULT_STREAM: CudaStream = CudaStream::DEFAULT;

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
    type HostAllocator: GoodAllocator;
    type Allocation<T: Sync>: DerefMut<Target = DeviceSlice<T>> + CudaSliceMut<T> + Sync;
    fn is_host_allocator_initialized() -> bool;
    fn initialize_host_allocator(
        host_allocations_count: usize,
        blocks_per_allocation_count: usize,
        block_log_size: u32,
    ) -> CudaResult<()>;
    fn get_device_id(&self) -> i32;
    fn switch_to_device(&self) -> CudaResult<()>;
    fn get_exec_stream(&self) -> &CudaStream;
    fn get_h2d_stream(&self) -> &CudaStream;
    fn alloc<T: Sync>(&self, size: usize) -> CudaResult<Self::Allocation<T>>;
    fn free<T: Sync>(&self, allocation: Self::Allocation<T>) -> CudaResult<()>;
    fn get_used_mem_current(&self) -> CudaResult<usize>;
    fn get_used_mem_high(&self) -> CudaResult<usize>;
    fn get_reserved_mem_current(&self) -> CudaResult<usize>;
    fn get_reserved_mem_high(&self) -> CudaResult<usize>;
    fn reset_used_mem_high(&self) -> CudaResult<()>;

    #[cfg(feature = "print_gpu_mem_usage")]
    fn print_mem_pool_stats(&self) -> CudaResult<()> {
        let used_mem_current = self.get_used_mem_current()?;
        let used_mem_high = self.get_used_mem_high()?;
        println!(
            "GPU memory usage current/high: {}/{} GB",
            used_mem_current as f64 / ((1 << 30) as f64),
            used_mem_high as f64 / ((1 << 30) as f64),
        );
        Ok(())
    }
}

pub struct MemPoolProverContext<'a> {
    _inner: Context,
    pub(crate) exec_stream: CudaStream,
    pub(crate) h2d_stream: CudaStream,
    pub(crate) mem_pool: CudaOwnedMemPool,
    pub(crate) device_id: i32,
    _phantom: PhantomData<&'a ()>,
}

impl<'a> MemPoolProverContext<'a> {
    pub fn new(config: &ProverContextConfig) -> CudaResult<Self> {
        assert!(ConcurrentStaticHostAllocator::is_initialized_global());
        let inner = Context::create(12)?;
        let exec_stream = CudaStream::create()?;
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
        println!(
            "initialized GPU memory pool for device ID {device_id} with {} GB of usable memory",
            (size << config.allocation_block_log_size) as f32 / 1024.0 / 1024.0 / 1024.0
        );
        mem_pool.set_attribute(CudaMemPoolAttributeU64::AttrUsedMemHigh, 0)?;
        DEFAULT_STREAM.synchronize()?;
        let context = Self {
            _inner: inner,
            exec_stream,
            h2d_stream,
            mem_pool,
            device_id,
            _phantom: PhantomData,
        };
        Ok(context)
    }
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
        println!(
            "initialized ConcurrentStaticHostAllocator with {host_allocations_count} x {} GB",
            host_allocation_size as f32 / 1024.0 / 1024.0 / 1024.0
        );
        Ok(())
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
            println!(
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
}
