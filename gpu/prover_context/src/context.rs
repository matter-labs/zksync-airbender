use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::memory::{memory_get_info, CudaHostAllocFlags};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr;
use gpu_core::allocator::device::{
    NonConcurrentStaticDeviceAllocator, StaticDeviceAllocationBackend,
};
use gpu_core::allocator::host::NonConcurrentStaticHostAllocator;
use gpu_core::allocator::is_small_allocation;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::{
    DeviceAllocation, DeviceAllocator, DeviceProperties, HostAllocation, HostAllocator,
};
use gpu_ntt::ntt_twiddles::DeviceContext;
use log::error;
use std::ops::Range;

#[derive(Copy, Clone, Debug)]
pub struct ProverContextConfig {
    pub powers_of_w_coarse_log_count: u32,
    pub allocator_block_log_size: u32,
    pub device_slack_static_bytes: usize,
    pub device_slack_per_thread_bytes: usize,
    /// Exact arena size in blocks, including the small pool. `None` uses
    /// available memory rounded down to whole blocks. Allocation never shrinks.
    pub device_allocation_blocks_count: Option<usize>,
    pub host_allocator_block_log_size: u32,
    pub host_allocator_blocks_count: usize,
    pub small_allocator_log_chunk_size: Option<u32>,
    /// Blocks of each of the two small pools, carved at the two ends of the arena.
    pub small_allocator_pool_blocks: usize,
    /// Arena bytes at the far end that proof-mode allocations never use; they
    /// hold the next request's inputs. See [`AllocationMode`].
    pub inputs_reserve_bytes: usize,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum AllocationSide {
    Low,
    High,
}

/// Where allocations go. A side's outer end is the arena end it names; its
/// inputs are packed there, and its proof working set stops short of the
/// other side's `inputs_reserve_bytes`.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum AllocationMode {
    Unbounded,
    Inputs(AllocationSide),
    Proof(AllocationSide),
}

impl Default for ProverContextConfig {
    fn default() -> Self {
        Self {
            powers_of_w_coarse_log_count: 13,
            allocator_block_log_size: 20,            // 1 MB blocks
            device_slack_static_bytes: 1 << 27,      // 128 MB static slack
            device_slack_per_thread_bytes: 1 << 11,  // 2 KB per thread slack
            device_allocation_blocks_count: None,    // use all available memory
            host_allocator_block_log_size: 13, // 8 KB host blocks (small to avoid waste on tiny staging buffers)
            host_allocator_blocks_count: 163840, // 1.25 GB host allocator pool (163840 × 8 KB)
            small_allocator_log_chunk_size: Some(8), // 256-byte granularity for small device allocations
            small_allocator_pool_blocks: 16, // 16 blocks × 1 MB = 16 MB per small allocation pool
            inputs_reserve_bytes: 0,
        }
    }
}

pub struct ProverContext {
    // Own the device-resident twiddle tables for the full lifetime of the prover context.
    _device_context: DeviceContext,
    device_allocator: DeviceAllocator,
    small_device_allocators: Option<[DeviceAllocator; 2]>,
    host_allocator: HostAllocator,
    exec_stream: CudaStream,
    side_stream: CudaStream,
    h2d_stream: CudaStream,
    device_allocator_mem_size: usize,
    allocator_block_log_size: u32,
    arena: Range<usize>,
    inputs_reserve_bytes: usize,
    allocation_mode: AllocationMode,
    device_id: i32,
    device_properties: DeviceProperties,
}

impl ProverContext {
    pub fn new(config: &ProverContextConfig) -> CudaResult<Self> {
        Self::new_with_auto_arena_size(config, |available| available)
    }

    /// Selects an automatic arena from memory remaining after slack and context
    /// allocations. Explicit block counts bypass the selector.
    pub fn new_with_auto_arena_size(
        config: &ProverContextConfig,
        select: impl FnOnce(usize) -> usize,
    ) -> CudaResult<Self> {
        let block_size = 1usize
            .checked_shl(config.allocator_block_log_size)
            .expect("allocator_block_log_size must be less than usize::BITS");
        if let Some(blocks) = config.device_allocation_blocks_count {
            assert!(blocks > 0, "device arena must contain at least one block");
            assert!(
                blocks.checked_mul(block_size).is_some(),
                "device arena size overflows usize: {blocks} blocks of {block_size} bytes"
            );
            if config.small_allocator_log_chunk_size.is_some() {
                assert!(
                    blocks >= 2 * config.small_allocator_pool_blocks,
                    "device arena has {blocks} blocks but the small allocator pools require {}",
                    2 * config.small_allocator_pool_blocks
                );
            }
        }
        // host_typed allocations rely on the host pool's block size being at
        // least 32 bytes so any `T` whose alignment is ≤32 is satisfied by the
        // block address (matches FIELD_ALIGN; see `proof/layout/mod.rs`).
        assert!(
            config.host_allocator_block_log_size >= 5,
            "host_allocator_block_log_size must be >= 5 (32-byte blocks) for host_typed alignment"
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
        let side_stream = CudaStream::create()?;
        let h2d_stream = CudaStream::create()?;
        let device_blocks_count = if let Some(blocks_count) = config.device_allocation_blocks_count
        {
            blocks_count
        } else {
            let (free, _) = memory_get_info()?;
            let bytes = select(free & !(block_size - 1));
            assert!(
                bytes > 0 && bytes <= free && bytes.is_multiple_of(block_size),
                "selected arena size {bytes} must be positive, block-aligned and fit in {free} available bytes"
            );
            let blocks = bytes / block_size;
            assert!(
                config.small_allocator_log_chunk_size.is_none()
                    || blocks >= 2 * config.small_allocator_pool_blocks,
                "selected arena has {blocks} blocks but the small allocator pools require {}",
                2 * config.small_allocator_pool_blocks
            );
            blocks
        };
        let device_allocation =
            era_cudart::memory::DeviceAllocation::<u8>::alloc(device_blocks_count * block_size)?;
        slack.free()?;
        let arena_start = device_allocation.as_ptr() as usize;
        let arena_end = arena_start + device_allocation.len();
        let device_allocation_backend = StaticDeviceAllocationBackend(device_allocation);
        let device_allocator = NonConcurrentStaticDeviceAllocator::new(
            [device_allocation_backend],
            allocator_block_log_size,
        );
        let small_pool_bytes = config.small_allocator_pool_blocks * block_size;
        let small_device_allocators = config
            .small_allocator_log_chunk_size
            .map(|small_log_chunk_size| {
                assert!(
                    small_log_chunk_size < allocator_block_log_size,
                    "small chunk size must be smaller than big chunk size"
                );
                assert!(
                    small_pool_bytes > 0,
                    "small pool size must be a positive multiple of the big chunk size"
                );
                let carve = |placement| {
                    device_allocator.carve(small_pool_bytes, placement, small_log_chunk_size)
                };
                CudaResult::Ok([
                    carve(AllocationPlacement::Bottom)?,
                    carve(AllocationPlacement::Top)?,
                ])
            })
            .transpose()?;
        let small_pools_bytes = if small_device_allocators.is_some() {
            small_pool_bytes
        } else {
            0
        };
        let arena = arena_start + small_pools_bytes..arena_end - small_pools_bytes;
        let inputs_reserve_bytes = config.inputs_reserve_bytes;
        assert!(
            inputs_reserve_bytes.is_multiple_of(block_size)
                && (inputs_reserve_bytes == 0 || 2 * inputs_reserve_bytes < arena.len()),
            "inputs reserve of {inputs_reserve_bytes} bytes must be block-aligned and leave room for proofs in a {}-byte arena",
            arena.len()
        );
        let device_allocator_mem_size = device_blocks_count * block_size;
        let host_block_log_size = config.host_allocator_block_log_size;
        let host_allocation_size = config.host_allocator_blocks_count << host_block_log_size;
        let host_allocation = era_cudart::memory::HostAllocation::alloc(
            host_allocation_size,
            CudaHostAllocFlags::DEFAULT,
        )?;
        let host_allocator =
            NonConcurrentStaticHostAllocator::new([host_allocation], host_block_log_size);
        let device_properties = DeviceProperties::new()?;
        let context = Self {
            _device_context: device_context,
            device_allocator,
            small_device_allocators,
            host_allocator,
            exec_stream,
            side_stream,
            h2d_stream,
            device_allocator_mem_size,
            allocator_block_log_size,
            arena,
            inputs_reserve_bytes,
            allocation_mode: AllocationMode::Unbounded,
            device_id,
            device_properties,
        };
        Ok(context)
    }

    pub fn get_host_allocator(&self) -> HostAllocator {
        self.host_allocator.clone()
    }

    pub fn get_exec_stream(&self) -> &CudaStream {
        &self.exec_stream
    }

    pub fn get_side_stream(&self) -> &CudaStream {
        &self.side_stream
    }

    /// The NTT twiddle/triangle `DeviceContext` owned for the prover's lifetime.
    /// The forward-NTT launchers (DIT engine + compact) read its precomputed
    /// CLEAN/COUPLED triangles and `__constant__` twiddle tables.
    pub fn ntt_device_context(&self) -> &DeviceContext {
        &self._device_context
    }

    pub fn get_h2d_stream(&self) -> &CudaStream {
        &self.h2d_stream
    }

    #[track_caller]
    pub fn alloc<T>(
        &self,
        size: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<DeviceAllocation<T>> {
        let (placement, bounds, side) = self.placement_for(placement);
        let result = match self.small_pool_for::<T>(size, side) {
            Some(pool) => pool.alloc::<T>(size, placement),
            None => self.device_allocator.alloc_in::<T>(size, placement, bounds),
        };
        self.check_allocation(result, size * size_of::<T>())
    }

    #[track_caller]
    pub fn alloc_with_extra_alignment<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &self,
        size: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<DeviceAllocation<T>> {
        let (placement, bounds, side) = self.placement_for(placement);
        let result = match self.small_pool_for::<T>(size, side) {
            Some(pool) => {
                pool.alloc_with_extra_alignment::<T, EXTRA_ALIGNMENT_LOG2>(size, placement)
            }
            None => self
                .device_allocator
                .alloc_with_extra_alignment_in::<T, EXTRA_ALIGNMENT_LOG2>(size, placement, bounds),
        };
        self.check_allocation(result, size * size_of::<T>())
    }

    fn placement_for(
        &self,
        placement: AllocationPlacement,
    ) -> (AllocationPlacement, Range<usize>, AllocationSide) {
        let Range { start, end } = self.arena;
        let reserve = self.inputs_reserve_bytes;
        let mirrored = match placement {
            AllocationPlacement::BestFit => AllocationPlacement::BestFit,
            AllocationPlacement::Bottom => AllocationPlacement::Top,
            AllocationPlacement::Top => AllocationPlacement::Bottom,
        };
        match self.allocation_mode {
            AllocationMode::Unbounded => (placement, start..end, AllocationSide::Low),
            AllocationMode::Inputs(AllocationSide::Low) => (
                AllocationPlacement::Bottom,
                start..start + reserve,
                AllocationSide::Low,
            ),
            AllocationMode::Inputs(AllocationSide::High) => (
                AllocationPlacement::Top,
                end - reserve..end,
                AllocationSide::High,
            ),
            AllocationMode::Proof(AllocationSide::Low) => {
                (placement, start..end - reserve, AllocationSide::Low)
            }
            AllocationMode::Proof(AllocationSide::High) => {
                (mirrored, start + reserve..end, AllocationSide::High)
            }
        }
    }

    fn small_pool_for<T>(&self, size: usize, side: AllocationSide) -> Option<&DeviceAllocator> {
        let pools = self.small_device_allocators.as_ref()?;
        is_small_allocation(size * size_of::<T>(), self.allocator_block_log_size).then(
            || match side {
                AllocationSide::Low => &pools[0],
                AllocationSide::High => &pools[1],
            },
        )
    }

    #[track_caller]
    fn check_allocation<T>(
        &self,
        result: CudaResult<DeviceAllocation<T>>,
        bytes: usize,
    ) -> CudaResult<DeviceAllocation<T>> {
        if result.is_err() {
            if let AllocationMode::Inputs(side) = self.allocation_mode {
                if !is_small_allocation(bytes, self.allocator_block_log_size)
                    || self.small_device_allocators.is_none()
                {
                    panic!(
                        "input bundle exceeds the {}-byte next-inputs reserve on the {side:?} side ({bytes}-byte request at {})",
                        self.inputs_reserve_bytes,
                        std::panic::Location::caller()
                    );
                }
            }
            error!(
                "failed to allocate {} bytes from GPU memory allocator of device ID {}, currently allocated {} bytes",
                bytes,
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
    /// inverted-access rule in `gpu/docs/gpu_scheduling_contract.md`, every read
    /// and write must come from a stream-scheduled op (host callback or
    /// `memory_copy_async`). The first stream op touching the buffer must be
    /// a write (an H2D from a callback-populated source, or a D2H of fresh
    /// device contents); reading from it before that is UB on the uninit
    /// memory.
    ///
    pub unsafe fn alloc_host_uninit_slice<T: Sized>(&self, len: usize) -> HostAllocation<[T]> {
        HostAllocation::new_uninit_slice_in(len, self.get_host_allocator())
    }

    pub fn get_mem_size(&self) -> usize {
        self.device_allocator_mem_size
    }

    pub fn get_used_mem_current(&self) -> usize {
        let used = self.device_allocator.get_used_mem_current();
        self.small_device_allocators
            .iter()
            .flatten()
            .fold(used, |used, pool| {
                used - pool.capacity() + pool.get_used_mem_current()
            })
    }

    #[doc(hidden)]
    pub fn get_used_mem_peak(&self) -> usize {
        self.device_allocator.get_used_mem_peak()
    }

    pub fn reset_used_mem_peak(&self) {
        self.device_allocator.reset_used_mem_peak();
    }

    pub fn get_device_id(&self) -> i32 {
        self.device_id
    }

    pub fn get_device_properties(&self) -> &DeviceProperties {
        &self.device_properties
    }

    pub fn set_allocation_mode(&mut self, mode: AllocationMode) {
        if let AllocationMode::Inputs(_) = mode {
            assert!(
                self.inputs_reserve_bytes > 0,
                "inputs mode requires a nonzero inputs_reserve_bytes"
            );
        }
        self.allocation_mode = mode;
    }
}

#[cfg(test)]
mod tests;
