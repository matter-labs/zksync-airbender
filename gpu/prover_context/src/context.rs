use crate::replay::{self, CachedGraph, PoolId, ReplayInputs};
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::memory::{memory_get_info, CudaHostAllocFlags};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr;
use gpu_core::allocator::device::{
    NonConcurrentStaticDeviceAllocator, StaticDeviceAllocationBackend,
};
use gpu_core::allocator::host::NonConcurrentStaticHostAllocator;
use gpu_core::allocator::tracker::{AllocationDirection, AllocationPlacement, UNBOUNDED};
use gpu_core::primitives::context::{
    DeviceAllocation, DeviceAllocator, DeviceProperties, HostAllocation, HostAllocator,
    UnsafeMutAccessor,
};
use gpu_core::primitives::graph::CudaGraph;
use gpu_ntt::ntt_twiddles::DeviceContext;
use log::error;
use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Range;

/// SM-dependent workspaces are sized for this many SMs, so their sizes do not
/// depend on the device.
pub const MAX_SM_COUNT: usize = 256;

/// Capacity of the pinned staging buffer behind `Transfer::stage`.
pub(crate) const H2D_STAGING_BYTES: usize = 1 << 16;

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
    pub small_allocator_pool_blocks: usize,
    /// See [`AllocationMode`].
    pub inputs_reserve_bytes: usize,
    pub cuda_graph_mode: CudaGraphMode,
}

/// `Ascending` works from the low arena end and `Descending` mirrors it from
/// the high end. Inputs are packed within `inputs_reserve_bytes` of their end;
/// a proof never enters the reserve at the opposite end.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum AllocationMode {
    Unbounded,
    Inputs(AllocationDirection),
    Proof(AllocationDirection),
}

/// Whether [`ProverContext::replay_phase`] caches and replays CUDA graphs
/// (`Replay`) or enqueues its phase directly (`Eager`).
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum CudaGraphMode {
    Eager,
    Replay,
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
            cuda_graph_mode: CudaGraphMode::Eager,
        }
    }
}

pub struct ProverContext {
    // Own the device-resident twiddle tables for the full lifetime of the prover context.
    _device_context: DeviceContext,
    device_allocator: DeviceAllocator,
    small_device_allocators: Option<[DeviceAllocator; 2]>,
    host_allocator: HostAllocator,
    h2d_staging: era_cudart::memory::HostAllocation<u8>,
    h2d_staging_fill_target: UnsafeMutAccessor<[u8]>,
    exec_stream: CudaStream,
    h2d_stream: CudaStream,
    device_allocator_mem_size: usize,
    allocator_block_log_size: u32,
    arena: Range<usize>,
    inputs_reserve_bytes: usize,
    allocation_mode: AllocationMode,
    cuda_graph_mode: CudaGraphMode,
    graph_cache: RefCell<HashMap<(String, Option<AllocationDirection>), CachedGraph>>,
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
        assert!(
            mpc <= MAX_SM_COUNT,
            "device has {mpc} SMs, more than MAX_SM_COUNT ({MAX_SM_COUNT})"
        );
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
        let small_pools_bytes = small_device_allocators
            .as_ref()
            .map_or(0, |_| small_pool_bytes);
        let arena = arena_start + small_pools_bytes..arena_end - small_pools_bytes;
        let inputs_reserve_bytes = config.inputs_reserve_bytes;
        assert!(
            2 * inputs_reserve_bytes <= arena.len(),
            "inputs reserves of 2 x {inputs_reserve_bytes} bytes exceed the {}-byte arena",
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
        let mut h2d_staging = era_cudart::memory::HostAllocation::alloc(
            H2D_STAGING_BYTES,
            CudaHostAllocFlags::DEFAULT,
        )?;
        let h2d_staging_fill_target = UnsafeMutAccessor::new(&mut h2d_staging[..]);
        let device_properties = DeviceProperties::new()?;
        let context = Self {
            _device_context: device_context,
            device_allocator,
            small_device_allocators,
            host_allocator,
            h2d_staging,
            h2d_staging_fill_target,
            exec_stream,
            h2d_stream,
            device_allocator_mem_size,
            allocator_block_log_size,
            arena,
            inputs_reserve_bytes,
            allocation_mode: AllocationMode::Unbounded,
            cuda_graph_mode: config.cuda_graph_mode,
            graph_cache: RefCell::default(),
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

    /// The NTT twiddle/triangle `DeviceContext` owned for the prover's lifetime.
    /// The forward-NTT launchers (DIT engine + compact) read its precomputed
    /// CLEAN/COUPLED triangles and `__constant__` twiddle tables.
    pub fn ntt_device_context(&self) -> &DeviceContext {
        &self._device_context
    }

    pub fn get_h2d_stream(&self) -> &CudaStream {
        &self.h2d_stream
    }

    pub(crate) fn h2d_staging_source(&self) -> &[u8] {
        &self.h2d_staging
    }

    pub(crate) fn h2d_staging_fill_target(&self) -> UnsafeMutAccessor<[u8]> {
        self.h2d_staging_fill_target
    }

    #[track_caller]
    pub fn alloc<T>(
        &self,
        size: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<DeviceAllocation<T>> {
        self.alloc_aligned(size, placement, align_of::<T>())
    }

    #[track_caller]
    pub fn alloc_with_extra_alignment<T, const EXTRA_ALIGNMENT_LOG2: u32>(
        &self,
        size: usize,
        placement: AllocationPlacement,
    ) -> CudaResult<DeviceAllocation<T>> {
        self.alloc_aligned(
            size,
            placement,
            align_of::<T>().max(1 << EXTRA_ALIGNMENT_LOG2),
        )
    }

    #[track_caller]
    fn alloc_aligned<T>(
        &self,
        size: usize,
        placement: AllocationPlacement,
        alignment: usize,
    ) -> CudaResult<DeviceAllocation<T>> {
        use AllocationDirection::{Ascending, Descending};
        let Range { start, end } = self.arena;
        let reserve = self.inputs_reserve_bytes;
        let (placement, bounds, direction) = match self.allocation_mode {
            AllocationMode::Unbounded => (placement, start..end, Ascending),
            AllocationMode::Inputs(Ascending) => (
                AllocationPlacement::Bottom,
                start..start + reserve,
                Ascending,
            ),
            AllocationMode::Inputs(Descending) => {
                (AllocationPlacement::Bottom, end - reserve..end, Descending)
            }
            AllocationMode::Proof(Ascending) => (placement, start..end - reserve, Ascending),
            AllocationMode::Proof(Descending) => (placement, start + reserve..end, Descending),
        };
        let bytes = size * size_of::<T>();
        let small = self.small_device_allocators.is_some()
            && bytes <= 1 << (self.allocator_block_log_size - 2);
        let (pool, bounds) = match (small, direction) {
            (false, _) => (0, bounds),
            (true, Ascending) => (1, UNBOUNDED),
            (true, Descending) => (2, UNBOUNDED),
        };
        let result = self
            .pool(pool)
            .alloc_in(size, placement, alignment, bounds, direction);
        if let Ok(allocation) = &result {
            replay::record_allocation(
                pool,
                allocation.as_ptr() as usize,
                allocation.allocated_bytes(),
            );
        }
        if result.is_err() {
            if let AllocationMode::Inputs(direction) = self.allocation_mode {
                panic!(
                    "{bytes}-byte input does not fit the {reserve}-byte {direction:?} inputs reserve"
                );
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
        self.allocation_mode = mode;
    }

    pub fn cuda_graph_mode(&self) -> CudaGraphMode {
        self.cuda_graph_mode
    }

    #[doc(hidden)]
    pub fn set_cuda_graph_mode(&mut self, mode: CudaGraphMode) {
        self.cuda_graph_mode = mode;
    }

    /// Runs `phase`, which enqueues work on exec, after `before_launch`. In
    /// `Replay` mode the phase is captured once per `key` and allocation
    /// direction and replayed afterwards.
    ///
    /// On replay `phase` does not run. The device ranges allocated before the
    /// phase that it reads (`inputs`) must be where they were at capture. The
    /// device memory the phase allocated must be free except where it reuses
    /// its inputs, and the registered kernel patches are re-applied from
    /// `replay_inputs`. Returns `metadata` of the phase's result, cached at
    /// capture, and the result itself when the phase ran.
    pub fn replay_phase<R, M: Clone + 'static>(
        &self,
        key: &str,
        inputs: &[(usize, usize)],
        replay_inputs: &ReplayInputs,
        before_launch: impl FnOnce() -> CudaResult<()>,
        phase: impl FnOnce() -> CudaResult<R>,
        metadata: impl FnOnce(&R) -> M,
    ) -> CudaResult<(M, Option<R>)> {
        if self.cuda_graph_mode == CudaGraphMode::Eager {
            before_launch()?;
            let result = phase()?;
            return Ok((metadata(&result), Some(result)));
        }
        let direction = match self.allocation_mode {
            AllocationMode::Unbounded => None,
            AllocationMode::Proof(direction) => Some(direction),
            AllocationMode::Inputs(_) => panic!("graph phases run in proof allocation mode"),
        };
        let cache_key = (key.to_owned(), direction);
        let stream = &self.exec_stream;
        if let Some(cached) = self.graph_cache.borrow().get(&cache_key) {
            assert_eq!(
                inputs, cached.inputs,
                "inputs of replayed graph `{key}` moved since capture"
            );
            for &(pool, addr, len) in &cached.footprint {
                for (addr, len) in replay::subtract_ranges(addr, len, inputs) {
                    assert!(
                        self.pool(pool).is_free(addr, len),
                        "replayed graph `{key}` overlaps a live allocation in {addr:#x}+{len:#x}"
                    );
                }
            }
            for patch in &cached.patches {
                patch(&cached.exec, replay_inputs)?;
            }
            before_launch()?;
            cached.exec.launch(stream)?;
            let metadata = cached
                .metadata
                .downcast_ref::<M>()
                .expect("cached graph metadata has a different type")
                .clone();
            return Ok((metadata, None));
        }
        replay::begin_record();
        let captured = CudaGraph::capture(stream, phase);
        let record = replay::end_record();
        let (graph, result) = captured?;
        let metadata = metadata(&result);
        let exec = graph.instantiate()?;
        before_launch()?;
        exec.launch(stream)?;
        let cached = CachedGraph {
            exec,
            _graph: graph,
            patches: record.patches,
            inputs: inputs.to_vec(),
            footprint: replay::merge_footprint(record.footprint),
            metadata: Box::new(metadata.clone()),
        };
        self.graph_cache.borrow_mut().insert(cache_key, cached);
        Ok((metadata, Some(result)))
    }

    #[doc(hidden)]
    pub fn cached_graph_count(&self) -> usize {
        self.graph_cache.borrow().len()
    }

    fn pool(&self, pool: PoolId) -> &DeviceAllocator {
        match (pool, &self.small_device_allocators) {
            (0, _) => &self.device_allocator,
            (1 | 2, Some(small)) => &small[pool - 1],
            _ => unreachable!("unknown allocator pool {pool}"),
        }
    }
}

#[cfg(test)]
mod tests;
