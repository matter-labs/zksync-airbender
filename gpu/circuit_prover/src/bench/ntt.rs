//! Bench helpers for the WHIR forward-NTT path.
//!
//! Compares `bitreversed_monomials_to_natural_evals` (strategy-routed multi-
//! stage NTT) against the prior per-column single-stage `bitreversed_coeffs_to
//! _natural_coset` fallback. Gated behind the `bench` feature and exposed only
//! to the `benches/ntt.rs` Criterion entry.
//!
//! L2-bypass: a single iteration of either kernel touches `2^log_n` BF
//! elements per buffer; on Blackwell-class L2 (~96 MB) a small `log_n` re-run
//! over the same allocation reads entirely from L2 and reports an unreliable
//! timing. The harness therefore allocates a 256 MB pool per side (input and
//! output) and round-robins through "slots" sized `2^log_n` so the working
//! set sweeps past L2 capacity at every per-log_n bench.

use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::ntt::{
    bitreversed_coeffs_to_natural_coset, bitreversed_monomials_to_natural_evals,
};
use crate::primitives::context::DeviceAllocation;
use crate::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};
use crate::primitives::field::BF;
use crate::prover::{ProverContext, ProverContextConfig};
use std::mem::size_of;

/// 256 MB per side. Targets ~2.5x the L2 of an RTX PRO 6000 Blackwell so
/// round-robined iterations evict cleanly before reuse. For log_n=20 (16 MB
/// per slot) the pool fits 16 slots; for log_n=4 it fits millions.
const POOL_BYTES_PER_SIDE: usize = 256 * 1024 * 1024;

pub struct NttBenchHarness {
    pub context: ProverContext,
    pub log_n: usize,
    pub log_lde_factor: usize,
    pub coset_index: usize,
    inputs_pool: DeviceAllocation<BF>,
    outputs_pool: DeviceAllocation<BF>,
    slot_count: usize,
    slot_size: usize,
    next_slot: usize,
}

impl NttBenchHarness {
    pub fn new(log_n: usize, log_lde_factor: usize, coset_index: usize) -> CudaResult<Self> {
        let mut config = ProverContextConfig::default();
        // 1 GB device arena: 512 MB for input+output pools plus headroom for
        // the prover-context bookkeeping.
        config.max_device_allocation_blocks_count = Some(1024);
        let host_block_size = 1usize << config.host_allocator_block_log_size;
        config.host_allocator_blocks_count = (32 * 1024 * 1024) / host_block_size;
        let context = ProverContext::new(&config)?;
        let slot_size = 1usize << log_n;
        let pool_elems = POOL_BYTES_PER_SIDE / size_of::<BF>();
        // At least 4 slots even at huge log_n; ensures round-robin actually
        // rotates between iterations.
        let slot_count = (pool_elems / slot_size).max(4);
        let pool_total = slot_count * slot_size;
        let inputs_pool = context.alloc(pool_total, AllocationPlacement::BestFit)?;
        let outputs_pool = context.alloc(pool_total, AllocationPlacement::BestFit)?;
        Ok(Self {
            context,
            log_n,
            log_lde_factor,
            coset_index,
            inputs_pool,
            outputs_pool,
            slot_count,
            slot_size,
            next_slot: 0,
        })
    }

    fn advance(&mut self) -> usize {
        let slot = self.next_slot;
        self.next_slot = (self.next_slot + 1) % self.slot_count;
        slot * self.slot_size
    }

    pub fn run_new_path(&mut self, stream: &CudaStream) -> CudaResult<()> {
        let n = self.slot_size;
        let offset = self.advance();
        let log_n = self.log_n;
        let log_lde_factor = self.log_lde_factor;
        let coset_index = self.coset_index;
        // Copy the scalar fields out of the immutable borrow so we can hold
        // the mutable pool borrows below without conflict.
        let props_ref = self.context.get_device_properties();
        let l2_cache_size_bytes = props_ref.l2_cache_size_bytes;
        let sm_count = props_ref.sm_count;
        let compute_capability_major = props_ref.compute_capability_major;
        let compute_capability_minor = props_ref.compute_capability_minor;
        let device_props = crate::primitives::context::DeviceProperties {
            l2_cache_size_bytes,
            sm_count,
            compute_capability_major,
            compute_capability_minor,
        };
        let inputs_matrix = DeviceMatrixChunk::new(&self.inputs_pool[offset..offset + n], n, 0, n);
        let mut outputs_matrix =
            DeviceMatrixChunkMut::new(&mut self.outputs_pool[offset..offset + n], n, 0, n);
        bitreversed_monomials_to_natural_evals(
            &inputs_matrix,
            &mut outputs_matrix,
            log_n,
            log_lde_factor,
            coset_index,
            false,
            stream,
            &device_props,
        )
    }

    pub fn run_old_path(&mut self, stream: &CudaStream) -> CudaResult<()> {
        let n = self.slot_size;
        let offset = self.advance();
        let outputs_slice = &mut self.outputs_pool[offset..offset + n];
        let inputs_slice = unsafe {
            DeviceSlice::from_raw_parts(self.inputs_pool.as_ptr(), self.inputs_pool.len())
        };
        bitreversed_coeffs_to_natural_coset(
            &inputs_slice[offset..offset + n],
            outputs_slice,
            self.log_n,
            self.log_lde_factor,
            self.coset_index,
            stream,
        )
    }
}
