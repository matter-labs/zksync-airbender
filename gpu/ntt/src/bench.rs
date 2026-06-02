//! Bench helpers for the WHIR forward-NTT path.
//!
//! Compares `bitreversed_monomials_to_natural_evals` (strategy-routed multi-
//! stage NTT) against the prior per-column single-stage `bitreversed_coeffs_to
//! _natural_coset` fallback. Gated behind the `bench` feature and exposed only
//! to the `benches/ntt.rs` Criterion entry.
//!
//! Self-contained (no `ProverContext`): like gpu_ntt's tests it uses a raw
//! `DeviceContext` (to initialize the twiddle `__constant__` tables), plain
//! `era_cudart` `DeviceAllocation`s, and a queried `DeviceProperties`.
//!
//! L2-bypass: a single iteration of either kernel touches `2^log_n` BF
//! elements per buffer; on Blackwell-class L2 (~96 MB) a small `log_n` re-run
//! over the same allocation reads entirely from L2 and reports an unreliable
//! timing. The harness therefore allocates a 256 MB pool per side (input and
//! output) and round-robins through "slots" sized `2^log_n` so the working
//! set sweeps past L2 capacity at every per-log_n bench.

use std::mem::size_of;

use era_cudart::memory::DeviceAllocation;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use crate::ntt::{bitreversed_coeffs_to_natural_coset, bitreversed_monomials_to_natural_evals};
use crate::ntt_twiddles::DeviceContext;
use gpu_core::primitives::context::DeviceProperties;
use gpu_core::primitives::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkMut};
use gpu_core::primitives::field::BF;

/// 256 MB per side. Targets ~2.5x the L2 of an RTX PRO 6000 Blackwell so
/// round-robined iterations evict cleanly before reuse. For log_n=20 (16 MB
/// per slot) the pool fits 16 slots; for log_n=4 it fits millions.
const POOL_BYTES_PER_SIDE: usize = 256 * 1024 * 1024;

/// `powers_of_w_coarse_log_count` for the twiddle context. Matches the
/// `GMEM_COARSE_LOG_COUNT` default used by the prover (and gpu_ntt's tests).
const TWIDDLE_LOG_COUNT: u32 = 13;

pub struct NttBenchHarness {
    /// Keeps the NTT twiddle `__constant__` tables alive for the harness'
    /// lifetime (the launchers read them).
    _device_context: DeviceContext,
    pub log_n: usize,
    pub log_lde_factor: usize,
    pub coset_index: usize,
    props: DeviceProperties,
    inputs_pool: DeviceAllocation<BF>,
    outputs_pool: DeviceAllocation<BF>,
    slot_count: usize,
    slot_size: usize,
    next_slot: usize,
}

impl NttBenchHarness {
    pub fn new(log_n: usize, log_lde_factor: usize, coset_index: usize) -> CudaResult<Self> {
        let _device_context = DeviceContext::create(TWIDDLE_LOG_COUNT)?;
        let props = DeviceProperties::new()?;
        let slot_size = 1usize << log_n;
        let pool_elems = POOL_BYTES_PER_SIDE / size_of::<BF>();
        // At least 4 slots even at huge log_n; ensures round-robin actually
        // rotates between iterations.
        let slot_count = (pool_elems / slot_size).max(4);
        let pool_total = slot_count * slot_size;
        let inputs_pool = DeviceAllocation::<BF>::alloc(pool_total)?;
        let outputs_pool = DeviceAllocation::<BF>::alloc(pool_total)?;
        Ok(Self {
            _device_context,
            log_n,
            log_lde_factor,
            coset_index,
            props,
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
            &self.props,
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
