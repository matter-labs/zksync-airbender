// Pre-prove H2D transfer of the memory base-layer Merkle cap.
//
// Mirrors the setup transfer's "scheduling-time-known cap" pattern: caller
// stages the per-coset memory caps produced by `MemoryCommitmentJob` into a
// single contiguous pinned host buffer (canonical bit-reversed coset order),
// allocates a matching device buffer up front, and `schedule_transfer` H2Ds
// the pinned buffer into the device cap on `h2d_stream` (overlapped with the
// prior proof's exec work, outside the WHIR hot range). `prove()` then D2Ds
// the device cap into the proof slab's `whir.memory.cap` range.
//
// `MemoryCommitmentJob` itself is intentionally not threaded into `prove()`
// — it stays a standalone caps-producer (see `gpu/circuit_prover/src/prover/memory.rs`).
// Callers obtain `Vec<MerkleTreeCapVarLength>` from `MemoryCommitmentJob::finish()`
// and hand it here.

use std::marker::PhantomData;
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::Digest;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use crate::prover::trace::decoder::DecoderTableTransfer;
use crate::prover::trace::holder::bitreverse_index;
use crate::prover::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::prover::transfer::Transfer;
use crate::prover::ProverContext;
use crate::upstream::MerkleTreeCapVarLength;

pub struct GpuGKRMemoryTransferHost {
    pub(crate) log_lde_factor: u32,
    pub(crate) log_tree_cap_size: u32,
    /// Single contiguous Merkle cap of length `1 << log_tree_cap_size`, stored
    /// in canonical bit-reversed coset order — same layout as the device-side
    /// unified cap that `prove()` consumes.
    pub(crate) unified_tree_cap: StaticPinnedBox<Digest>,
}

impl GpuGKRMemoryTransferHost {
    /// Repacks the per-coset caps produced by `MemoryCommitmentJob` (in natural
    /// coset order) into the canonical bit-reversed unified-cap layout used by
    /// the device side. `log_lde_factor` and `log_tree_cap_size` are the same
    /// geometry that the memory commitment job was configured with; they are
    /// captured here so `schedule_transfer` does not need to re-derive them.
    pub fn from_per_coset_caps(
        memory_tree_caps: &[MerkleTreeCapVarLength],
        log_lde_factor: u32,
        log_tree_cap_size: u32,
    ) -> CudaResult<Self> {
        let lde_factor = 1usize << log_lde_factor;
        assert_eq!(
            memory_tree_caps.len(),
            lde_factor,
            "memory tree caps must contain one entry per coset",
        );
        let cap_size = 1usize << log_tree_cap_size;
        let per_coset = cap_size >> log_lde_factor;
        let mut unified_tree_cap = alloc_static_pinned_box_uninit::<Digest>(cap_size)?;
        for stage1_pos in 0..lde_factor {
            let natural_coset_index = bitreverse_index(stage1_pos, log_lde_factor);
            let src = &memory_tree_caps[natural_coset_index].cap;
            assert_eq!(
                src.len(),
                per_coset,
                "memory tree cap[{natural_coset_index}] length mismatch",
            );
            unified_tree_cap[stage1_pos * per_coset..(stage1_pos + 1) * per_coset]
                .copy_from_slice(src);
        }
        Ok(Self {
            log_lde_factor,
            log_tree_cap_size,
            unified_tree_cap,
        })
    }
}

pub struct GpuGKRMemoryTransfer<'a> {
    pub(crate) host: Arc<GpuGKRMemoryTransferHost>,
    pub(crate) unified_device_cap: DeviceAllocation<Digest>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> GpuGKRMemoryTransfer<'a> {
    pub fn new(
        host: Arc<GpuGKRMemoryTransferHost>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let cap_size = 1usize << host.log_tree_cap_size;
        let unified_device_cap = context.alloc::<Digest>(cap_size, AllocationPlacement::BestFit)?;
        Ok(Self {
            host,
            unified_device_cap,
            _marker: PhantomData,
        })
    }

    pub(crate) fn schedule_transfer(
        &mut self,
        transfer: &mut Transfer<'a>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        transfer.ensure_allocated(context)?;
        let stream = context.get_h2d_stream();
        memory_copy_async(
            &mut self.unified_device_cap,
            &self.host.unified_tree_cap[..],
            stream,
        )
    }

    pub(crate) fn unified_device_cap(&self) -> &DeviceAllocation<Digest> {
        &self.unified_device_cap
    }
}

// ---------------------------------------------------------------------------
// GpuGKRCommitMemoryTransfer
// ---------------------------------------------------------------------------

/// Bundle for `commit_memory_from_transfers()` — same shape as
/// `GpuGKRProofTransfer` but only carrying the pieces the memory-commitment
/// path consumes (decoder, inits_and_teardowns, tracing_data; no setup,
/// memory caps, or challenges).
pub struct GpuGKRCommitMemoryTransfer<'a, A: GoodAllocator> {
    pub(crate) transfer: Transfer<'a>,
    pub(crate) decoder: Option<DecoderTableTransfer<'a>>,
    pub(crate) inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a>>,
    pub(crate) tracing_data: Option<TracingDataTransfer<'a, A>>,
}

pub(crate) struct GpuGKRCommitMemoryTransferKeepalive<'a, A: GoodAllocator> {
    pub(crate) decoder: Option<DecoderTableTransfer<'a>>,
    pub(crate) inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a>>,
    pub(crate) tracing_data: Option<TracingDataTransfer<'a, A>>,
    _callbacks: Callbacks<'a>,
}

impl<'a, A: GoodAllocator + 'a> GpuGKRCommitMemoryTransfer<'a, A> {
    pub fn new(
        decoder: Option<DecoderTableTransfer<'a>>,
        inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a>>,
        tracing_data: Option<TracingDataTransfer<'a, A>>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            transfer,
            decoder,
            inits_and_teardowns,
            tracing_data,
        })
    }

    pub fn schedule(&mut self, context: &ProverContext) -> CudaResult<()> {
        if let Some(decoder) = self.decoder.as_mut() {
            decoder.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(it) = self.inits_and_teardowns.as_mut() {
            it.schedule_transfer(&mut self.transfer, context)?;
        }
        if let Some(td) = self.tracing_data.as_mut() {
            td.schedule_transfer(&mut self.transfer, context)?;
        }
        self.transfer.record_transferred(context)
    }

    pub(crate) fn ensure_transferred(&self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.ensure_transferred(context)
    }

    pub(crate) fn into_keepalive(self) -> GpuGKRCommitMemoryTransferKeepalive<'a, A> {
        let Self {
            transfer,
            decoder,
            inits_and_teardowns,
            tracing_data,
        } = self;
        GpuGKRCommitMemoryTransferKeepalive {
            decoder,
            inits_and_teardowns,
            tracing_data,
            _callbacks: transfer.into_callbacks(),
        }
    }
}
