//! H2D transfer of a memory Merkle cap. Per-coset host caps are packed into a
//! contiguous pinned buffer in bit-reversed coset order and copied into a
//! matching device allocation on `h2d_stream`.

use std::marker::PhantomData;
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::trace::decoder::DecoderTableTransfer;
use crate::trace::holder::bitreverse_index;
use crate::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::upstream::MerkleTreeCapVarLength;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use gpu_hash::blake2s::Digest;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;

pub struct GpuGKRMemoryTransferHost {
    pub log_lde_factor: u32,
    pub log_tree_cap_size: u32,
    /// Single contiguous Merkle cap of length `1 << log_tree_cap_size`, stored
    /// in canonical bit-reversed coset order, matching the device-side cap.
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
    pub host: Arc<GpuGKRMemoryTransferHost>,
    pub(crate) unified_device_cap: DeviceAllocation<Digest>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> GpuGKRMemoryTransfer<'a> {
    pub fn new(host: Arc<GpuGKRMemoryTransferHost>, context: &ProverContext) -> CudaResult<Self> {
        let cap_size = 1usize << host.log_tree_cap_size;
        let unified_device_cap = context.alloc::<Digest>(cap_size, AllocationPlacement::BestFit)?;
        Ok(Self {
            host,
            unified_device_cap,
            _marker: PhantomData,
        })
    }

    pub fn schedule_transfer(
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

    pub fn unified_device_cap(&self) -> &DeviceAllocation<Digest> {
        &self.unified_device_cap
    }
}

// ---------------------------------------------------------------------------
// GpuGKRCommitMemoryTransfer
// ---------------------------------------------------------------------------

/// Input transfers for `commit_memory_from_transfers`: decoder,
/// inits-and-teardowns, and tracing data share one transfer fence.
pub struct GpuGKRCommitMemoryTransfer<'a, A: GoodAllocator> {
    pub(crate) transfer: Transfer<'a>,
    pub(crate) decoder: Option<DecoderTableTransfer<'a>>,
    pub(crate) inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a>>,
    pub(crate) tracing_data: Option<TracingDataTransfer<'a, A>>,
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
}
