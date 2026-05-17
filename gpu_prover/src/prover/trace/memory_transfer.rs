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
// — it stays a standalone caps-producer (see `gpu_prover/src/prover/memory.rs`).
// Callers obtain `Vec<MerkleTreeCapVarLength>` from `MemoryCommitmentJob::finish()`
// and hand it here.

use std::marker::PhantomData;
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::Digest;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use crate::primitives::transfer::Transfer;
use crate::prover::trace::holder::bitreverse_index;
use crate::upstream::MerkleTreeCapVarLength;

pub(crate) struct GpuGKRMemoryTransferHost {
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
    pub(crate) fn from_per_coset_caps(
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

pub(crate) struct GpuGKRMemoryTransfer<'a> {
    pub(crate) host: Arc<GpuGKRMemoryTransferHost>,
    pub(crate) unified_device_cap: DeviceAllocation<Digest>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> GpuGKRMemoryTransfer<'a> {
    pub(crate) fn new(
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
