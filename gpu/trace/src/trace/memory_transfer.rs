//! H2D transfer of a memory Merkle cap. Per-coset host caps are packed into a
//! contiguous host buffer in bit-reversed coset order and staged into a
//! matching device allocation on `h2d_stream`.

use std::marker::PhantomData;
use std::sync::Arc;

use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::trace::decoder::DecoderTableTransfer;
use crate::trace::holder::bitreverse_index;
use crate::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::upstream::{
    BaseCommitmentGeometry, BaseOracleRole, CommitmentMode, MerkleTreeCapVarLength,
};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_hash::blake2s::Digest;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;

#[cfg(test)]
mod tests;

pub struct GpuGKRMemoryTransferHost {
    base_geometry: Option<BaseCommitmentGeometry>,
    pub log_lde_factor: u32,
    pub log_tree_cap_size: u32,
    /// Single contiguous Merkle cap of length `1 << log_tree_cap_size`, stored
    /// in canonical bit-reversed coset order, matching the device-side cap.
    pub(crate) unified_tree_cap: Vec<Digest>,
}

impl GpuGKRMemoryTransferHost {
    /// Packs naturally ordered per-coset caps into one bit-reversed cap.
    /// `log_lde_factor` specifies the number of cosets; `log_tree_cap_size`
    /// specifies the total cap size across all cosets.
    pub fn from_per_coset_caps(
        memory_tree_caps: &[MerkleTreeCapVarLength],
        log_lde_factor: u32,
        log_tree_cap_size: u32,
    ) -> Self {
        let lde_factor = 1usize
            .checked_shl(log_lde_factor)
            .expect("memory cap LDE shift overflow");
        let cap_size = 1usize
            .checked_shl(log_tree_cap_size)
            .expect("memory cap size shift overflow");
        assert!(
            cap_size >= lde_factor,
            "memory cap needs at least one node per coset"
        );
        assert_eq!(
            memory_tree_caps.len(),
            lde_factor,
            "memory tree caps must contain one entry per coset",
        );
        let per_coset = cap_size >> log_lde_factor;
        let mut unified_tree_cap = Vec::with_capacity(cap_size);
        for stage1_pos in 0..lde_factor {
            let natural_coset_index = bitreverse_index(stage1_pos, log_lde_factor);
            let src = &memory_tree_caps[natural_coset_index].cap;
            assert_eq!(
                src.len(),
                per_coset,
                "memory tree cap[{natural_coset_index}] length mismatch",
            );
            unified_tree_cap.extend_from_slice(src);
        }
        Self {
            base_geometry: None,
            log_lde_factor,
            log_tree_cap_size,
            unified_tree_cap,
        }
    }

    /// Bind GPU-internal cap metadata to the producing commitment geometry.
    /// This retains the CPU pipeline's trust in the supplied cap contents.
    pub fn from_per_coset_caps_for_geometry(
        caps: &[MerkleTreeCapVarLength],
        geometry: BaseCommitmentGeometry,
    ) -> Self {
        let log_lde = geometry.lde_factor().trailing_zeros();
        let log_cap = geometry.cap_size().trailing_zeros();
        let mut host = if geometry.oracle(BaseOracleRole::Memory).physical_columns() == 0 {
            assert_eq!(
                caps.len(),
                geometry.lde_factor(),
                "empty memory cap coset count mismatch"
            );
            assert!(
                caps.iter().all(|cap| cap.cap.is_empty()),
                "empty memory oracle has empty caps"
            );
            Self {
                base_geometry: None,
                log_lde_factor: log_lde,
                log_tree_cap_size: log_cap,
                unified_tree_cap: Vec::new(),
            }
        } else {
            Self::from_per_coset_caps(caps, log_lde, log_cap)
        };
        host.base_geometry = Some(geometry);
        host.validate_for_geometry(&geometry);
        host
    }

    pub fn base_commitment_geometry(&self) -> Option<BaseCommitmentGeometry> {
        self.base_geometry
    }

    pub fn validate_for_geometry(&self, geometry: &BaseCommitmentGeometry) {
        assert_eq!(
            self.log_lde_factor,
            geometry.lde_factor().trailing_zeros(),
            "memory cap LDE geometry mismatch"
        );
        assert_eq!(
            self.log_tree_cap_size,
            geometry.cap_size().trailing_zeros(),
            "memory cap size geometry mismatch"
        );
        if let Some(producing) = self.base_geometry {
            assert_eq!(
                producing, *geometry,
                "memory cap producing geometry mismatch"
            );
        } else {
            assert!(
                geometry.pack_log2() == 0
                    && !geometry.is_virtual_packing()
                    && geometry.commitment_mode() == CommitmentMode::SeparateMemoryAndWitness,
                "legacy memory cap lacks packed, virtual or merged geometry"
            );
        }
        let expected = if geometry.oracle(BaseOracleRole::Memory).physical_columns() == 0 {
            0
        } else {
            geometry.cap_size()
        };
        assert_eq!(
            self.unified_tree_cap.len(),
            expected,
            "memory cap payload length mismatch"
        );
    }
}

pub struct GpuGKRMemoryTransfer<'a> {
    pub host: Arc<GpuGKRMemoryTransferHost>,
    pub(crate) unified_device_cap: DeviceAllocation<Digest>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> GpuGKRMemoryTransfer<'a> {
    pub fn new(host: Arc<GpuGKRMemoryTransferHost>, context: &ProverContext) -> CudaResult<Self> {
        let cap_size = if let Some(geometry) = host.base_geometry {
            host.validate_for_geometry(&geometry);
            host.unified_tree_cap.len()
        } else {
            let cap_size = 1usize
                .checked_shl(host.log_tree_cap_size)
                .expect("memory cap size shift overflow");
            assert_eq!(
                host.unified_tree_cap.len(),
                cap_size,
                "memory cap payload length mismatch"
            );
            cap_size
        };
        let unified_device_cap = context.alloc::<Digest>(cap_size, AllocationPlacement::BestFit)?;
        Ok(Self {
            host,
            unified_device_cap,
            _marker: PhantomData,
        })
    }

    pub fn stage_transfer(&mut self, transfer: &mut Transfer<'a>) {
        transfer.stage(&self.host.unified_tree_cap, &mut self.unified_device_cap);
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
    pub(crate) inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a, A>>,
    pub(crate) tracing_data: Option<TracingDataTransfer<'a, A>>,
}

impl<'a, A: GoodAllocator + 'a> GpuGKRCommitMemoryTransfer<'a, A> {
    pub fn new(
        decoder: Option<DecoderTableTransfer<'a>>,
        inits_and_teardowns: Option<InitsAndTeardownsTransfer<'a, A>>,
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
