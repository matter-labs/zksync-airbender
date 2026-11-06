//! H2D transfer of a memory Merkle cap. Per-coset host caps are packed into a
//! contiguous host buffer in bit-reversed coset order and staged into a
//! matching device allocation on `h2d_stream`.

use std::marker::PhantomData;
use std::sync::Arc;

use era_cudart::result::CudaResult;

use crate::trace::holder::bitreverse_index;
use crate::upstream::{BaseCommitmentGeometry, BaseOracleRole, MerkleTreeCapVarLength};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_hash::blake2s::Digest;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;

pub struct GpuGKRMemoryCapHost {
    base_geometry: BaseCommitmentGeometry,
    pub log_lde_factor: u32,
    pub log_tree_cap_size: u32,
    /// Single contiguous Merkle cap of length `1 << log_tree_cap_size`, stored
    /// in canonical bit-reversed coset order, matching the device-side cap.
    pub(crate) unified_tree_cap: Vec<Digest>,
}

impl GpuGKRMemoryCapHost {
    /// Packs naturally ordered per-coset caps into one bit-reversed cap bound
    /// to the producing commitment geometry.
    pub fn from_per_coset_caps_for_geometry(
        caps: &[MerkleTreeCapVarLength],
        geometry: BaseCommitmentGeometry,
    ) -> Self {
        let log_lde_factor = geometry.lde_factor().trailing_zeros();
        let log_tree_cap_size = geometry.cap_size().trailing_zeros();
        let lde_factor = geometry.lde_factor();
        let cap_size = geometry.cap_size();
        assert_eq!(
            caps.len(),
            lde_factor,
            "memory tree caps must contain one entry per coset"
        );
        let empty = geometry.oracle(BaseOracleRole::Memory).physical_columns() == 0;
        let per_coset = if empty { 0 } else { cap_size / lde_factor };
        for (index, cap) in caps.iter().enumerate() {
            assert_eq!(
                cap.cap.len(),
                per_coset,
                "memory tree cap[{index}] length mismatch"
            );
        }
        let mut unified_tree_cap = Vec::with_capacity(if empty { 0 } else { cap_size });
        for stage1_pos in 0..lde_factor {
            let natural_coset_index = bitreverse_index(stage1_pos, log_lde_factor);
            unified_tree_cap.extend_from_slice(&caps[natural_coset_index].cap);
        }
        Self {
            base_geometry: geometry,
            log_lde_factor,
            log_tree_cap_size,
            unified_tree_cap,
        }
    }

    /// A memory cap serves only proofs of the geometry it was produced for.
    pub fn validate_for_geometry(&self, geometry: &BaseCommitmentGeometry) {
        assert_eq!(
            self.base_geometry, *geometry,
            "memory cap producing geometry mismatch"
        );
    }
}

pub struct GpuGKRMemoryCapTransfer<'a> {
    pub host: Arc<GpuGKRMemoryCapHost>,
    pub(crate) unified_device_cap: DeviceAllocation<Digest>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> GpuGKRMemoryCapTransfer<'a> {
    pub fn new(host: Arc<GpuGKRMemoryCapHost>, context: &ProverContext) -> CudaResult<Self> {
        let cap_size = host.unified_tree_cap.len();
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
