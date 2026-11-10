//! Device limits asserted while scheduling the DR tail.

use super::capacity::{select_capacity, DrTailCapacityDecision, DrTailCapacityRequest};
use era_cudart::result::CudaResult;
use gpu_prover_context::ProverContext;

pub(crate) const DR_TAIL_OCCUPANCY_THREADS: u32 = super::kernels::DR_TAIL_BLOCK_THREADS;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrTailRawAttributes {
    pub static_smem_bytes: usize,
    pub local_bytes: usize,
    pub max_dynamic_smem_bytes: usize,
}

pub(crate) fn dr_continuation_window_count(entry_round: usize) -> usize {
    if entry_round == 0 {
        return 0;
    }
    debug_assert!(entry_round >= 3 && entry_round.is_multiple_of(3));
    (entry_round - 3) / 3
}

pub(crate) struct DrTailResources {
    attributes: DrTailRawAttributes,
    device_cap_bytes: usize,
}

impl DrTailResources {
    pub(crate) fn new(context: &ProverContext) -> CudaResult<Self> {
        let device_id = era_cudart::device::get_device()?;
        assert_eq!(
            device_id,
            context.get_device_id(),
            "proof scheduling must run on the context device"
        );
        let attributes = super::kernels::dr_tail_attributes()?;
        assert_eq!(
            attributes.local_bytes, 0,
            "DR-tail kernel spills to local memory"
        );
        Ok(Self {
            attributes,
            device_cap_bytes: super::kernels::dr_tail_device_optin_cap_bytes(device_id)?,
        })
    }

    pub(crate) fn capacity(
        &mut self,
        folding_steps: usize,
        canonical_sources: usize,
    ) -> CudaResult<DrTailCapacityDecision> {
        let capacity = select_capacity(DrTailCapacityRequest {
            folding_steps,
            canonical_sources,
            static_smem_bytes: self.attributes.static_smem_bytes,
            device_cap_bytes: self.device_cap_bytes,
        });
        // Never lower the kernel-wide ceiling: an earlier proof may still use it.
        if capacity.dynamic_smem_bytes > self.attributes.max_dynamic_smem_bytes {
            super::kernels::set_dr_tail_max_dynamic_smem_bytes(capacity.dynamic_smem_bytes)?;
            self.attributes = super::kernels::dr_tail_attributes()?;
            assert!(capacity.dynamic_smem_bytes <= self.attributes.max_dynamic_smem_bytes);
        }
        assert_ne!(
            super::kernels::dr_tail_occupancy(capacity.dynamic_smem_bytes)?,
            0
        );
        Ok(capacity)
    }
}
