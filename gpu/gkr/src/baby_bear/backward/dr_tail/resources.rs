//! Device limits asserted while scheduling the DR tail.
use crate::backward::dr_tail::capacity::{DrTailCapacityDecision, DrTailCapacityRequest};
use era_cudart::result::CudaResult;
use gpu_prover_context::ProverContext;

use crate::{
    baby_bear::backward::dr_tail::capacity::select_capacity, backward::dr_tail::resources::*,
};

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
        let attributes = crate::baby_bear::backward::dr_tail::kernels::dr_tail_attributes()?;
        assert_eq!(
            attributes.local_bytes, 0,
            "DR-tail kernel spills to local memory"
        );
        Ok(Self {
            attributes,
            device_cap_bytes: crate::backward::dr_tail::kernels::dr_tail_device_optin_cap_bytes(
                device_id,
            )?,
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
            crate::baby_bear::backward::dr_tail::kernels::set_dr_tail_max_dynamic_smem_bytes(
                capacity.dynamic_smem_bytes,
            )?;
            self.attributes = crate::baby_bear::backward::dr_tail::kernels::dr_tail_attributes()?;
            assert!(capacity.dynamic_smem_bytes <= self.attributes.max_dynamic_smem_bytes);
        }
        assert_ne!(
            crate::baby_bear::backward::dr_tail::kernels::dr_tail_occupancy(
                capacity.dynamic_smem_bytes
            )?,
            0
        );
        Ok(capacity)
    }
}
