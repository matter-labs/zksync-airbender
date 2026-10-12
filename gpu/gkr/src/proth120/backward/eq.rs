use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_prover_context::ProverContext;

use super::scheduled_execution::{note_device, ResourceEventPr};
use crate::backward::{GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN};
pub(crate) use crate::proth120::forward::kernels::launch_eq_high_low as launch_eq_high_low_pr;
use crate::upstream::PR;

pub(crate) const PR_FOLD_WEIGHT_SLOTS: usize = 11;

pub(crate) struct BackwardScratchPr {
    pub(crate) eq_high: DeviceAllocation<PR>,
    pub(crate) fold_weights: DeviceAllocation<PR>,
}

impl BackwardScratchPr {
    pub(crate) fn new(context: &ProverContext) -> CudaResult<Self> {
        let scratch = Self {
            eq_high: context.alloc(2 * GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)?,
            fold_weights: context.alloc(PR_FOLD_WEIGHT_SLOTS, AllocationPlacement::BestFit)?,
        };
        scratch.note_resources(context, "backward", ResourceEventPr::Allocated);
        Ok(scratch)
    }

    pub(crate) fn note_resources(
        &self,
        context: &ProverContext,
        stage: &'static str,
        event: ResourceEventPr,
    ) {
        note_device(
            context,
            stage,
            None,
            event,
            "bwd.scratch.eq_high",
            &self.eq_high,
        );
        note_device(
            context,
            stage,
            None,
            event,
            "bwd.scratch.fold_weights",
            &self.fold_weights,
        );
    }

    pub(crate) fn eq_high_0(&mut self) -> *mut PR {
        self.eq_high.as_mut_ptr()
    }

    pub(crate) fn eq_high_1(&mut self) -> *mut PR {
        unsafe { self.eq_high.as_mut_ptr().add(GKR_EQ_GROUP_TABLE_LEN) }
    }
}

pub(crate) fn resolve_active_eq_slot_pr(
    eq_sizes: &GkrEqSizes,
    eq_low: *mut PR,
    eq_high_0: *mut PR,
    eq_high_1: *mut PR,
) -> (*mut PR, u32) {
    if eq_sizes.low > 0 {
        (eq_low, eq_sizes.low)
    } else if eq_sizes.high[1] > 0 {
        (eq_high_1, eq_sizes.high[1])
    } else {
        assert!(
            eq_sizes.high[0] >= 1,
            "Proth120 eq state drained past empty"
        );
        (eq_high_0, eq_sizes.high[0])
    }
}
