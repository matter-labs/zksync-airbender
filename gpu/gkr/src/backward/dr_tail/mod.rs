pub(crate) mod capacity;
mod census;
mod kernels;
pub(crate) mod resources;

pub use capacity::{DrTailCapacityDecision, DrTailCapacityRejection, DrTailEntrySelection};
#[cfg(all(test, feature = "dr_tail_trace", not(no_cuda)))]
pub(crate) use kernels::*;
pub(crate) use kernels::{
    launch_dr_tail_megakernel_e4, DrTailMegakernelDesc, DrTailSlot, DR_TAIL_MAX_SOURCES,
    DR_TAIL_SLOTS,
};
pub use resources::{
    DrTailKernelResources, DrTailLayerPlan, DrTailPlanIdentityError, DrTailProofPlan,
    DrTailResourceError, DrTailScheduleError,
};

/// Production entry point: admit DR-tail kernel resources for this proof.
///
/// Call after the landed pure preflight and before constructing any transfer.
/// The returned plan is owned by the caller and threaded explicitly into
/// `prove()`; nothing is cached in `GkrPrograms`.
///
/// `entry` is [`DrTailEntrySelection::Portable`] on every production path. A
/// diagnostic neighbour is decided by the same capacity pass, so an illegal or
/// capacity-failing entry is a typed rejection here — before any transfer is
/// constructed and before anything is enqueued.
pub fn preflight_dr_tail_resources(
    programs: &crate::GkrPrograms,
    final_trace_size_log_2: u32,
    device_id: i32,
    entry: DrTailEntrySelection,
) -> Result<DrTailProofPlan, DrTailResourceError> {
    resources::admit_dr_tail_resources(
        &kernels::DrTailCudaQueries { device_id },
        programs.runtime_circuit().as_ref(),
        final_trace_size_log_2 as usize,
        entry,
    )
}

#[cfg(test)]
mod reference;
#[cfg(test)]
mod tests;

#[cfg(all(test, feature = "dr_tail_trace", not(no_cuda)))]
mod gpu_tests;

#[cfg(all(test, not(no_cuda)))]
mod gpu_resource_tests;

#[doc(hidden)]
pub use census::dr_tail_first_order_mismatch;
