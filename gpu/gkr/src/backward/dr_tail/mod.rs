pub(crate) mod capacity;
mod kernels;
pub(crate) mod resources;

pub(crate) use kernels::{
    launch_dr_tail_megakernel_e4, DrTailMegakernelDesc, DrTailSlot, DR_TAIL_MAX_SOURCES,
    DR_TAIL_SLOTS,
};
pub use resources::DrTailProofPlan;

/// Production entry point: admit DR-tail kernel resources for this proof.
///
/// Call after the landed pure preflight and before constructing any transfer.
/// The returned plan is owned by the caller and threaded explicitly into
/// `prove()`; nothing is cached in `GkrPrograms`.
///
pub fn preflight_dr_tail_resources(
    programs: &crate::GkrPrograms,
    final_trace_size_log_2: u32,
    device_id: i32,
) -> era_cudart::result::CudaResult<DrTailProofPlan> {
    resources::admit_dr_tail_resources(
        &kernels::DrTailCudaQueries { device_id },
        programs.runtime_circuit().as_ref(),
        final_trace_size_log_2 as usize,
    )
}
