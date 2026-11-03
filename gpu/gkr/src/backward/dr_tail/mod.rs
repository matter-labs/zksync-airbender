pub(crate) mod capacity;
mod kernels;
pub(crate) mod resources;

pub(crate) use kernels::{
    launch_dr_tail_megakernel_e4, DrTailMegakernelDesc, DrTailSlot, DR_TAIL_MAX_SOURCES,
    DR_TAIL_SLOTS,
};
pub use resources::DrTailProofPlan;

/// Admit device-specific DR-tail resources before constructing transfers.
/// The returned plan owns this proof's DR programs and is passed to `prove()`.
pub fn preflight_dr_tail_resources(
    programs: &crate::GkrPrograms,
    final_trace_size_log_2: u32,
    device_id: i32,
) -> era_cudart::result::CudaResult<DrTailProofPlan> {
    let plan = resources::admit_dr_tail_resources(
        device_id,
        programs.runtime_circuit().as_ref(),
        final_trace_size_log_2 as usize,
        programs.compile_dr_window_programs(final_trace_size_log_2),
    )?;
    for layer in plan.layers() {
        if resources::dr_continuation_window_count(layer.capacity().entry_round) != 0 {
            let program = plan
                .window_programs()
                .layer(layer.layer_idx())
                .expect("admitted DR layer program");
            gpu_gkr_compiler::validate_dr_window_split_ownership(program.input_projection())
                .unwrap_or_else(|error| {
                    panic!(
                        "DR continuation split admission at layer {}: {error}",
                        layer.layer_idx()
                    )
                });
        }
    }
    Ok(plan)
}
