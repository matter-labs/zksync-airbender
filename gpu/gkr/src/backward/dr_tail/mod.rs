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
    let plan = resources::admit_dr_tail_resources(
        &kernels::DrTailCudaQueries { device_id },
        programs.runtime_circuit().as_ref(),
        final_trace_size_log_2 as usize,
    )?;
    let bundle = programs.resolve_dr_window_programs(final_trace_size_log_2);
    for layer in plan.layers() {
        if layer.execution_plan().continuation_window_count() != 0 {
            let program = bundle
                .layer(layer.layer_idx())
                .expect("admitted DR layer program");
            let slots = program.program().slot_count();
            let capacity = super::window_dr::dr_window_partials_len(program.folding_steps());
            for pass in 0..layer.execution_plan().continuation_window_count() {
                let round = 3 + 3 * pass;
                let tiles = 1usize << program.folding_steps().saturating_sub(round + 8);
                let required = 27 * (tiles * slots + 1);
                assert!(required <= capacity,
                    "DR continuation split partials exceed admitted capacity at layer {} round {}: {} > {}",
                    layer.layer_idx(), round, required, capacity);
            }
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
