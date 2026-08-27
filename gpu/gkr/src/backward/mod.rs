use std::collections::BTreeMap;

use super::GpuGKRStorage;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

mod dim_reducing_sumcheck_plan;
mod dr_tail;
pub mod kernels;
pub mod main_continuation;
pub(crate) mod main_layer;
pub mod main_tail;
mod scheduled_execution;
mod stage_snapshots;
pub mod window;
pub(crate) mod window_dr;

pub use dr_tail::{preflight_dr_tail_resources, DrTailProofPlan};
pub(crate) use kernels::*;
pub use kernels::{
    eq_group_count, eq_group_tables_len, gkr_dim_reducing_launch_config,
    launch_build_eq_values_from_point, make_eq_sizes, ClaimBufferLayout, GkrEqSizes,
    GpuGKRBackwardScheduledExecution, GpuGKRDimensionReducingBackwardState, GKR_EQ_GROUP_TABLE_LEN,
    GKR_EQ_HIGH_SLOTS,
};
#[doc(hidden)]
pub use stage_snapshots::{GKRBackwardStageSnapshot, GKRBackwardStageSnapshotSink};
#[cfg(test)]
pub(crate) use window::bank::final_evaluation_repoint_probe;

#[cfg(test)]
pub(crate) use main_continuation::ContinuationPublishedShape;

pub(crate) use main_layer::extras::derive_dimension_reducing_inputs;

use crate::upstream::{DimensionReducingInputOutput, GKRAddress, OutputType};
use dr_tail::resources::DrTailPlanCursor;
use main_layer::blueprints::build_dimension_reducing_slots_static;

fn validate_dr_window_layer_program(
    program: &crate::DrWindowLayerProgram,
    layer_idx: usize,
    folding_steps: usize,
) {
    assert_eq!(
        program.layer(),
        layer_idx,
        "DR window preparation must use the absolute layer key"
    );
    assert_eq!(
        program.folding_steps(),
        folding_steps,
        "preflighted DR geometry must match the runtime layer"
    );
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DrWindowPassEqGeometry {
    build_offset: usize,
    challenge_count: usize,
    eq_sizes: GkrEqSizes,
}

fn dr_window_pass_eq_geometry(folding_steps: usize) -> DrWindowPassEqGeometry {
    const BUILD_OFFSET: usize = 3;
    let challenge_count = folding_steps
        .checked_sub(BUILD_OFFSET)
        .expect("preflighted DR R0 geometry must include the first three coordinates");
    DrWindowPassEqGeometry {
        build_offset: BUILD_OFFSET,
        challenge_count,
        eq_sizes: make_eq_sizes(challenge_count),
    }
}

impl GpuGKRDimensionReducingBackwardState {
    pub(super) fn new(
        forward_tracing_ranges: Vec<Range>,
        storage: GpuGKRStorage<BF, E4>,
        initial_layer_for_sumcheck: usize,
        dimension_reducing_inputs: BTreeMap<
            usize,
            BTreeMap<OutputType, DimensionReducingInputOutput>,
        >,
    ) -> Self {
        let first_output_addr = dimension_reducing_inputs[&initial_layer_for_sumcheck]
            .values()
            .next()
            .and_then(|io| io.output.first())
            .copied()
            .expect("dimension-reducing backward state requires at least one reduced output");
        let next_trace_len_after_reduction = storage.get_ext_poly(first_output_addr).len();
        let pending_layers = dimension_reducing_inputs.into_iter().rev().collect();

        Self {
            forward_tracing_ranges,
            storage,
            pending_layers,
            next_trace_len_after_reduction,
        }
    }
}

impl GpuGKRDimensionReducingBackwardState {
    pub(crate) fn into_main_layer_backward_state_static(
        self,
        inits_and_teardowns_top_bits: Vec<u32>,
        programs: std::sync::Arc<crate::GkrPrograms>,
    ) -> GpuGKRMainLayerBackwardState {
        assert!(
            self.pending_layers.is_empty(),
            "main-layer handoff requires dimension-reducing layers to be exhausted"
        );
        let compiled_circuit = programs.runtime_circuit();
        let num_layers = compiled_circuit.layers.len();
        let trace_len = compiled_circuit.trace_len;
        let teardown_sets = compiled_circuit.memory_layout.teardown_sets.len();
        assert!(programs.window_programs_ready());
        assert!(programs.main_continuation_window_programs_ready());
        assert!(programs.main_tail_programs_ready());
        GpuGKRMainLayerBackwardState {
            forward_tracing_ranges: self.forward_tracing_ranges,
            storage: self.storage,
            pending_layers: (0..num_layers).rev().collect(),
            trace_len,
            inits_and_teardowns_top_bits: {
                assert_eq!(
                    inits_and_teardowns_top_bits.len(),
                    teardown_sets,
                    "i&t top bits must have one entry per teardown set",
                );
                inits_and_teardowns_top_bits
            },
            programs,
        }
    }
}

impl GpuGKRDimensionReducingBackwardState {
    fn prepare_layer_from_slots(
        &mut self,
        layer_idx: usize,
        layer_slots: GpuGKRDimensionReducingLayerSlots,
        dr_window_program: &crate::DrWindowLayerProgram,
        dr_tail_plan_cursor: &mut DrTailPlanCursor<'_>,
        context: &ProverContext,
    ) -> era_cudart::result::CudaResult<GpuGKRDimensionReducingSumcheckLayerPlan> {
        let trace_len_after_reduction = self.next_trace_len_after_reduction;
        assert!(trace_len_after_reduction.is_power_of_two());
        let folding_steps = trace_len_after_reduction.trailing_zeros() as usize;
        assert!(folding_steps >= 2);
        assert_ne!(
            layer_slots.enabled_mask(),
            0,
            "dimension-reducing layer must enable at least one slot"
        );

        let aliases = self.storage.layout.as_ref().map(|layout| &layout.aliases);
        let dim_reducing_ext_inputs: std::collections::BTreeSet<GKRAddress> = layer_slots
            .input_addresses()
            .map(|address| {
                aliases
                    .and_then(|aliases| aliases.get(&address))
                    .copied()
                    .unwrap_or(address)
            })
            .collect();
        let folding_addresses: Vec<GKRAddress> = dim_reducing_ext_inputs.into_iter().collect();
        let dr_execution_plan =
            dr_tail_plan_cursor.bind(dr_tail::resources::DrTailLayerIdentity::new(
                layer_idx,
                folding_steps,
                &folding_addresses,
            ));
        let max_acc_size = trace_len_after_reduction / 2;
        validate_dr_window_layer_program(dr_window_program, layer_idx, folding_steps);
        let required_future_partials_len = window_dr::dr_window_partials_len(folding_steps);
        let retained_partials_len =
            kernels::max_partials_len(max_acc_size).max(required_future_partials_len);
        let mut partials = context.alloc(retained_partials_len, AllocationPlacement::Top)?;
        let eq_geometry = dr_window_pass_eq_geometry(folding_steps);
        let eq_low = context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?;
        let eq_pointer = eq_low.as_ptr();
        let eq = window_dr::DrWindowPassEqState {
            eq_low,
            eq_sizes: eq_geometry.eq_sizes,
            build_offset: eq_geometry.build_offset,
        };
        let dr_window = window_dr::prepare_dr_window_r0(
            dr_window_program.program(),
            dr_window_program.input_projection(),
            &self.storage,
            folding_steps,
            dr_execution_plan.continuation_window_count(),
            dr_execution_plan.megakernel_entry_round(),
            eq,
            required_future_partials_len,
            partials.as_mut_ptr(),
        )
        .expect("preflighted DR window program must bind to runtime storage");
        assert_eq!(dr_window.r0_launch.binding.batch.eq_low, eq_pointer);

        self.next_trace_len_after_reduction *= 2;

        Ok(GpuGKRDimensionReducingSumcheckLayerPlan {
            layer_idx,
            folding_steps,
            layer_slots,
            folding_addresses,
            dr_window: Some(dr_window),
            dr_execution_plan,
            _partials: partials,
        })
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        dr_window_programs: &crate::DrWindowProgramBundle,
        dr_tail_plan_cursor: &mut DrTailPlanCursor<'_>,
        context: &ProverContext,
    ) -> era_cudart::result::CudaResult<Option<GpuGKRDimensionReducingSumcheckLayerPlan>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };
        let layer_slots = build_dimension_reducing_slots_static(&layer);
        let dr_window_program = dr_window_programs.layer(layer_idx).unwrap_or_else(|| {
            panic!("preflighted DR window bundle is missing absolute layer {layer_idx}")
        });
        Ok(Some(self.prepare_layer_from_slots(
            layer_idx,
            layer_slots,
            dr_window_program,
            dr_tail_plan_cursor,
            context,
        )?))
    }
}

#[cfg(test)]
mod tests;
