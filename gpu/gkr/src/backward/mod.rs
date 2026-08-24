use std::collections::BTreeMap;

use era_cudart::result::CudaResult;

use super::GpuGKRStorage;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

mod dim_reducing_encoder;
mod dim_reducing_sumcheck_plan;
mod dr_tail;
pub mod kernels;
mod main_layer;
pub mod round_timing;
mod scheduled_execution;
mod stage_snapshots;
pub(crate) mod vm;
pub mod window;
pub(crate) mod window_dr;

#[doc(hidden)]
pub use dr_tail::dr_tail_first_order_mismatch;

pub(crate) use kernels::*;
pub use kernels::{
    eq_group_count, eq_group_tables_len, gkr_dim_reducing_launch_config,
    launch_build_eq_values_from_point, make_eq_sizes, ClaimBufferLayout, GkrEqSizes,
    GpuGKRBackwardScheduledExecution, GpuGKRDimensionReducingBackwardState, GKR_EQ_GROUP_TABLE_LEN,
    GKR_EQ_HIGH_SLOTS,
};
#[doc(hidden)]
pub use stage_snapshots::{GKRBackwardStageSnapshot, GKRBackwardStageSnapshotSink};
#[doc(hidden)]
pub use vm::continuation_golden::{
    build_continuation_golden, compile_corpus_layout, continuation_golden_path, decode_golden,
    encode_golden, ContinuationGoldenDto, GoldenEntry, CONTINUATION_GOLDEN_CORPUS,
};
#[doc(hidden)]
pub use vm::production_bind::{continuation_snapshot, legacy_continuation_snapshot};

pub(crate) use main_layer::extras::derive_dimension_reducing_inputs;

use crate::upstream::{DimensionReducingInputOutput, GKRAddress, OutputType};
use main_layer::blueprints::build_dimension_reducing_slots_static;

#[cfg(test)]
pub(crate) fn legacy_dimension_reducing_slots_for_test(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
) -> GpuGKRDimensionReducingLayerSlots {
    build_dimension_reducing_slots_static(layer)
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
        options: crate::GkrBackwardOptions,
        strategy: crate::BackwardExecutionStrategy,
    ) -> GpuGKRMainLayerBackwardState {
        assert!(
            self.pending_layers.is_empty(),
            "main-layer handoff requires dimension-reducing layers to be exhausted"
        );
        let compiled_circuit = programs.runtime_circuit();
        let num_layers = compiled_circuit.layers.len();
        let trace_len = compiled_circuit.trace_len;
        let teardown_sets = compiled_circuit.memory_layout.teardown_sets.len();
        if strategy == crate::BackwardExecutionStrategy::WindowedR0 {
            assert!(
                programs.window_programs_ready(),
                "the windowed arm requires a resolved window program bundle"
            );
        }
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
            strategy,
            window_tail: options.window_tail,
        }
    }
}

impl GpuGKRDimensionReducingBackwardState {
    fn prepare_layer_from_slots(
        &mut self,
        layer_idx: usize,
        layer_slots: GpuGKRDimensionReducingLayerSlots,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingSumcheckLayerPlan> {
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

        let round0_batch_template_compact =
            self::dim_reducing_encoder::build_round0_batch_compact(&layer_slots, &self.storage);
        let max_acc_size = trace_len_after_reduction / 2;
        let partials_len = kernels::max_partials_len(max_acc_size);
        let partials = context.alloc(partials_len, AllocationPlacement::Top)?;

        let round_scratch = GpuGKRDimensionReducingRoundScratch {
            eq_low_group: context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?,
            accumulator: context.alloc(max_acc_size * 2, AllocationPlacement::Top)?,
            partials,
        };

        self.next_trace_len_after_reduction *= 2;

        Ok(GpuGKRDimensionReducingSumcheckLayerPlan {
            layer_idx,
            trace_len_after_reduction,
            folding_steps,
            layer_slots,
            folding_addresses: dim_reducing_ext_inputs.into_iter().collect(),
            round0_batch_template_compact,
            round_scratch,
            eq_sizes: GkrEqSizes::zeroed(),
        })
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRDimensionReducingSumcheckLayerPlan>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };
        let layer_slots = build_dimension_reducing_slots_static(&layer);
        Ok(Some(self.prepare_layer_from_slots(
            layer_idx,
            layer_slots,
            context,
        )?))
    }
}

#[cfg(test)]
mod tests;
