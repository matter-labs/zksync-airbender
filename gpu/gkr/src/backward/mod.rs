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
pub mod main_continuation;
mod main_layer;
pub mod round_timing;
mod scheduled_execution;
mod stage_snapshots;
pub(crate) mod vm;
pub mod window;
pub(crate) mod window_dr;

#[doc(hidden)]
pub use dr_tail::dr_tail_first_order_mismatch;

pub use dr_tail::{
    preflight_dr_tail_resources, DrTailCapacityDecision, DrTailCapacityRejection,
    DrTailEntrySelection, DrTailKernelResources, DrTailLayerPlan, DrTailPlanIdentityError,
    DrTailProofPlan, DrTailResourceError, DrTailScheduleError,
};
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
    encode_golden, ContinuationGoldenDto, ContinuationStartRoundSnapshot, GoldenEntry,
    CONTINUATION_GOLDEN_CORPUS,
};
#[doc(hidden)]
pub use vm::production_bind::{
    continuation_snapshot, continuation_start_round_snapshot, legacy_continuation_snapshot,
};

#[cfg(test)]
pub(crate) use vm::production_bind::final_evaluation_repoint_probe;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DrWindowPreparationAllocationPolicy {
    r0_eq_owner_count: usize,
    retained_partials_len: usize,
    required_future_partials_len: Option<usize>,
}

fn dr_window_preparation_allocation_policy(
    max_acc_size: usize,
    folding_steps: usize,
    prepares_dr_window: bool,
) -> DrWindowPreparationAllocationPolicy {
    let legacy_partials_len = kernels::max_partials_len(max_acc_size);
    let required_future_partials_len =
        prepares_dr_window.then(|| window_dr::dr_window_partials_len(folding_steps));
    let retained_partials_len = required_future_partials_len.map_or(legacy_partials_len, |r0| {
        // Every continuation has a shorter suffix than R0, so the R0 maximum
        // covers the shared producer/tail scratch for the complete chain.
        window_dr::dr_window_partials_maximum(legacy_partials_len, r0, [])
    });
    DrWindowPreparationAllocationPolicy {
        r0_eq_owner_count: 1,
        retained_partials_len,
        required_future_partials_len,
    }
}

fn dr_legacy_accumulator_len(max_acc_size: usize, admitted_complete_chain: bool) -> Option<usize> {
    (!admitted_complete_chain).then(|| {
        max_acc_size
            .checked_mul(2)
            .expect("legacy DR accumulator length must fit usize")
    })
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
        dr_window_program: Option<&crate::DrWindowLayerProgram>,
        dr_window_bundle_final_log: Option<u32>,
        dr_tail_plan_cursor: Option<&mut DrTailPlanCursor<'_>>,
        options: crate::GkrBackwardOptions,
        strategy: crate::BackwardExecutionStrategy,
        context: &ProverContext,
    ) -> Result<GpuGKRDimensionReducingSumcheckLayerPlan, DrTailScheduleError> {
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
        let dr_execution_plan = dr_tail_plan_cursor
            .map(|cursor| {
                cursor.bind(dr_tail::resources::DrTailLayerIdentity::new(
                    layer_idx,
                    folding_steps,
                    &folding_addresses,
                ))
            })
            .transpose()?;
        let admitted_complete_chain = dr_execution_plan.is_some();
        if dr_execution_plan.is_some() {
            assert!(
                dr_window_program.is_some(),
                "an admitted complete-chain layer requires its preflighted window program",
            );
        }

        let round0_batch_template_compact =
            self::dim_reducing_encoder::build_round0_batch_compact(&layer_slots, &self.storage);
        let max_acc_size = trace_len_after_reduction / 2;
        if let Some(program) = dr_window_program {
            validate_dr_window_layer_program(program, layer_idx, folding_steps);
        }
        let allocation_policy = dr_window_preparation_allocation_policy(
            max_acc_size,
            folding_steps,
            dr_window_program.is_some(),
        );
        assert_eq!(
            allocation_policy.r0_eq_owner_count, 1,
            "both Task 6 arms must allocate exactly one common round Eq owner",
        );
        let partials = context.alloc(
            allocation_policy.retained_partials_len,
            AllocationPlacement::Top,
        )?;

        let mut round_scratch = GpuGKRDimensionReducingRoundScratch {
            eq_low_group: GpuGKRDimensionReducingEqLowGroup::owned(
                context.alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)?,
            ),
            accumulator: match dr_legacy_accumulator_len(max_acc_size, admitted_complete_chain) {
                Some(len) => GpuGKRDimensionReducingAccumulator::legacy_diagnostic(
                    context.alloc(len, AllocationPlacement::Top)?,
                ),
                None => GpuGKRDimensionReducingAccumulator::production_chain(),
            },
            partials,
        };

        let dr_window = if let Some(program) = dr_window_program {
            let eq_geometry = dr_window_pass_eq_geometry(folding_steps);
            debug_assert_eq!(
                eq_geometry.eq_sizes,
                make_eq_sizes(eq_geometry.challenge_count),
            );
            let eq_pointer = round_scratch.eq_low_group.as_ptr();
            let eq = window_dr::DrWindowPassEqState {
                eq_low: round_scratch.eq_low_group.take_owner(),
                eq_sizes: eq_geometry.eq_sizes,
                build_offset: eq_geometry.build_offset,
                owner_count: 1,
            };
            debug_assert_eq!(eq.eq_sizes, eq_geometry.eq_sizes);
            assert_eq!(eq.eq_low.as_ptr(), eq_pointer);
            let required_future_partials_len = allocation_policy
                .required_future_partials_len
                .expect("prepared DR window policy must retain its future partials requirement");
            let (continuation_window_count, megakernel_entry_round) = dr_execution_plan
                .map(|plan| {
                    (
                        plan.continuation_window_count(),
                        plan.megakernel_entry_round(),
                    )
                })
                .unwrap_or_else(|| {
                    (
                        window_dr::continuation_window_count(folding_steps),
                        window_dr::megakernel_entry_round(folding_steps),
                    )
                });
            let mut prepared = window_dr::prepare_dr_window_r0(
                program.program(),
                program.input_projection(),
                &self.storage,
                folding_steps,
                continuation_window_count,
                megakernel_entry_round,
                eq,
                required_future_partials_len,
                round_scratch.partials.as_mut_ptr(),
            )
            .expect(
                "preflighted DR window preparation contract (geometry, Eq contract, mask, \
                 storage, and raw keepalive) must bind to runtime storage",
            );
            prepared
                .configure_continuation_readiness(options, strategy, true)
                .expect(
                    "preflighted DR continuation prerequisites must remain valid during \
                     absolute-layer preparation",
                );
            assert_eq!(
                prepared.r0_launch.binding.batch.eq_low,
                round_scratch.eq_low_group.as_ptr(),
                "Task 6 prepared batch must point at the transferred common Eq owner",
            );
            Some(prepared)
        } else {
            None
        };

        self.next_trace_len_after_reduction *= 2;

        Ok(GpuGKRDimensionReducingSumcheckLayerPlan {
            layer_idx,
            trace_len_after_reduction,
            folding_steps,
            layer_slots,
            folding_addresses,
            round0_batch_template_compact,
            dr_window,
            dr_window_bundle_final_log,
            dr_execution_plan,
            round_scratch,
            eq_sizes: GkrEqSizes::zeroed(),
        })
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        dr_window_programs: Option<&crate::DrWindowProgramBundle>,
        dr_tail_plan_cursor: Option<&mut DrTailPlanCursor<'_>>,
        options: crate::GkrBackwardOptions,
        strategy: crate::BackwardExecutionStrategy,
        context: &ProverContext,
    ) -> Result<Option<GpuGKRDimensionReducingSumcheckLayerPlan>, DrTailScheduleError> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };
        let layer_slots = build_dimension_reducing_slots_static(&layer);
        let (dr_window_program, dr_window_bundle_final_log) = dr_window_programs
            .map(|bundle| {
                let program = bundle.layer(layer_idx).unwrap_or_else(|| {
                    panic!("preflighted DR window bundle is missing absolute layer {layer_idx}")
                });
                (Some(program), Some(bundle.final_trace_log()))
            })
            .unwrap_or((None, None));
        Ok(Some(self.prepare_layer_from_slots(
            layer_idx,
            layer_slots,
            dr_window_program,
            dr_window_bundle_final_log,
            dr_tail_plan_cursor,
            options,
            strategy,
            context,
        )?))
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod cpu_dr_window_composition_preparation_tests {
    use super::*;
    use core::mem::size_of;
    use gpu_gkr_compiler::{
        lower_dr_window_program, project_dr_window_inputs, DrWindowInputOutput,
    };
    use gpu_prover_context::ProverContextConfig;

    const CANONICAL_FIXTURE_INITIAL_TRACE_LOG: usize = 23;
    const CANONICAL_FIXTURE_FINAL_TRACE_LOG: usize = 4;
    const SMALL_ALLOCATION_CHUNK_BYTES: usize = 1 << 8;
    const SMALL_ALLOCATION_THRESHOLD_BYTES: usize = 1 << 18;
    const OUTER_ALLOCATION_BLOCK_BYTES: usize = 1 << 20;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Task6AllocationOwnershipViolation {
        EqOwnerCount {
            folding_steps: usize,
            baseline: usize,
            candidate: usize,
            corrected_logical_delta_bytes: usize,
        },
        PartialsCapacity {
            folding_steps: usize,
            expected_len: usize,
            candidate_len: usize,
            corrected_logical_delta_bytes: usize,
        },
    }

    fn corrected_logical_allocation_bytes(len: usize) -> usize {
        let requested_bytes = len
            .checked_mul(size_of::<E4>())
            .expect("canonical fixture allocation byte length must fit usize");
        let chunk_bytes = if requested_bytes <= SMALL_ALLOCATION_THRESHOLD_BYTES {
            SMALL_ALLOCATION_CHUNK_BYTES
        } else {
            OUTER_ALLOCATION_BLOCK_BYTES
        };
        requested_bytes.next_multiple_of(chunk_bytes)
    }

    fn assert_canonical_allocator_rounding_contract() {
        let config = ProverContextConfig::default();
        assert_eq!(
            1usize << config.allocator_block_log_size,
            OUTER_ALLOCATION_BLOCK_BYTES,
        );
        assert_eq!(
            config.small_allocator_log_chunk_size,
            Some(SMALL_ALLOCATION_CHUNK_BYTES.trailing_zeros()),
        );
        assert_eq!(
            1usize << (config.allocator_block_log_size - 2),
            SMALL_ALLOCATION_THRESHOLD_BYTES,
        );
    }

    fn task6_allocation_ownership_violation(
        folding_steps: usize,
        baseline: DrWindowPreparationAllocationPolicy,
        candidate: DrWindowPreparationAllocationPolicy,
    ) -> Option<Task6AllocationOwnershipViolation> {
        if candidate.r0_eq_owner_count != baseline.r0_eq_owner_count {
            let extra_owners = candidate
                .r0_eq_owner_count
                .checked_sub(baseline.r0_eq_owner_count)
                .expect("the mutation oracle only admits added Eq owners");
            return Some(Task6AllocationOwnershipViolation::EqOwnerCount {
                folding_steps,
                baseline: baseline.r0_eq_owner_count,
                candidate: candidate.r0_eq_owner_count,
                corrected_logical_delta_bytes: extra_owners
                    * corrected_logical_allocation_bytes(GKR_EQ_GROUP_TABLE_LEN),
            });
        }
        let expected_len = baseline.retained_partials_len.max(
            candidate
                .required_future_partials_len
                .unwrap_or(baseline.retained_partials_len),
        );
        let expected_partials = corrected_logical_allocation_bytes(expected_len);
        let candidate_partials =
            corrected_logical_allocation_bytes(candidate.retained_partials_len);
        if candidate.retained_partials_len != expected_len {
            return Some(Task6AllocationOwnershipViolation::PartialsCapacity {
                folding_steps,
                expected_len,
                candidate_len: candidate.retained_partials_len,
                corrected_logical_delta_bytes: expected_partials.abs_diff(candidate_partials),
            });
        }
        None
    }

    fn canonical_fixture_policy(
        folding_steps: usize,
        prepares_dr_window: bool,
    ) -> DrWindowPreparationAllocationPolicy {
        let max_acc_size = 1usize << (folding_steps - 1);
        dr_window_preparation_allocation_policy(max_acc_size, folding_steps, prepares_dr_window)
    }

    #[test]
    fn cpu_dr_window_composition_uses_one_common_eq_owner_at_every_canonical_fold() {
        assert_eq!(GKR_EQ_GROUP_TABLE_LEN, 256);
        assert_eq!(size_of::<E4>(), 16);
        let composition = include_str!("window_dr/composition.rs");
        let activate_start = composition
            .find("pub(crate) fn activate<B>(")
            .expect("the production activation seam must remain explicit");
        let activate_end = composition[activate_start..]
            .find("pub(crate) fn configure_continuation_readiness")
            .map(|offset| activate_start + offset)
            .expect("readiness configuration must follow activation");
        let activate = &composition[activate_start..activate_end];
        assert!(activate.contains("self.r0_eq"));
        assert!(
            !activate.contains("DrWindowPassEqState::allocate"),
            "activation must consume the prepared common Eq owner, not allocate a duplicate",
        );
        let mut fold_count = 0;
        for folding_steps in CANONICAL_FIXTURE_FINAL_TRACE_LOG..CANONICAL_FIXTURE_INITIAL_TRACE_LOG
        {
            let baseline = canonical_fixture_policy(folding_steps, false);
            let prepared = canonical_fixture_policy(folding_steps, true);
            assert_eq!(baseline.r0_eq_owner_count, 1);
            assert_eq!(
                prepared.r0_eq_owner_count, 1,
                "Task 6 prepared fold f={folding_steps} must borrow the one common Eq owner"
            );
            assert_eq!(
                task6_allocation_ownership_violation(folding_steps, baseline, prepared),
                None,
            );
            fold_count += 1;
        }
        assert_eq!(fold_count, 19);
    }

    #[test]
    fn cpu_dr_window_composition_retains_complete_chain_partials_at_every_canonical_fold() {
        let mut fold_count = 0;
        for folding_steps in CANONICAL_FIXTURE_FINAL_TRACE_LOG..CANONICAL_FIXTURE_INITIAL_TRACE_LOG
        {
            let baseline = canonical_fixture_policy(folding_steps, false);
            let prepared = canonical_fixture_policy(folding_steps, true);
            let required = window_dr::dr_window_partials_len(folding_steps);
            assert_eq!(
                prepared.retained_partials_len,
                baseline.retained_partials_len.max(required),
                "Task 6 fold f={folding_steps} must retain enough scratch for legacy diagnostics and the production R0/continuation chain",
            );
            assert_eq!(prepared.required_future_partials_len, Some(required),);
            assert_eq!(
                task6_allocation_ownership_violation(folding_steps, baseline, prepared),
                None,
            );
            fold_count += 1;
        }
        assert_eq!(fold_count, 19);
    }

    #[test]
    fn cpu_dr_window_composition_rejects_duplicate_eq_owner_with_exact_4096_bytes() {
        for folding_steps in CANONICAL_FIXTURE_FINAL_TRACE_LOG..CANONICAL_FIXTURE_INITIAL_TRACE_LOG
        {
            let baseline = canonical_fixture_policy(folding_steps, false);
            let mut mutated = canonical_fixture_policy(folding_steps, true);
            mutated.r0_eq_owner_count += 1;
            assert_eq!(
                task6_allocation_ownership_violation(folding_steps, baseline, mutated),
                Some(Task6AllocationOwnershipViolation::EqOwnerCount {
                    folding_steps,
                    baseline: 1,
                    candidate: 2,
                    corrected_logical_delta_bytes: 4_096,
                }),
            );
        }
    }

    #[test]
    fn cpu_dr_window_composition_rejects_legacy_only_partials_with_exact_fold_deltas() {
        assert_canonical_allocator_rounding_contract();
        let mut observed_deltas = BTreeMap::new();
        for folding_steps in CANONICAL_FIXTURE_FINAL_TRACE_LOG..CANONICAL_FIXTURE_INITIAL_TRACE_LOG
        {
            let baseline = canonical_fixture_policy(folding_steps, false);
            let mut mutated = canonical_fixture_policy(folding_steps, true);
            let expected_len = mutated.retained_partials_len;
            mutated.retained_partials_len = baseline.retained_partials_len;
            let expected_delta = corrected_logical_allocation_bytes(expected_len)
                - corrected_logical_allocation_bytes(baseline.retained_partials_len);
            assert_eq!(
                task6_allocation_ownership_violation(folding_steps, baseline, mutated),
                Some(Task6AllocationOwnershipViolation::PartialsCapacity {
                    folding_steps,
                    expected_len,
                    candidate_len: mutated.retained_partials_len,
                    corrected_logical_delta_bytes: expected_delta,
                }),
            );
            observed_deltas.insert(folding_steps, expected_delta);
        }
        assert_eq!(observed_deltas.len(), 19);
        assert_eq!(observed_deltas[&4], 768);
        assert_eq!(observed_deltas[&8], 768);
        assert_eq!(observed_deltas[&9], 1_280);
        assert_eq!(observed_deltas[&18], 917_504);
        assert_eq!(observed_deltas[&19], 786_432);
        assert_eq!(observed_deltas[&22], 5_242_880);
    }

    #[test]
    fn cpu_dr_window_admitted_plan_cannot_own_or_access_legacy_accumulator() {
        assert_canonical_allocator_rounding_contract();
        for folding_steps in CANONICAL_FIXTURE_FINAL_TRACE_LOG..CANONICAL_FIXTURE_INITIAL_TRACE_LOG
        {
            let max_acc_size = 1usize << (folding_steps - 1);
            assert_eq!(
                dr_legacy_accumulator_len(max_acc_size, true),
                None,
                "admitted fold f={folding_steps} must not construct legacy-only storage",
            );
            assert_eq!(
                dr_legacy_accumulator_len(max_acc_size, false),
                Some(max_acc_size * 2),
                "diagnostic fold f={folding_steps} must retain its explicit legacy owner",
            );

            // Mutation control: admitting the chain under the legacy arm
            // recreates at least one allocator chunk and must remain distinct.
            assert!(
                corrected_logical_allocation_bytes(max_acc_size * 2) > 0,
                "legacy accumulator mutation must be observable at f={folding_steps}",
            );
        }

        let production = GpuGKRDimensionReducingAccumulator::production_chain();
        assert!(production.is_production_chain());
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            production.legacy_diagnostic_ref()
        }));
        assert!(
            rejected.is_err(),
            "an admitted production owner must fail closed before exposing a legacy pointer",
        );
    }

    fn address(offset: usize) -> GKRAddress {
        GKRAddress::InnerLayer { layer: 7, offset }
    }

    #[test]
    fn cpu_dr_window_composition_preparation_is_absolute_and_pass_local() {
        const ABSOLUTE_LAYER: usize = 17;
        const FOLDING_STEPS: usize = 11;
        const R0_COORDINATES: usize = 3;

        let input_a = address(0);
        let input_b = address(1);
        let output_a = address(2);
        let output_b = address(3);
        let lowered = lower_dr_window_program(&BTreeMap::from([(
            OutputType::PermutationProduct,
            DrWindowInputOutput::new([input_a, input_b], [output_a, output_b]),
        )]))
        .unwrap();
        let projection = project_dr_window_inputs(&lowered, &BTreeMap::new());
        let layer =
            crate::DrWindowLayerProgram::new(ABSOLUTE_LAYER, FOLDING_STEPS, lowered, projection);
        let bundle =
            crate::DrWindowProgramBundle::new(4, BTreeMap::from([(ABSOLUTE_LAYER, layer)]));
        let prepared = bundle.layer(ABSOLUTE_LAYER).unwrap();

        validate_dr_window_layer_program(prepared, ABSOLUTE_LAYER, FOLDING_STEPS);
        assert!(bundle.layer(ABSOLUTE_LAYER - 1).is_none());
        assert_eq!(
            prepared.input_projection().canonical_sources(),
            &[input_a, input_b],
            "raw keepalive projection must contain inputs only"
        );
        assert!(!prepared
            .input_projection()
            .canonical_sources()
            .contains(&output_a));
        assert!(!prepared
            .input_projection()
            .canonical_sources()
            .contains(&output_b));
        assert_eq!(window_dr::continuation_window_count(FOLDING_STEPS), 2);
        assert_eq!(window_dr::megakernel_entry_round(FOLDING_STEPS), 9);
        let eq_geometry = dr_window_pass_eq_geometry(FOLDING_STEPS);
        assert_eq!(eq_geometry.build_offset, R0_COORDINATES);
        assert_eq!(eq_geometry.challenge_count, FOLDING_STEPS - R0_COORDINATES);
        assert_eq!(
            eq_geometry.eq_sizes,
            make_eq_sizes(FOLDING_STEPS - R0_COORDINATES)
        );
        assert!(window_dr::dr_window_partials_len(FOLDING_STEPS) >= 27);

        assert!(std::panic::catch_unwind(|| {
            validate_dr_window_layer_program(prepared, ABSOLUTE_LAYER + 1, FOLDING_STEPS)
        })
        .is_err());
        assert!(std::panic::catch_unwind(|| {
            validate_dr_window_layer_program(prepared, ABSOLUTE_LAYER, FOLDING_STEPS + 1)
        })
        .is_err());
    }
}
