use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;

use super::dr_tail::resources::{DrTailLayerIdentity, DrTailPlanCursor, DrTailScheduleError};
use super::kernels::*;
use crate::proof_layout::ProofLayout;
use crate::upstream::GKRAddress;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::context::UnsafeMutAccessor;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

use super::stage_snapshots::{schedule_stage_snapshot, GKRBackwardStageSnapshotSink};

impl GpuGKRBackwardScheduledExecution {
    /// Number of dimension-reducing layers actually scheduled.
    #[doc(hidden)]
    pub fn dimension_reducing_layer_count(&self) -> usize {
        self.dimension_reducing_layers.len()
    }

    /// Number of scheduled layers that entered with a real DR composition hook.
    #[doc(hidden)]
    pub fn dr_prepared_layer_count(&self) -> usize {
        self.dimension_reducing_layers
            .iter()
            .filter(|layer| layer.dr_window_prepared)
            .count()
    }

    /// Canonical final-log identity carried by the actual prepared hooks.
    #[doc(hidden)]
    pub fn dr_prepared_bundle_final_log(&self) -> Option<u32> {
        let mut logs = self
            .dimension_reducing_layers
            .iter()
            .filter(|layer| layer.dr_window_prepared)
            .map(|layer| {
                layer
                    .dr_window_bundle_final_log
                    .expect("a prepared DR hook must carry its bundle final-log identity")
            });
        let first = logs.next()?;
        assert!(
            logs.all(|log| log == first),
            "all prepared DR hooks must come from one canonical final-log bundle"
        );
        Some(first)
    }

    /// Exact dimension-reducing work scheduled by this proof, in execution
    /// order. The expected segment list is derived from the same admitted
    /// entry round (complete arm) or folding count (legacy diagnostic arm)
    /// that selected the real scheduler path.
    #[doc(hidden)]
    pub fn exact_memory_work_json(&self) -> serde_json::Value {
        serde_json::Value::Array(
            self.dimension_reducing_layers
                .iter()
                .enumerate()
                .map(|(coordinate, layer)| {
                    let executor = if layer.dr_tail_entry_round.is_some() {
                        "mega_dr"
                    } else {
                        "per_round"
                    };
                    serde_json::json!({
                        "coordinate": coordinate,
                        "kind": "dim_reducing",
                        "layer_idx": layer.layer_idx,
                        "folding_steps": layer.folding_steps,
                        "canonical_source_count": layer.canonical_source_count,
                        "executor": executor,
                        "entry_round": layer.dr_tail_entry_round,
                        "segments": super::round_timing::expected_dim_reducing_segments(
                            layer.folding_steps,
                            layer.dr_tail_entry_round,
                        ),
                    })
                })
                .collect(),
        )
    }

    pub fn final_device_seed_and_claim_point_mut(
        &mut self,
    ) -> (
        &mut DeviceAllocation<u32>,
        &era_cudart::slice::DeviceSlice<E4>,
    ) {
        let device_seed = self
            .final_device_seed
            .as_mut()
            .expect("backward seed handoff buffer must be allocated before consumption");
        let buffer = self
            .final_device_claim_point_and_batching
            .as_ref()
            .expect("backward claim_point handoff buffer must be allocated before consumption");
        let len = buffer.len();
        assert!(
            len >= 1,
            "final claim point handoff must include batching challenge"
        );
        (device_seed, buffer.slice(0, len - 1))
    }

    /// Schedule-time-known set of layer-1 incoming claim addresses (i.e. the
    /// addresses whose claim values land in the final main-layer's device
    /// claim buffer). Exposed so that base-layer claim scheduling can build
    /// its extras plan from a schedule-time slice without ever waiting for a
    /// runtime D2H + host BTreeMap materialization.
    pub fn final_claim_addresses(&self) -> &[GKRAddress] {
        &self
            .final_claim_layout
            .as_ref()
            .expect("backward layer-0 claim layout must be set before consumption")
            .addresses
    }

    /// Release device buffers after all consumers have been enqueued.
    pub fn release_device_buffers(&mut self) {
        // Final backward handoff buffers — WHIR fold setup has already drawn the
        // base batching challenge from the rolling seed on-device by this point.
        self.final_device_seed = None;
        self.final_device_claim_point_and_batching = None;
        // Per-layer next-layer handoff buffers — already `.take()`-en into the
        // following layer by the orchestrator; null any residual explicitly.
        for layer in &mut self.dimension_reducing_layers {
            layer.device_seed = None;
            layer.device_claim_point_for_next_layer = None;
            layer.device_claims_for_next_layer = None;
        }
        for layer in &mut self.main_layers {
            layer.device_seed = None;
            layer.device_claim_point_for_next_layer = None;
            layer.device_claims_for_next_layer = None;
        }
    }
}

impl GpuGKRDimensionReducingBackwardState {
    pub fn schedule_execute_backward_workflow(
        mut self,
        // ACTUAL per-circuit i&t top bits: canonical for real i&t data, all
        // zeros for trivial (dummy) unified chunks (CPU-reference parity).
        inits_and_teardowns_top_bits: Vec<u32>,
        programs: std::sync::Arc<crate::GkrPrograms>,
        // Resolved once per proof by `crate::backward_execution_strategy`; the
        // options carry the tail arm the windowed path launches.
        options: crate::GkrBackwardOptions,
        dr_tail_plan: Option<crate::DrTailProofPlan>,
        strategy: crate::BackwardExecutionStrategy,
        final_trace_size_log_2: u32,
        device_external_challenges_ptr: *const E4,
        initial_d_seed: DeviceAllocation<u32>,
        initial_d_claim_point_and_batching: DeviceAllocation<E4>,
        initial_d_claims: DeviceAllocation<E4>,
        initial_claim_layout: ClaimBufferLayout,
        device_lookup_challenges: DeviceAllocation<E4>,
        // The proof slab and its layout thread through from prove().
        // Per-layer schedulers D2D-copy slab-bound fields
        // (`internal_round_coefficients`, `final_step_evaluations`) into slab
        // offsets via `ProofLayout` accessors. `extra_evaluations_from_caching_relations`
        // uses dedicated per-layer main-layer ranges. Only the base-layer
        // fallback is represented as sparse references into slab-resident WHIR
        // base eval ranges and merged at parse time.
        proof_slab: &DeviceAllocation<E4>,
        proof_layout: &ProofLayout,
        stage_snapshots: Option<UnsafeMutAccessor<GKRBackwardStageSnapshotSink>>,
        callbacks: &mut Callbacks<'_>,
        context: &ProverContext,
    ) -> Result<GpuGKRBackwardScheduledExecution, DrTailScheduleError> {
        let stream = context.get_exec_stream();
        // Defence in depth only. The load-bearing rejection is the typed
        // resource preflight that runs before any transfer is constructed;
        // reaching scheduling without an admitted plan is a caller bug.
        // `windowed_dr` is not an execution selector, so this keys on the
        // DR-tail selector itself.
        if options.dr_tail_megakernel {
            assert!(
                dr_tail_plan.is_some(),
                "DR-tail scheduling requires the resource plan admitted before transfers"
            );
        } else {
            assert!(
                dr_tail_plan.is_none(),
                "a DR-tail resource plan may only accompany the explicit production selector",
            );
        }
        let mut dr_tail_plan_cursor = if let Some(plan) = dr_tail_plan.as_ref() {
            plan.validate_before_enqueue(
                programs.runtime_circuit().as_ref(),
                final_trace_size_log_2 as usize,
            )?;
            Some(DrTailPlanCursor::new(plan.layers()))
        } else {
            None
        };
        let device_lookup_challenges_ptr = device_lookup_challenges.as_ptr();
        let mut tracing_ranges = Vec::new();
        let workflow_range = Range::new("gkr.backward.schedule")?;
        workflow_range.start(stream)?;
        let mut dimension_reducing_layers = Vec::new();
        let dimension_reducing_layers_range = Range::new("gkr.backward.dimension_reducing_layers")?;
        dimension_reducing_layers_range.start(stream)?;
        let mut shared_device_seed = initial_d_seed;
        let mut shared_device_claim_point =
            DeviceClaimPointAndBatching::from_allocation(initial_d_claim_point_and_batching);
        let mut shared_device_claims = initial_d_claims;
        let mut shared_claim_layout = initial_claim_layout;
        // Preflight has already seated this exact final-log result. Clone its
        // canonical Arc once before the DR loop; layer preparation must never
        // resolve or lower independently.
        let dr_window_programs = if options.windowed_dr {
            assert!(
                programs.dr_window_programs_ready(final_trace_size_log_2),
                "DR window preparation requires an accepted preflight result"
            );
            Some(
                programs
                    .resolve_dr_window_programs(final_trace_size_log_2)
                    .expect("preflighted DR window bundle must remain accepted"),
            )
        } else {
            None
        };
        if let Some(output) = stage_snapshots {
            let initial_layer_idx = self
                .pending_layers
                .front()
                .map_or(programs.runtime_circuit().layers.len(), |(layer_idx, _)| {
                    layer_idx + 1
                });
            schedule_stage_snapshot(
                initial_layer_idx,
                &shared_device_claim_point,
                &shared_device_claims,
                &shared_claim_layout,
                output,
                callbacks,
                context,
            )?;
        }
        let mut backward_layer_slot: usize = 0;
        while let Some(mut prepared_layer) = self.prepare_next_layer_static(
            dr_window_programs.as_deref(),
            options,
            strategy,
            context,
        )? {
            let layer_idx = prepared_layer.layer_idx;
            let mut execution = prepared_layer.schedule_execute_dimension_reducing_layer(
                shared_device_seed,
                shared_device_claim_point,
                shared_device_claims,
                &shared_claim_layout,
                proof_slab,
                proof_layout,
                backward_layer_slot,
                dr_tail_plan_cursor
                    .as_mut()
                    .map(|cursor| {
                        cursor.bind(DrTailLayerIdentity::new(
                            prepared_layer.layer_idx,
                            prepared_layer.folding_steps,
                            &prepared_layer.folding_addresses,
                        ))
                    })
                    .transpose()?,
                options.window_tail,
                &mut self.storage,
                context,
            )?;
            if let Some(output) = stage_snapshots {
                schedule_stage_snapshot(
                    layer_idx,
                    execution
                        .device_claim_point_for_next_layer
                        .as_ref()
                        .expect("dimension-reducing layer must return its claim point"),
                    execution
                        .device_claims_for_next_layer
                        .as_ref()
                        .expect("dimension-reducing layer must return its claims"),
                    execution
                        .claim_layout_for_next_layer
                        .as_ref()
                        .expect("dimension-reducing layer must return its claim layout"),
                    output,
                    callbacks,
                    context,
                )?;
            }
            shared_device_seed = execution
                .device_seed
                .take()
                .expect("dim-reducing scheduler must return the device seed");
            shared_device_claim_point = execution
                .device_claim_point_for_next_layer
                .take()
                .expect("dim-reducing scheduler must return the device claim_point");
            shared_device_claims = execution
                .device_claims_for_next_layer
                .take()
                .expect("dim-reducing scheduler must return the device claims");
            shared_claim_layout = execution
                .claim_layout_for_next_layer
                .take()
                .expect("dim-reducing scheduler must return the claim layout");
            dimension_reducing_layers.push(execution);
            backward_layer_slot += 1;
        }
        if let Some(cursor) = dr_tail_plan_cursor {
            cursor.finish()?;
        }
        dimension_reducing_layers_range.end(stream)?;
        tracing_ranges.push(dimension_reducing_layers_range);

        let mut main_backward_state = self.into_main_layer_backward_state_static(
            inits_and_teardowns_top_bits,
            programs,
            options,
            strategy,
        );
        let mut main_layers = Vec::new();
        let main_layers_range = Range::new("gkr.backward.main_layers")?;
        main_layers_range.start(stream)?;
        while let Some(mut prepared_layer) =
            main_backward_state.prepare_next_layer_static(options, context)?
        {
            let layer_idx = prepared_layer.layer_idx;
            let mut execution = prepared_layer.schedule_execute_main_layer(
                shared_device_seed,
                shared_device_claim_point,
                shared_device_claims,
                &shared_claim_layout,
                device_lookup_challenges_ptr,
                device_external_challenges_ptr,
                proof_slab,
                proof_layout,
                backward_layer_slot,
                &mut main_backward_state.storage,
                context,
            )?;
            if let Some(output) = stage_snapshots {
                schedule_stage_snapshot(
                    layer_idx,
                    execution
                        .device_claim_point_for_next_layer
                        .as_ref()
                        .expect("main layer must return its claim point"),
                    execution
                        .device_claims_for_next_layer
                        .as_ref()
                        .expect("main layer must return its claims"),
                    execution
                        .claim_layout_for_next_layer
                        .as_ref()
                        .expect("main layer must return its claim layout"),
                    output,
                    callbacks,
                    context,
                )?;
            }
            shared_device_seed = execution
                .device_seed
                .take()
                .expect("main-layer scheduler must return the device seed");
            shared_device_claim_point = execution
                .device_claim_point_for_next_layer
                .take()
                .expect("main-layer scheduler must return the device claim_point");
            shared_device_claims = execution
                .device_claims_for_next_layer
                .take()
                .expect("main-layer scheduler must return the device claims");
            shared_claim_layout = execution
                .claim_layout_for_next_layer
                .take()
                .expect("main-layer scheduler must return the claim layout");
            main_layers.push(execution);
            backward_layer_slot += 1;
        }
        main_layers_range.end(stream)?;
        tracing_ranges.push(main_layers_range);

        drop(main_backward_state);
        // All main-layer work has been scheduled before its storage drops.
        drop(device_lookup_challenges);
        workflow_range.end(stream)?;
        tracing_ranges.push(workflow_range);

        // Stream-ordered drop: the final main-layer kernel wrote into
        // `shared_device_claims` on `exec_stream`; nothing else reads it now
        // that base-layer claim scheduling sources layer-1 incoming addresses
        // from `final_claim_layout` and layer-0 values from the slab. The
        // pool defers the underlying free until exec_stream has progressed
        // past the writing kernel, so dropping here is safe.
        drop(shared_device_claims);

        Ok(GpuGKRBackwardScheduledExecution {
            tracing_ranges,
            dimension_reducing_layers,
            main_layers,
            final_device_seed: Some(shared_device_seed),
            final_device_claim_point_and_batching: Some(shared_device_claim_point),
            final_claim_layout: Some(shared_claim_layout),
        })
    }
}
