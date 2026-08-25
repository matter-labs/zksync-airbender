use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;

use super::kernels::*;
use crate::proof_layout::ProofLayout;
use crate::upstream::GKRAddress;
use crate::MainLayerScheduleError;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::context::UnsafeMutAccessor;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

use super::stage_snapshots::{schedule_stage_snapshot, GKRBackwardStageSnapshotSink};

impl GpuGKRBackwardScheduledExecution {
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
        strategy: crate::BackwardExecutionStrategy,
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
    ) -> Result<GpuGKRBackwardScheduledExecution, MainLayerScheduleError> {
        let stream = context.get_exec_stream();
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
        #[cfg(all(
            any(test, feature = "task8_continuation_differential_test"),
            not(no_cuda)
        ))]
        let mut task8_requests = stage_snapshots.map(|sink| {
            // SAFETY: no snapshot callback using this accessor has been
            // scheduled yet. The helper consumes only the sink-owned request.
            unsafe { super::stage_snapshots::take_task8_sink_requests(sink) }
        });
        #[cfg(all(
            any(test, feature = "task8_continuation_differential_test"),
            not(no_cuda)
        ))]
        let stage_snapshots = stage_snapshots.filter(|_| {
            task8_requests
                .as_ref()
                .is_none_or(|requests| requests.capture_snapshots)
        });
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
        while let Some(mut prepared_layer) = self.prepare_next_layer_static(context)? {
            let layer_idx = prepared_layer.layer_idx;
            let mut execution = prepared_layer.schedule_execute_dimension_reducing_layer(
                shared_device_seed,
                shared_device_claim_point,
                shared_device_claims,
                &shared_claim_layout,
                proof_slab,
                proof_layout,
                backward_layer_slot,
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
        dimension_reducing_layers_range.end(stream)?;
        tracing_ranges.push(dimension_reducing_layers_range);

        let mut main_backward_state = self.into_main_layer_backward_state_static(
            inits_and_teardowns_top_bits,
            programs,
            options,
            strategy,
        );
        #[cfg(all(
            any(test, feature = "task8_continuation_differential_test"),
            not(no_cuda)
        ))]
        if let Some(request) = task8_requests
            .as_mut()
            .and_then(|requests| requests.differential.take())
        {
            super::main_continuation::schedule_prepared_main_continuation_differential(
                request,
                &main_backward_state.storage,
                &main_backward_state.programs,
                &main_backward_state.inits_and_teardowns_top_bits,
                callbacks,
                context,
            )?;
        }
        let mut main_layers = Vec::new();
        let main_layers_range = Range::new("gkr.backward.main_layers")?;
        main_layers_range.start(stream)?;
        while let Some(mut prepared_layer) =
            main_backward_state.prepare_next_layer_static(options, context)?
        {
            let layer_idx = prepared_layer.layer_idx;
            #[cfg(all(
                any(test, feature = "task8_continuation_differential_test"),
                not(no_cuda)
            ))]
            let task8_expected_window_launches =
                usize::from(prepared_layer.main_execution_plan.window_count());
            #[cfg(all(
                any(test, feature = "task8_continuation_differential_test"),
                not(no_cuda)
            ))]
            let task8_launch_counter = task8_requests
                .as_ref()
                .filter(|requests| requests.tracks_execution_counts())
                .map(|_| {
                    super::main_continuation::Task8MainContinuationLaunchCounterGuard::install()
                });
            let execution_result = prepared_layer.schedule_execute_main_layer(
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
            );
            let mut execution = execution_result?;
            #[cfg(all(
                any(test, feature = "task8_continuation_differential_test"),
                not(no_cuda)
            ))]
            if let Some(requests) = task8_requests.as_ref() {
                let boundary_window_launches = prepared_layer
                    .main_continuation
                    .final_eq_boundary()
                    .map_or(0, |boundary| {
                        assert_eq!(
                            boundary.consumer_round % 3,
                            0,
                            "Task 8 continuation boundary must be width-three aligned"
                        );
                        usize::from(boundary.consumer_round)
                            .checked_div(3)
                            .and_then(|groups| groups.checked_sub(1))
                            .expect("Task 8 continuation boundary must encode complete width-three passes")
                    });
                assert_eq!(
                    boundary_window_launches, task8_expected_window_launches,
                    "Task 8 continuation boundary differs from the prepared plan"
                );
                let window_launches = task8_launch_counter
                    .map(|counter| counter.finish())
                    .unwrap_or(0);
                if requests.tracks_execution_counts() {
                    assert_eq!(
                        window_launches, task8_expected_window_launches,
                        "Task 8 actual continuation enqueue count differs from the prepared plan"
                    );
                }
                let legacy_rounds = prepared_layer.bwd_vm_ext.task8_scheduled_rounds();
                requests.record_main_layer(
                    window_launches,
                    usize::from(window_launches > 0) * legacy_rounds,
                    usize::from(window_launches == 0) * legacy_rounds,
                );
            }
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

        #[cfg(all(
            any(test, feature = "task8_continuation_differential_test"),
            not(no_cuda)
        ))]
        if let Some(requests) = task8_requests.as_ref() {
            requests.finalize_execution_counts();
        }

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
