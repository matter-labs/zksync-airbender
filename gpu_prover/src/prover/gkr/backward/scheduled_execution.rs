#[cfg(test)]
use std::collections::BTreeMap;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;
use field::{Field, FieldExtension};
use prover::gkr::prover::GKRExternalChallenges;
use prover::transcript::Seed;

use super::super::backward_kernels::*;
#[cfg(test)]
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::STATE_SIZE;
use crate::ops::cub::device_reduce::Reduce;
use crate::ops::simple::{BinaryOp, Mul};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::proof::layout::ProofLayout;

impl<B, E: FieldExtension<BF> + Field> GpuGKRDimensionReducingScheduledLayerExecution<B, E> {
    pub(crate) fn into_host_keepalive(self) -> GpuGKRDimensionReducingHostKeepalive<B, E> {
        let Self {
            tracing_ranges,
            start_callbacks,
            reduction_states,
            final_readback,
            shared_state,
            device_seed: _,
            device_claim_point_for_next_layer: _,
            device_claims_for_next_layer: _,
            claim_layout_for_next_layer: _,
            _phantom: _,
        } = self;
        GpuGKRDimensionReducingHostKeepalive {
            tracing_ranges,
            start_callbacks,
            reduction_states,
            final_readback,
            shared_state,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<E: FieldExtension<BF> + Field> GpuGKRMainLayerScheduledLayerExecution<E> {
    pub(crate) fn into_host_keepalive(self) -> GpuGKRMainLayerHostKeepalive<E> {
        let Self {
            tracing_ranges,
            start_callbacks,
            batch_challenge_storage,
            batch_challenge_buffer: _,
            reduction_states,
            final_readback,
            flat_coeff_callbacks,
            recipe_upload_callbacks,
            shared_state,
            device_seed: _,
            device_claim_point_for_next_layer: _,
            device_claims_for_next_layer: _,
            claim_layout_for_next_layer: _,
        } = self;
        GpuGKRMainLayerHostKeepalive {
            tracing_ranges,
            start_callbacks,
            batch_challenge_storage: challenge_storage_into_host_keepalive(batch_challenge_storage),
            reduction_states,
            final_readback,
            flat_coeff_callbacks,
            recipe_upload_callbacks,
            shared_state,
        }
    }
}

impl<B, E> GpuGKRBackwardScheduledExecution<B, E>
where
    E: FieldExtension<BF> + Field,
{
    pub(crate) fn into_host_keepalive(self) -> GpuGKRBackwardHostKeepalive<B, E> {
        let Self {
            tracing_ranges,
            dimension_reducing_layers,
            main_layers,
            shared_state,
            initial_callbacks,
            external_challenges_device_keepalive,
            final_device_seed,
            final_device_claim_point_and_batching,
            final_claim_layout,
            final_seed_host,
            final_claim_point_and_batching_host,
        } = self;
        GpuGKRBackwardHostKeepalive {
            tracing_ranges,
            dimension_reducing_layers: dimension_reducing_layers
                .into_iter()
                .map(GpuGKRDimensionReducingScheduledLayerExecution::into_host_keepalive)
                .collect(),
            main_layers: main_layers
                .into_iter()
                .map(GpuGKRMainLayerScheduledLayerExecution::into_host_keepalive)
                .collect(),
            shared_state,
            initial_callbacks,
            external_challenges_device_keepalive,
            final_device_seed,
            final_device_claim_point_and_batching,
            final_claim_layout,
            final_seed_host,
            final_claim_point_and_batching_host,
        }
    }

    pub(crate) fn shared_state_handle(&mut self) -> ScheduledBackwardWorkflowStateHandle<E> {
        crate::primitives::context::UnsafeMutAccessor::new(self.shared_state.as_mut())
    }

    /// Device-resident layer-0 claim point. The final-device buffer packs
    /// `[claim_point || batching_challenge]`, so we slice off the trailing batching
    /// element. Stream-ordered against `exec_stream`; consumers must respect that
    /// `self` (the keepalive) remains live until any kernel reading the slice has
    /// been scheduled.
    pub(crate) fn final_device_claim_point(&self) -> &era_cudart::slice::DeviceSlice<E> {
        let buffer = self
            .final_device_claim_point_and_batching
            .as_ref()
            .expect("backward claim_point handoff buffer must be allocated before consumption");
        let len = buffer.len();
        assert!(
            len >= 1,
            "final claim point handoff must include batching challenge"
        );
        unsafe { buffer.slice(0, len - 1) }
    }

    pub(crate) fn final_device_seed_and_claim_point_mut(
        &mut self,
    ) -> (
        &mut DeviceAllocation<u32>,
        &era_cudart::slice::DeviceSlice<E>,
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
        (device_seed, unsafe { buffer.slice(0, len - 1) })
    }

    /// Schedule-time-known set of layer-1 incoming claim addresses (i.e. the
    /// addresses whose claim values land in the final main-layer's device
    /// claim buffer). Exposed so that base-layer claim scheduling can build
    /// its extras plan from a schedule-time slice without ever waiting for a
    /// runtime D2H + host BTreeMap materialization.
    pub(crate) fn final_claim_addresses(&self) -> &[GKRAddress] {
        &self
            .final_claim_layout
            .as_ref()
            .expect("backward layer-0 claim layout must be set before consumption")
            .addresses
    }

    pub(crate) fn schedule_post_backward_handoff(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Callbacks<'static>>
    where
        E: 'static,
    {
        let stream = context.get_exec_stream();
        let device_seed = self
            .final_device_seed
            .as_ref()
            .expect("post-backward handoff requires final device seed");
        let device_claim_point_and_batching = self
            .final_device_claim_point_and_batching
            .as_ref()
            .expect("post-backward handoff requires final device claim point");
        assert!(
            device_claim_point_and_batching.len() >= 1,
            "final claim point handoff must include batching challenge"
        );

        let mut final_seed_host = unsafe { context.alloc_host_uninit_slice::<u32>(STATE_SIZE) };
        let final_seed_accessor = final_seed_host.get_accessor();
        let mut final_claim_point_and_batching_host =
            unsafe { context.alloc_host_uninit_slice::<E>(device_claim_point_and_batching.len()) };
        let final_claim_point_and_batching_accessor =
            final_claim_point_and_batching_host.get_accessor();

        memory_copy_async(&mut final_seed_host, device_seed, stream)?;
        memory_copy_async(
            &mut final_claim_point_and_batching_host,
            device_claim_point_and_batching.as_slice(),
            stream,
        )?;

        let shared_state = self.shared_state_handle();
        let mut callbacks = Callbacks::new();
        callbacks.schedule(
            move || unsafe {
                let seed = Seed(
                    <&[u32; STATE_SIZE]>::try_from(final_seed_accessor.get())
                        .expect("seed handoff has STATE_SIZE words")
                        .to_owned(),
                );
                let claim_point_and_batching = final_claim_point_and_batching_accessor.get();
                let (claim_point, batching_challenge) =
                    claim_point_and_batching.split_at(claim_point_and_batching.len() - 1);
                let current_claim_point = claim_point.to_vec();
                let current_batching_challenge = batching_challenge[0];

                let state = shared_state.get_mut();
                state.current_batching_challenge = current_batching_challenge;
                state.seed = seed;
                state
                    .points_for_claims_at_layer
                    .insert(0, current_claim_point);
            },
            stream,
        )?;

        // Park the pinned host buffers on `self` so they outlive the scheduled
        // callback. The callback's accessors are raw pointers into these
        // chunks; `backward_scheduled` stays alive (via the proof keepalive)
        // until the proof finishes, which is well after the callback fires.
        // Storing on `self` instead of dropping at function return prevents
        // pool reuse from a sibling prove writing into the same chunks before
        // this prove's callback executes.
        self.final_seed_host = Some(final_seed_host);
        self.final_claim_point_and_batching_host = Some(final_claim_point_and_batching_host);
        Ok(callbacks)
    }

    #[cfg(test)]
    pub(crate) fn wait(self, context: &ProverContext) -> CudaResult<GpuGKRBackwardExecution<E>> {
        context.get_exec_stream().synchronize()?;
        let Self {
            mut shared_state, ..
        } = self;
        let state = shared_state.as_mut();
        Ok(GpuGKRBackwardExecution {
            claims_for_layers: std::mem::take(&mut state.claims_for_layers),
            points_for_claims_at_layer: std::mem::take(&mut state.points_for_claims_at_layer),
            next_batching_challenge: state.current_batching_challenge,
            updated_seed: state.seed,
        })
    }
}

impl<E> GpuGKRDimensionReducingBackwardState<BF, E>
where
    E: Field
        + FieldExtension<BF>
        + Reduce
        + GpuDimensionReducingKernelSet
        + GpuBackwardSumcheckRoundUpdateKernel
        + super::super::backward_flat_compact::GpuFlatRound0CompactKernelSet
        + super::super::backward_flat_compact::GpuFlatRound0ConstantCompactKernelSet
        + super::super::backward_flat_compact::GpuFlatRound1UnifiedCompactKernelSet
        + super::super::backward_flat_compact::GpuFlatRound2UnifiedCompactKernelSet
        + super::super::backward_flat_compact::GpuFlatRound3UnifiedCompactKernelSet
        + 'static,
    Mul: BinaryOp<E, E, E>,
    [(); E::DEGREE]: Sized,
{
    pub(crate) fn schedule_execute_backward_workflow_from_shared_state(
        mut self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        device_external_challenges_ptr: *const E,
        mut shared_state: Box<ScheduledBackwardWorkflowState<E>>,
        initial_d_seed: DeviceAllocation<u32>,
        initial_d_claim_point_and_batching: DeviceAllocation<E>,
        initial_d_claims: DeviceAllocation<E>,
        initial_claim_layout: ClaimBufferLayout,
        device_lookup_and_constraint: DeviceAllocation<E>,
        mirror_layers_to_host: bool,
        // The proof slab and its layout thread through from prove().
        // Per-layer schedulers D2D-copy slab-bound fields
        // (`internal_round_coefficients`, `final_step_evaluations`) into slab
        // offsets via `ProofLayout` accessors. `extra_evaluations_from_caching_relations`
        // is represented as sparse references into the slab-resident WHIR base
        // eval ranges and merged at parse time.
        // `None` skips all slab routing (test paths).
        proof_slab: Option<&DeviceAllocation<E4>>,
        proof_layout: &ProofLayout,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRBackwardScheduledExecution<BF, E>> {
        let shared_state_handle =
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut());
        let stream = context.get_exec_stream();
        let workflow_initial_callbacks = Callbacks::new();
        // `[lookup_mul, lookup_add]` is threaded as a device-resident buffer into every
        // main-layer `schedule_flat_eval_recipes` call so those layers can D2D
        // the per-proof constants into their eval_recipes challenges buffer
        // instead of reading `workflow_state` inside a per-layer host callback.
        let device_lookup_and_constraint_ptr = device_lookup_and_constraint.as_ptr();
        let mut tracing_ranges = Vec::new();
        let workflow_range = Range::new("gkr.backward.schedule")?;
        workflow_range.start(stream)?;
        let mut dimension_reducing_layers = Vec::new();
        let dimension_reducing_layers_range = Range::new("gkr.backward.dimension_reducing_layers")?;
        dimension_reducing_layers_range.start(stream)?;
        // `shared_device_seed` lives across every backward layer. It enters the
        // pass from `initial_d_seed` (post-forward device squeeze in proof.rs),
        // is mutated in place by each layer's fused per-round kernel and
        // end-of-layer device transcript work, and flows to the next layer via
        // the layer's returned `Execution::device_seed`. No H2D, no per-layer
        // allocation — the whole backward seed pipeline is GPU-resident.
        let mut shared_device_seed = initial_d_seed;
        // `shared_device_claim_point` holds the next layer's input claim_point
        // followed by its batching_challenge, in the same `[claim_point ||
        // batching]` layout each layer consumes directly. The first layer
        // receives the post-forward device squeeze
        // buffer (`evaluation_point || batching_challenge`) unchanged; every
        // subsequent layer receives a symbol-backed view sized to its own
        // `[claim_point || batching]` layout and populated on device by the
        // previous layer's round-update and transcript kernels.
        let mut shared_device_claim_point =
            DeviceClaimPointAndBatching::from_allocation(initial_d_claim_point_and_batching);
        let mut shared_device_claims = initial_d_claims;
        let mut shared_claim_layout = initial_claim_layout;
        // `backward_layer_slot` tracks the scheduler-order index into
        // `_proof_layout.backward[...]`. The outer BTreeMap in
        // `dimension_reducing_inputs` pops highest-first (see
        // `GpuGKRDimensionReducingBackwardState::new`), which matches
        // `build_proof_layout_inputs_structural`'s dim-reducing slot numbering: slot 0 is
        // the highest layer_idx (`initial_layer_for_sumcheck`) and slots
        // ascend as we descend through the dim-reducing chain. Main layers
        // continue from slot `num_dim_reducing_layers` and count downward
        // through `compiled_circuit.layers[num_main - 1..=0]`.
        let mut backward_layer_slot: usize = 0;
        while let Some(mut prepared_layer) = self.prepare_next_layer_static(context)? {
            let layer_idx = prepared_layer.layer_idx;
            let mut execution = prepared_layer
                .schedule_execute_dimension_reducing_layer_from_workflow_state(
                    shared_state_handle,
                    shared_device_seed,
                    shared_device_claim_point,
                    shared_device_claims,
                    &shared_claim_layout,
                    proof_slab,
                    proof_layout,
                    backward_layer_slot,
                    mirror_layers_to_host,
                    context,
                )?;
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
            // Stream-ordered storage can be dropped once the layer's uploads and kernels have
            // been fully enqueued on exec_stream.
            self.purge_up_to_layer(layer_idx);
        }
        dimension_reducing_layers_range.end(stream)?;
        tracing_ranges.push(dimension_reducing_layers_range);

        let mut main_backward_state = self.into_main_layer_backward_state_static(
            compiled_circuit,
            external_challenges,
            false,
        );
        let mut main_layers = Vec::new();
        let main_layers_range = Range::new("gkr.backward.main_layers")?;
        main_layers_range.start(stream)?;
        while let Some(mut prepared_layer) =
            main_backward_state.prepare_next_layer_static(context)?
        {
            let layer_idx = prepared_layer.layer_idx;
            // SAFETY: `prepare_next_layer_static` released its `&mut`
            // borrow on `main_backward_state` when it returned. The
            // re-borrow here is read-only and lives only across the
            // scheduler call (which doesn't touch storage mutably).
            let storage_for_extras = main_backward_state.storage();
            let mut execution = prepared_layer.schedule_execute_main_layer_from_workflow_state(
                shared_state_handle,
                shared_device_seed,
                shared_device_claim_point,
                shared_device_claims,
                &shared_claim_layout,
                device_lookup_and_constraint_ptr,
                device_external_challenges_ptr,
                proof_slab,
                proof_layout,
                backward_layer_slot,
                mirror_layers_to_host,
                Some(storage_for_extras),
                context,
            )?;
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
            main_backward_state.purge_up_to_layer(layer_idx);
        }
        main_layers_range.end(stream)?;
        tracing_ranges.push(main_layers_range);

        let GpuGKRMainLayerBackwardState { storage: _, .. } = main_backward_state;
        // Remaining main-layer storage drops here after all exec-stream work has been scheduled.
        // The shared device buffers now hold the final backward handoff. The hot proof path
        // materializes them once, outside `gkr.backward.*`, before base-layer/WHIR host setup.
        // Stream-ordered drop: the device buffer stays alive on GPU until
        // all scheduled reads complete (last layer's per-element pointer
        // reads in eval_recipes_e4 / eval_continuation_recipes_e4).
        drop(device_lookup_and_constraint);
        // Backward-end join: per-layer joins already cover each layer's D2Hs individually, but
        // this defensive join gives a single "both streams drained through backward" point
        // before WHIR-setup callbacks on exec_stream read `workflow_state.points_for_claims_at_layer[0]`
        // and `workflow_state.seed`, and before `backward_scheduled.wait()`'s
        // `exec_stream.synchronize()` blocks the host thread.
        let backward_d2h_done = era_cudart::event::CudaEvent::create_with_flags(
            era_cudart::event::CudaEventCreateFlags::DISABLE_TIMING,
        )?;
        backward_d2h_done.record(context.get_d2h_stream())?;
        stream.wait_event(
            &backward_d2h_done,
            era_cudart::stream::CudaStreamWaitEventFlags::DEFAULT,
        )?;
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
            shared_state,
            initial_callbacks: workflow_initial_callbacks,
            external_challenges_device_keepalive: None,
            final_device_seed: Some(shared_device_seed),
            final_device_claim_point_and_batching: Some(shared_device_claim_point),
            final_claim_layout: Some(shared_claim_layout),
            final_seed_host: None,
            final_claim_point_and_batching_host: None,
        })
    }

    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn schedule_execute_backward_workflow(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        external_challenges: GKRExternalChallenges<BF, E>,
        initial_output_layer_idx: usize,
        top_layer_claims: BTreeMap<GKRAddress, E>,
        evaluation_point: Vec<E>,
        seed: Seed,
        batching_challenge: E,
        lookup_multiplicative_challenge: E,
        lookup_additive_challenge: E,
        proof_slab: Option<&DeviceAllocation<E4>>,
        proof_layout: &ProofLayout,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRBackwardScheduledExecution<BF, E>> {
        let mut shared_state = Box::new(ScheduledBackwardWorkflowState {
            claims_for_layers: BTreeMap::from([(
                initial_output_layer_idx,
                top_layer_claims.clone(),
            )]),
            points_for_claims_at_layer: BTreeMap::from([(
                initial_output_layer_idx,
                evaluation_point.clone(),
            )]),
            current_claims: top_layer_claims,
            current_claim_point: evaluation_point,
            current_batching_challenge: batching_challenge,
            lookup_multiplicative_challenge,
            lookup_additive_challenge,
            seed,
        });
        // Host seed / claim_point / batching_challenge are only available via this
        // test-path entry point; stage them into device buffers so the orchestrator's
        // device-resident seed + claim_point pipelines kick off with the right values.
        // All host staging must happen inside stream-scheduled callbacks per the GPU
        // scheduling contract (`HostAllocation` contents are only touched as stream ops);
        // the produced `Callbacks` ride along in the returned execution's keepalive.
        let mut initial_callbacks = Callbacks::new();
        let initial_d_seed =
            h2d_seed_from_host(context, &mut initial_callbacks, &shared_state.seed)?;
        let initial_d_claim_point_and_batching = h2d_claim_point_and_batching_from_host(
            context,
            &mut initial_callbacks,
            &shared_state.current_claim_point,
            shared_state.current_batching_challenge,
        )?;
        let (initial_d_claims, initial_claim_layout) = h2d_claims_from_host(
            context,
            &mut initial_callbacks,
            &shared_state.current_claims,
        )?;
        let device_lookup_and_constraint = h2d_lookup_and_constraint_from_shared_state::<E>(
            context,
            &mut initial_callbacks,
            crate::primitives::context::UnsafeMutAccessor::new(shared_state.as_mut()),
        )?;
        let mut external_challenges_flat = external_challenges
            .permutation_argument_linearization_challenges
            .to_vec();
        external_challenges_flat.push(external_challenges.permutation_argument_additive_part);
        let mut external_challenges_host =
            unsafe { context.alloc_host_uninit_slice(external_challenges_flat.len()) };
        unsafe {
            external_challenges_host
                .get_mut_accessor()
                .get_mut()
                .copy_from_slice(&external_challenges_flat);
        }
        let mut device_external_challenges = context
            .alloc(external_challenges_host.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(
            &mut device_external_challenges,
            &external_challenges_host,
            context.get_exec_stream(),
        )?;
        drop(external_challenges_host);

        let mut execution = self.schedule_execute_backward_workflow_from_shared_state(
            compiled_circuit,
            external_challenges,
            device_external_challenges.as_ptr(),
            shared_state,
            initial_d_seed,
            initial_d_claim_point_and_batching,
            initial_d_claims,
            initial_claim_layout,
            device_lookup_and_constraint,
            true,
            proof_slab,
            proof_layout,
            context,
        )?;
        execution.initial_callbacks.extend(initial_callbacks);
        execution.external_challenges_device_keepalive = Some(device_external_challenges);
        Ok(execution)
    }
}
