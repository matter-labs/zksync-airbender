use era_cudart::result::CudaResult;

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::context::ProverContext;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::backward::kernels::{
    eq_group_tables_len, launch_build_eq_values_from_point, ScheduledBackwardWorkflowStateHandle,
};
use crate::prover::gkr::backward::{
    ClaimBufferLayout, GpuGKRBackwardScheduledExecution, GpuGKRDimensionReducingBackwardState,
    ScheduledBackwardWorkflowState,
};
use crate::prover::gkr::forward::{GpuGKRForwardOutput, GpuGKRTranscriptHandoff};
use crate::prover::gkr::setup::{GpuGKRForwardSetup, GpuGKRForwardSetupHostKeepalive};
use crate::prover::proof::layout::ProofLayout;
use crate::upstream::{GKRCircuitArtifact, GKRExternalChallenges};

use super::top_layer_claim_layout;

pub(in crate::prover::proof) struct ForwardToBackwardHandoff {
    pub(in crate::prover::proof) post_forward_handoff_range: Range,
    pub(in crate::prover::proof) transcript_handoff: GpuGKRTranscriptHandoff<E4>,
    pub(in crate::prover::proof) backward_state: GpuGKRDimensionReducingBackwardState<BF, E4>,
    pub(in crate::prover::proof) forward_setup_keepalive: GpuGKRForwardSetupHostKeepalive<E4>,
    pub(in crate::prover::proof) d_lookup_challenges_for_backward: DeviceAllocation<E4>,
    pub(in crate::prover::proof) d_seed: DeviceAllocation<u32>,
    pub(in crate::prover::proof) d_evaluation_point_and_batching: DeviceAllocation<E4>,
    pub(in crate::prover::proof) top_layer_claim_layout: ClaimBufferLayout,
    pub(in crate::prover::proof) initial_d_claims: DeviceAllocation<E4>,
}

pub(in crate::prover::proof) struct BackwardPhaseResult {
    pub(in crate::prover::proof) backward_scheduled: GpuGKRBackwardScheduledExecution<BF, E4>,
    pub(in crate::prover::proof) backward_shared_state: ScheduledBackwardWorkflowStateHandle<E4>,
}

pub(in crate::prover::proof) fn prepare_backward_handoff(
    forward_output: GpuGKRForwardOutput<BF, E4>,
    forward_setup: GpuGKRForwardSetup<E4>,
    mut d_seed: DeviceAllocation<u32>,
    final_trace_size_log_2: usize,
    context: &ProverContext,
) -> CudaResult<ForwardToBackwardHandoff> {
    let stream = context.get_exec_stream();
    let post_forward_handoff_range = Range::new("gkr.proof.post_forward_handoff")?;
    post_forward_handoff_range.start(stream)?;

    // The reduced-output polys at the initial sumcheck layer share a single
    // consolidated backing. In the proof path, the final forward dim-reduction
    // writes that backing directly into the slab's `output_evaluations` prefix;
    // the terminal slab D2H then mirrors it back to host as part of the single
    // batched copy.
    let transcript_handoff = forward_output.schedule_transcript_handoff(false, context)?;
    let initial_layer_for_sumcheck = forward_output.initial_layer_for_sumcheck;
    let output_layer_for_sumcheck =
        forward_output.dimension_reducing_inputs[&initial_layer_for_sumcheck].clone();

    // Device post-forward transcript: absorb flattened explicit evaluations into d_seed and
    // squeeze the evaluation point + batching challenge. Replaces the previous host pair
    // `commit_field_els` / `draw_random_field_els` on the host seed.
    //
    // SAFETY: `device_flat_evaluations` is a packed `DeviceAllocation<E4>` whose u32 byte
    // layout matches `commit_field_els::<BF, E4>` — E4 = 4 BF limbs, each limb stored as a
    // u32 in Montgomery form. The parity is covered by
    // `ops::blake2s::tests::transcript_squeeze_e4_parity_*`.
    let d_flat_evals_u32: &era_cudart::slice::DeviceSlice<u32> = unsafe {
        transcript_handoff
            .device_flat_evaluations()
            .transmute::<u32>()
    };
    crate::ops::blake2s::transcript_commit(&mut d_seed, d_flat_evals_u32, stream)?;
    let num_challenges = final_trace_size_log_2 + 1;
    let mut d_evaluation_point_and_batching: DeviceAllocation<E4> =
        context.alloc(num_challenges, AllocationPlacement::BestFit)?;
    crate::ops::blake2s::transcript_squeeze_e4(
        &mut d_seed,
        &mut d_evaluation_point_and_batching,
        stream,
    )?;

    // The (evaluation_point || batching_challenge) and seed buffers stay device-resident:
    // `d_evaluation_point_and_batching` flows into the first backward layer as
    // `initial_d_claim_point_and_batching` (claim_point + batching challenge, matching
    // the `round_scratch.claim_point` layout); `d_seed` threads through as `device_seed`.
    let backward_state = forward_output.into_dimension_reducing_backward_state();
    let (forward_setup_keepalive, d_lookup_challenges_for_backward) =
        forward_setup.into_host_keepalive_taking_lookup_challenges();
    let top_layer_claim_layout = top_layer_claim_layout(&output_layer_for_sumcheck);
    let num_top_claims = top_layer_claim_layout.len();
    let mut initial_d_claims: DeviceAllocation<E4> =
        context.alloc(num_top_claims, AllocationPlacement::BestFit)?;

    // GPU-side initial claim computation: the top-layer sumcheck claims were
    // previously computed on host via `compute_initial_sumcheck_claims_from_explicit_evaluations`
    // (build eq poly from evaluation_point, inner-product against each reduced
    // output poly) inside the post-forward callback, then H2D'd into
    // `initial_d_claims`. Both the eq build and the 8 inner products now run
    // on device, writing `initial_d_claims` directly; the callback D2Hs the 8
    // resulting scalars for the host-side workflow_state mirror.
    let poly_len = 1usize << final_trace_size_log_2;
    let mut eq_group_tables_for_init: DeviceAllocation<E4> = context.alloc(
        eq_group_tables_len(final_trace_size_log_2).max(1),
        AllocationPlacement::Top,
    )?;
    let mut eq_values_for_init: DeviceAllocation<E4> =
        context.alloc(poly_len, AllocationPlacement::Top)?;
    launch_build_eq_values_from_point::<E4>(
        d_evaluation_point_and_batching.as_ptr(),
        0,
        final_trace_size_log_2,
        eq_group_tables_for_init.as_mut_ptr(),
        eq_values_for_init.as_mut_ptr(),
        poly_len,
        context,
    )?;
    // Top-layer polys are written into `device_flat_evaluations` in iteration
    // order (BTreeMap-by-OutputType, 2 polys per OutputType). The slot order
    // from `top_layer_claim_layout` sorts the same address set by
    // (layer, offset), where offsets come from
    // `derive_dimension_reducing_inputs` in the *same* iteration
    // order. Both orderings collapse to OutputType-ordinal × half-index, so
    // `slot == poly_idx` for every poly — no pointer table needed; the kernel
    // computes its own per-block pointer from `polys_base + i * poly_len`.
    // The `assert!` below pins the invariant in production builds.
    {
        let device_flat_evaluations = transcript_handoff.device_flat_evaluations();
        let mut poly_idx = 0usize;
        for (_output_type, reduced_io) in output_layer_for_sumcheck.iter() {
            for half in 0..2 {
                let address = reduced_io.output[half];
                let slot = top_layer_claim_layout.claim_idx(&address) as usize;
                assert_eq!(
                    slot, poly_idx,
                    "top-layer claim layout slot order must match BTreeMap iteration order \
                     (slot={slot}, poly_idx={poly_idx}); the kernel relies on this identity \
                     permutation to derive each poly's base pointer from polys_base + i * poly_len",
                );
                poly_idx += 1;
            }
        }
        crate::prover::gkr::gkr_initial_inner_products::initial_inner_product_e4(
            device_flat_evaluations.as_ptr(),
            num_top_claims,
            &eq_values_for_init,
            poly_len as u32,
            &mut initial_d_claims,
            stream,
        )?;
    }

    post_forward_handoff_range.end(stream)?;
    Ok(ForwardToBackwardHandoff {
        post_forward_handoff_range,
        transcript_handoff,
        backward_state,
        forward_setup_keepalive,
        d_lookup_challenges_for_backward,
        d_seed,
        d_evaluation_point_and_batching,
        top_layer_claim_layout,
        initial_d_claims,
    })
}

pub(in crate::prover::proof) fn schedule_backward_phase(
    backward_state: GpuGKRDimensionReducingBackwardState<BF, E4>,
    compiled_circuit: GKRCircuitArtifact<BF>,
    external_challenges: GKRExternalChallenges<BF, E4>,
    d_external_challenges_ptr: *const E4,
    backward_shared_state: Box<ScheduledBackwardWorkflowState<E4>>,
    d_seed: DeviceAllocation<u32>,
    d_evaluation_point_and_batching: DeviceAllocation<E4>,
    initial_d_claims: DeviceAllocation<E4>,
    top_layer_claim_layout: ClaimBufferLayout,
    d_lookup_challenges_for_backward: DeviceAllocation<E4>,
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
    context: &ProverContext,
) -> CudaResult<BackwardPhaseResult> {
    let mut backward_scheduled = backward_state
        .schedule_execute_backward_workflow_from_shared_state(
            compiled_circuit,
            external_challenges,
            d_external_challenges_ptr,
            backward_shared_state,
            d_seed,
            d_evaluation_point_and_batching,
            initial_d_claims,
            top_layer_claim_layout,
            d_lookup_challenges_for_backward,
            false,
            proof_slab,
            proof_layout,
            context,
        )?;
    let backward_shared_state = backward_scheduled.shared_state_handle();
    Ok(BackwardPhaseResult {
        backward_scheduled,
        backward_shared_state,
    })
}
