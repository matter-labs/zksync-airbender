use era_cudart::result::CudaResult;

use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::backward::kernels::{eq_group_tables_len, launch_build_eq_values_from_point};
use gpu_gkr::backward::{
    ClaimBufferLayout, GpuGKRBackwardScheduledExecution, GpuGKRDimensionReducingBackwardState,
};
use gpu_gkr::forward::{GpuGKRForwardOutput, GpuGKRTranscriptHandoff};
use gpu_gkr::proof_layout::ProofLayout;
use gpu_gkr::setup::{GpuGKRForwardSetup, GpuGKRForwardSetupHostKeepalive};
use gpu_prover_context::ProverContext;

use super::top_layer_claim_layout;

pub(in crate::proof) struct ForwardToBackwardHandoff {
    pub(in crate::proof) post_forward_handoff_range: Range,
    pub(in crate::proof) transcript_handoff: GpuGKRTranscriptHandoff<E4>,
    pub(in crate::proof) backward_state: GpuGKRDimensionReducingBackwardState,
    pub(in crate::proof) forward_setup_keepalive: GpuGKRForwardSetupHostKeepalive,
    pub(in crate::proof) d_lookup_challenges_for_backward: DeviceAllocation<E4>,
    pub(in crate::proof) d_seed: DeviceAllocation<u32>,
    pub(in crate::proof) d_evaluation_point_and_batching: DeviceAllocation<E4>,
    pub(in crate::proof) top_layer_claim_layout: ClaimBufferLayout,
    pub(in crate::proof) initial_d_claims: DeviceAllocation<E4>,
}

pub(in crate::proof) struct BackwardPhaseResult {
    pub(in crate::proof) backward_scheduled: GpuGKRBackwardScheduledExecution,
}

pub(in crate::proof) fn prepare_backward_handoff(
    forward_output: GpuGKRForwardOutput<BF, E4>,
    forward_setup: GpuGKRForwardSetup,
    mut d_seed: DeviceAllocation<u32>,
    final_trace_size_log_2: u32,
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
    let transcript_handoff = forward_output.transcript_handoff();
    let initial_layer_for_sumcheck = forward_output.initial_layer_for_sumcheck;
    let output_layer_for_sumcheck =
        forward_output.dimension_reducing_inputs[&initial_layer_for_sumcheck].clone();

    // E4 is four packed BF limbs, so the evaluations can be absorbed as u32 words.
    let d_flat_evals_u32: &era_cudart::slice::DeviceSlice<u32> = unsafe {
        transcript_handoff
            .device_flat_evaluations()
            .transmute::<u32>()
    };
    gpu_hash::blake2s::transcript_commit(&mut d_seed, d_flat_evals_u32, stream)?;
    let num_challenges = (final_trace_size_log_2 + 1) as usize;
    let mut d_evaluation_point_and_batching: DeviceAllocation<E4> =
        context.alloc(num_challenges, AllocationPlacement::BestFit)?;
    gpu_hash::blake2s::transcript_squeeze_e4(
        &mut d_seed,
        &mut d_evaluation_point_and_batching,
        stream,
    )?;

    let backward_state = forward_output.into_dimension_reducing_backward_state();
    let (forward_setup_keepalive, d_lookup_challenges_for_backward) =
        forward_setup.into_host_keepalive_taking_lookup_challenges();
    let top_layer_claim_layout = top_layer_claim_layout(&output_layer_for_sumcheck);
    let num_top_claims = top_layer_claim_layout.claim_count();
    let mut initial_d_claims: DeviceAllocation<E4> =
        context.alloc(num_top_claims, AllocationPlacement::BestFit)?;

    // Compute the initial claims directly from the reduced output polynomials.
    let poly_len = 1usize << final_trace_size_log_2;
    let mut eq_group_tables_for_init: DeviceAllocation<E4> = context.alloc(
        eq_group_tables_len(final_trace_size_log_2 as usize).max(1),
        AllocationPlacement::Top,
    )?;
    let mut eq_values_for_init: DeviceAllocation<E4> =
        context.alloc(poly_len, AllocationPlacement::Top)?;
    launch_build_eq_values_from_point(
        d_evaluation_point_and_batching.as_ptr(),
        0,
        final_trace_size_log_2 as usize,
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
        for reduced_io in output_layer_for_sumcheck.values() {
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
        gpu_gkr::gkr_initial_inner_products::initial_inner_product_e4(
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

pub(in crate::proof) fn schedule_backward_phase(
    backward_state: GpuGKRDimensionReducingBackwardState,
    // ACTUAL per-circuit i&t top bits: canonical for real i&t data, all
    // zeros for trivial (dummy) unified chunks (CPU-reference parity).
    inits_and_teardowns_top_bits: Vec<u32>,
    gkr_programs: std::sync::Arc<gpu_gkr::GkrPrograms>,
    d_external_challenges_ptr: *const E4,
    d_seed: DeviceAllocation<u32>,
    d_evaluation_point_and_batching: DeviceAllocation<E4>,
    initial_d_claims: DeviceAllocation<E4>,
    top_layer_claim_layout: ClaimBufferLayout,
    d_lookup_challenges_for_backward: DeviceAllocation<E4>,
    proof_slab: &DeviceAllocation<E4>,
    proof_layout: &ProofLayout,
    context: &ProverContext,
) -> CudaResult<BackwardPhaseResult> {
    let backward_scheduled = backward_state.schedule_execute_backward_workflow(
        inits_and_teardowns_top_bits,
        gkr_programs,
        d_external_challenges_ptr,
        d_seed,
        d_evaluation_point_and_batching,
        initial_d_claims,
        top_layer_claim_layout,
        d_lookup_challenges_for_backward,
        proof_slab,
        proof_layout,
        context,
    )?;
    Ok(BackwardPhaseResult { backward_scheduled })
}
