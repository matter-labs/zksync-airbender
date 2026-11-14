use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, UnsafeMutAccessor};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::packed::PackedCosetRecomputeOracle;

use super::backward::dr_tail::PR_DR_FINAL_TRACE_LOG_2;
use super::backward::{schedule_backward_pr, DrTailProofPlanPr, GKRBackwardStageSnapshotSinkPr};
use super::base_layer_claims::BaseClaimGatherPr;
use super::forward::{
    prepare_backward_handoff_pr, schedule_forward_challenge_banks, schedule_forward_pass_pr,
};
use super::inputs::Proth120GkrWitnessInputs;
use super::packed_challenges::PackedChallenges;
use super::packed_merge::{schedule_base_layer_claims_and_packed_merge_pr, GkrOutputPr};
use super::programs::GkrProgramsPr;
use super::proof_layout::ProofSlabPr;
use crate::setup::PackedSetupSource;
use crate::upstream::{ProverConfig, PR};

/// Per-proof GKR launch constants, passed by value.
#[derive(Clone, Copy)]
pub struct GkrPreparedInputsPr {
    pub base_claim_indices: BaseClaimGatherPr,
}

#[allow(clippy::too_many_arguments)]
pub fn schedule_gkr(
    programs: Arc<GkrProgramsPr>,
    base: &PackedCosetRecomputeOracle<PR>,
    setup: &PackedSetupSource<'_>,
    witness: Proth120GkrWitnessInputs<'_>,
    inits_and_teardowns_top_bits: &[u32],
    challenges: &PackedChallenges,
    config: &ProverConfig,
    batching_pow_bits: u32,
    seed: DeviceAllocation<u8>,
    proof: &mut ProofSlabPr,
    dr_tail_plan: &DrTailProofPlanPr,
    stage_snapshots: Option<UnsafeMutAccessor<GKRBackwardStageSnapshotSinkPr>>,
    prepared: GkrPreparedInputsPr,
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<GkrOutputPr> {
    let GkrPreparedInputsPr { base_claim_indices } = prepared;
    assert_eq!(
        config.trace_len_log2,
        base.log_rows() as usize,
        "Proth120 facade trace log mismatch"
    );
    assert_eq!(
        config.sumcheck_explicit_output_size_log_2, PR_DR_FINAL_TRACE_LOG_2 as usize,
        "Proth120 facade final trace log must be {PR_DR_FINAL_TRACE_LOG_2}"
    );
    let pack_log2 = proof.layout.pack_log2() as u32;
    assert_eq!(
        base.pack_log2(),
        pack_log2,
        "Proth120 facade base packing differs from the admitted proof layout"
    );
    assert_eq!(
        setup.host.pack_log2, pack_log2,
        "Proth120 facade setup packing differs from the admitted proof layout"
    );
    assert_eq!(seed.len(), 32, "Proth120 facade seed length mismatch");
    assert_eq!(
        inits_and_teardowns_top_bits.len(),
        programs.runtime_circuit.memory_layout.teardown_sets.len(),
        "Proth120 facade top bits count mismatch"
    );

    let stream = context.get_exec_stream();
    memory_copy_async(
        proof.external_challenges_device_mut(),
        challenges.challenges(),
        stream,
    )?;
    memory_copy_async(proof.lookup_nonce_device_mut(), challenges.nonce(), stream)?;
    let banks = schedule_forward_challenge_banks(challenges, &programs.challenge_plan, context)?;
    let forward = schedule_forward_pass_pr(
        base,
        setup,
        &witness,
        &banks,
        inits_and_teardowns_top_bits,
        PR_DR_FINAL_TRACE_LOG_2,
        proof.output_evaluations_target(),
        &programs,
        context,
    )?;

    drop(witness);

    drop(banks);
    let handoff = prepare_backward_handoff_pr(forward, seed, PR_DR_FINAL_TRACE_LOG_2, context)?;
    let mut backward = schedule_backward_pr(
        handoff,
        inits_and_teardowns_top_bits.to_vec(),
        programs,
        dr_tail_plan,
        challenges,
        proof,
        stage_snapshots,
        callbacks,
        context,
    )?;
    let mut output = schedule_base_layer_claims_and_packed_merge_pr(
        &mut backward,
        base,
        setup,
        pack_log2,
        batching_pow_bits,
        base_claim_indices,
        proof,
        context,
    )?;

    backward.release_device_buffers();

    output.backward = Some(backward);
    Ok(output)
}
