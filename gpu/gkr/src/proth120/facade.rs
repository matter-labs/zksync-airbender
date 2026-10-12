use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, UnsafeMutAccessor};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::packed::PackedCosetRecomputeOracle;

use super::backward::{schedule_backward_pr, DrTailProofPlanPr, GKRBackwardStageSnapshotSinkPr};
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
    callbacks: &mut Callbacks<'_>,
    context: &ProverContext,
) -> CudaResult<GkrOutputPr> {
    assert_eq!(
        config.trace_len_log2,
        base.log_rows() as usize,
        "Proth120 facade trace log mismatch"
    );
    assert_eq!(
        config.sumcheck_explicit_output_size_log_2, 4,
        "Proth120 facade final trace log must be 4"
    );
    assert_eq!(base.pack_log2(), 4, "Proth120 facade requires pack_log2=4");
    assert_eq!(
        setup.host.pack_log2, 4,
        "Proth120 facade setup requires pack_log2=4"
    );
    assert_eq!(seed.len(), 32, "Proth120 facade seed length mismatch");
    assert_eq!(
        inits_and_teardowns_top_bits.len(),
        programs.runtime_circuit.memory_layout.teardown_sets.len(),
        "Proth120 facade top bits count mismatch"
    );
    dr_tail_plan.validate_before_enqueue(&programs, 4, context);
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
        4,
        proof.output_evaluations_target(),
        &programs,
        context,
    )?;
    drop(witness);
    drop(banks);
    let handoff = prepare_backward_handoff_pr(forward, seed, 4, context)?;
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
        4,
        batching_pow_bits,
        proof,
        context,
    )?;
    backward.release_device_buffers();
    output.backward = Some(backward);
    Ok(output)
}
