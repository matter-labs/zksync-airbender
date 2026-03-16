use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStreamWaitEventFlags;
use fft::GoodAllocator;
use field::Field;
use prover::definitions::Transcript;
use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use prover::gkr::prover::{GKRExternalChallenges, GKRProof, WhirSchedule};
use prover::merkle_trees::DefaultTreeConstructor;
use prover::prover_stages::query_producer::BitSource;
use prover::transcript::Seed;

use crate::circuit_type::CircuitType;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::decoder::DecoderTableTransfer;
use crate::prover::gkr::backward::{
    clone_backward_claims_for_layer, fill_backward_claim_point_for_layer,
    current_backward_batching_challenge, current_backward_seed,
    make_deferred_backward_workflow_state, populate_backward_workflow_state,
    take_backward_execution_from_shared_state, GpuGKRBackwardHostKeepalive,
};
use crate::prover::gkr::base_layer_claims::{
    fill_mem_polys_claims, fill_setup_polys_claims, fill_wit_polys_claims,
    schedule_prepare_base_layer_claims_with_sources,
    GpuGKRBaseLayerClaimsScheduledExecution,
};
use crate::prover::gkr::forward::{schedule_forward_pass, GpuGKRTranscriptHandoff};
use crate::prover::gkr::setup::{
    GpuGKRForwardSetupHostKeepalive, GpuGKRSetupTransfer, GpuGKRSetupTransferHostKeepalive,
};
use crate::prover::gkr::stage1::GpuGKRStage1Output;
use crate::prover::trace_holder::flatten_tree_caps;
use crate::prover::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::prover::whir_fold::{
    schedule_gpu_whir_fold_with_sources, take_scheduled_whir_proof, GpuWhirFoldScheduledExecution,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct GkrExternalPowChallenges {
    pub whir_pow_nonces: Vec<u64>,
}

struct GpuGKRProofJobKeepalive<'a> {
    #[allow(dead_code)]
    setup: GpuGKRSetupTransferHostKeepalive<'a>,
    #[allow(dead_code)]
    forward_setup: GpuGKRForwardSetupHostKeepalive<E4>,
    #[allow(dead_code)]
    transcript_handoff: GpuGKRTranscriptHandoff<E4>,
    #[allow(dead_code)]
    backward: GpuGKRBackwardHostKeepalive<BF, E4>,
    #[allow(dead_code)]
    base_layer_claims: GpuGKRBaseLayerClaimsScheduledExecution<E4>,
    #[allow(dead_code)]
    whir: GpuWhirFoldScheduledExecution,
}

pub(crate) struct GpuGKRProofJob<'a> {
    pub(crate) is_finished_event: CudaEvent,
    pub(crate) callbacks: Callbacks<'a>,
    pub(crate) proof: Arc<Mutex<Option<GKRProof<BF, E4, DefaultTreeConstructor>>>>,
    pub(crate) ranges: Vec<Range>,
    #[allow(dead_code)]
    keepalive: GpuGKRProofJobKeepalive<'a>,
}

impl<'a> GpuGKRProofJob<'a> {
    pub(crate) fn is_finished(&self) -> CudaResult<bool> {
        self.is_finished_event.query()
    }

    pub(crate) fn finish(self) -> CudaResult<(GKRProof<BF, E4, DefaultTreeConstructor>, f32)> {
        let Self {
            is_finished_event,
            callbacks,
            proof,
            ranges,
            keepalive,
        } = self;
        is_finished_event.synchronize()?;
        drop(callbacks);
        drop(keepalive);
        let proof = proof
            .lock()
            .unwrap()
            .take()
            .expect("proof must be materialized before finish");
        let proof_time_ms = ranges
            .last()
            .expect("proof job must keep the top-level range")
            .elapsed()?;

        Ok((proof, proof_time_ms))
    }
}

pub(crate) fn compute_initial_sumcheck_claims_from_explicit_evaluations<E: Field>(
    final_explicit_evaluations: &BTreeMap<OutputType, [Vec<E>; 2]>,
    eval_point: &[E],
) -> [E; 8] {
    let eq = make_eq_poly_in_full_serial(eval_point);
    let mut evals = Vec::with_capacity(8);
    for key in [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        let explicit_evals = &final_explicit_evaluations[&key];
        for poly in explicit_evals.iter() {
            evals.push(evaluate_ext_poly_with_eq(poly, &eq));
        }
    }

    evals.try_into().expect("expected exactly eight claims")
}

pub(crate) fn build_top_layer_claims(
    output_layer_for_sumcheck: &BTreeMap<
        OutputType,
        prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput,
    >,
    claims: [E4; 8],
) -> BTreeMap<GKRAddress, E4> {
    let [claim_readset, claim_writeset, claim_rangechecknum, claim_rangecheckden, claim_timechecknum, claim_timecheckden, claim_lookupnum, claim_lookupden] =
        claims;
    let mut top_layer_claims = BTreeMap::new();
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::PermutationProduct].output[0],
        claim_readset,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::PermutationProduct].output[1],
        claim_writeset,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::Lookup16Bits].output[0],
        claim_rangechecknum,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::Lookup16Bits].output[1],
        claim_rangecheckden,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::LookupTimestamps].output[0],
        claim_timechecknum,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::LookupTimestamps].output[1],
        claim_timecheckden,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::GenericLookup].output[0],
        claim_lookupnum,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::GenericLookup].output[1],
        claim_lookupden,
    );

    top_layer_claims
}

pub(crate) fn draw_query_bits_with_external_nonce(
    seed: &mut Seed,
    num_bits_for_queries: usize,
    pow_bits: u32,
    external_nonce: u64,
) -> (u64, BitSource) {
    if pow_bits == 0 {
        assert_eq!(
            external_nonce, 0,
            "pow_bits=0 expects the external nonce to be zero",
        );
    }
    Transcript::verify_pow(seed, external_nonce, pow_bits);

    (
        external_nonce,
        draw_query_bits_after_verified_pow(seed, num_bits_for_queries),
    )
}

pub(crate) fn draw_query_bits_after_verified_pow(
    seed: &mut Seed,
    num_bits_for_queries: usize,
) -> BitSource {
    let num_required_words =
        num_bits_for_queries.next_multiple_of(u32::BITS as usize) / (u32::BITS as usize);
    let num_required_words_padded =
        (num_required_words + 1).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
    let mut source = vec![0u32; num_required_words_padded];
    Transcript::draw_randomness(seed, &mut source);

    BitSource::new(source[1..].to_vec())
}

pub(crate) fn flatten_final_explicit_evaluations(
    final_explicit_evaluations: &BTreeMap<OutputType, [Vec<E4>; 2]>,
) -> Vec<E4> {
    let capacity = final_explicit_evaluations
        .values()
        .map(|evals| evals.iter().map(Vec::len).sum::<usize>())
        .sum();
    let mut flattened = Vec::with_capacity(capacity);
    for evals in final_explicit_evaluations.values() {
        for poly in evals.iter() {
            flattened.extend_from_slice(poly);
        }
    }

    flattened
}

pub(crate) fn grand_product_accumulator_from_explicit_evaluations(
    final_explicit_evaluations: &BTreeMap<OutputType, [Vec<E4>; 2]>,
) -> E4 {
    let [read_set_computed, write_set_computed] = final_explicit_evaluations
        .get(&OutputType::PermutationProduct)
        .expect("must contain permutation-product outputs")
        .clone()
        .map(|els| {
            let mut result = E4::ONE;
            for el in els.iter() {
                result.mul_assign(el);
            }
            result
        });
    let mut grand_product_accumulator_computed = read_set_computed;
    grand_product_accumulator_computed.mul_assign(
        &write_set_computed
            .inverse()
            .expect("write-set accumulator must not be zero"),
    );

    grand_product_accumulator_computed
}

fn collect_explicit_evaluations_from_accessors<E: Copy>(
    accessors: &BTreeMap<OutputType, [UnsafeAccessor<[E]>; 2]>,
) -> BTreeMap<OutputType, [Vec<E>; 2]> {
    accessors
        .iter()
        .map(|(output_type, evals)| {
            (
                *output_type,
                [
                    unsafe { evals[0].get() }.to_vec(),
                    unsafe { evals[1].get() }.to_vec(),
                ],
            )
        })
        .collect()
}

fn flatten_explicit_evaluations_from_accessors<E: Copy>(
    accessors: &BTreeMap<OutputType, [UnsafeAccessor<[E]>; 2]>,
) -> Vec<E> {
    let capacity = accessors
        .values()
        .map(|evals| unsafe { evals[0].get().len() + evals[1].get().len() })
        .sum();
    let mut flattened = Vec::with_capacity(capacity);
    for evals in accessors.values() {
        flattened.extend_from_slice(unsafe { evals[0].get() });
        flattened.extend_from_slice(unsafe { evals[1].get() });
    }
    flattened
}

fn flatten_tree_caps_from_slices<S: AsRef<[[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]]>>(
    caps: &[S],
    log_lde_factor: u32,
) -> Vec<u32> {
    let lde_factor = 1usize << log_lde_factor;
    assert_eq!(caps.len(), lde_factor);
    let mut flattened = Vec::with_capacity(
        caps.iter()
            .map(|cap| cap.as_ref().len() * BLAKE2S_DIGEST_SIZE_U32_WORDS)
            .sum(),
    );
    for stage1_pos in 0..lde_factor {
        let natural_coset_index = stage1_pos.reverse_bits() >> (usize::BITS - log_lde_factor);
        for digest in caps[natural_coset_index].as_ref() {
            flattened.extend_from_slice(digest);
        }
    }

    flattened
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn prove<'a, A: GoodAllocator + 'a>(
    circuit_type: CircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
    external_challenges: GKRExternalChallenges<BF, E4>,
    whir_schedule: WhirSchedule,
    final_trace_size_log_2: usize,
    mut setup_transfer: GpuGKRSetupTransfer<'a>,
    mut decoder_transfer: Option<DecoderTableTransfer<'a>>,
    inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a, A>>,
    mut tracing_data_transfer: TracingDataTransfer<'a, A>,
    external_pow_challenges: Option<GkrExternalPowChallenges>,
    context: &ProverContext,
) -> CudaResult<GpuGKRProofJob<'a>> {
    let stream = context.get_exec_stream();
    let mut callbacks = Callbacks::new();
    let proof = Arc::new(Mutex::new(None));
    let mut ranges = Vec::new();
    let proof_range = Range::new("gkr.proof")?;
    proof_range.start(stream)?;

    setup_transfer.schedule_transfer(context)?;
    if let Some(decoder_transfer) = decoder_transfer.as_mut() {
        decoder_transfer.schedule_transfer(context)?;
        decoder_transfer.transfer.ensure_transferred(context)?;
    }
    tracing_data_transfer.schedule_transfer(context)?;
    tracing_data_transfer.transfer.ensure_transferred(context)?;
    if let Some(mut inits_and_teardowns_transfer) = inits_and_teardowns_transfer {
        callbacks.extend(inits_and_teardowns_transfer.into_host_keepalive());
    }

    let mut stage1_output = GpuGKRStage1Output::generate(
        circuit_type,
        &compiled_circuit,
        &setup_transfer,
        decoder_transfer
            .as_ref()
            .map(|transfer| &transfer.data_device[..]),
        &tracing_data_transfer.data_device,
        context,
    )?;
    if let Some(decoder_transfer) = decoder_transfer {
        callbacks.extend(decoder_transfer.into_host_keepalive());
    }
    callbacks.extend(tracing_data_transfer.into_host_keepalive());

    let memory_base_caps_keepalive = stage1_output.memory_trace_holder.take_tree_caps_host();
    let witness_base_caps_keepalive = stage1_output.witness_trace_holder.take_tree_caps_host();
    let memory_base_caps_accessors = memory_base_caps_keepalive
        .iter()
        .map(HostAllocation::get_accessor)
        .collect::<Vec<_>>();
    let witness_base_caps_accessors = witness_base_caps_keepalive
        .iter()
        .map(HostAllocation::get_accessor)
        .collect::<Vec<_>>();
    let memory_log_lde_factor = stage1_output.memory_trace_holder.log_lde_factor;
    let witness_log_lde_factor = stage1_output.witness_trace_holder.log_lde_factor;
    let setup_log_lde_factor = setup_transfer.host.log_lde_factor;
    let flattened_setup_tree_caps = flatten_tree_caps_from_slices(
        &setup_transfer
            .host
            .tree_caps
            .iter()
            .map(|cap| cap.as_slice())
            .collect::<Vec<_>>(),
        setup_log_lde_factor,
    );

    let mut seed_host = unsafe { context.alloc_host_uninit::<Seed>() };
    let seed_accessor = seed_host.get_mut_accessor();
    let mut lookup_challenges_host = unsafe { context.alloc_transient_host_uninit_slice(3) };
    let lookup_challenges_write_accessor = lookup_challenges_host.get_mut_accessor();
    let lookup_challenges_read_accessor = lookup_challenges_host.get_accessor();
    let external_challenges_for_seed = external_challenges.clone();
    callbacks.schedule(
        move || unsafe {
            let mut transcript_input = Vec::new();
            external_challenges_for_seed.flatten_into_buffer(&mut transcript_input);
            transcript_input.extend_from_slice(&flattened_setup_tree_caps);
            transcript_input.extend(flatten_tree_caps(
                &memory_base_caps_accessors,
                memory_log_lde_factor,
            ));
            transcript_input.extend(flatten_tree_caps(
                &witness_base_caps_accessors,
                witness_log_lde_factor,
            ));
            seed_accessor.set(Transcript::commit_initial(&transcript_input));
            let challenges = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 3);
            lookup_challenges_write_accessor
                .get_mut()
                .copy_from_slice(&challenges);
        },
        stream,
    )?;

    let mut forward_setup = setup_transfer.schedule_forward_setup(
        &compiled_circuit,
        lookup_challenges_host,
        context,
    )?;
    let forward_output = schedule_forward_pass(
        &setup_transfer,
        &mut stage1_output,
        &mut forward_setup,
        &compiled_circuit,
        &external_challenges,
        final_trace_size_log_2,
        context,
    )?;
    let transcript_handoff = forward_output.schedule_transcript_handoff(context)?;
    let transcript_handoff_accessors_for_backward =
        transcript_handoff.explicit_evaluation_accessors();
    let transcript_handoff_accessors_for_final = transcript_handoff.explicit_evaluation_accessors();
    let initial_layer_for_sumcheck = forward_output.initial_layer_for_sumcheck;
    let output_layer_for_sumcheck =
        forward_output.dimension_reducing_inputs[&initial_layer_for_sumcheck].clone();
    let backward_state = forward_output.into_dimension_reducing_backward_state();
    let mut forward_setup_keepalive = forward_setup.into_host_keepalive();

    let backward_shared_state = make_deferred_backward_workflow_state();
    callbacks.schedule(
        {
            let backward_shared_state = Arc::clone(&backward_shared_state);
            let lookup_challenges_read_accessor = lookup_challenges_read_accessor;
            move || unsafe {
                let final_explicit_evaluations = collect_explicit_evaluations_from_accessors(
                    &transcript_handoff_accessors_for_backward,
                );
                let flattened = flatten_final_explicit_evaluations(&final_explicit_evaluations);
                commit_field_els::<BF, E4>(seed_accessor.get_mut(), &flattened);
                let num_challenges = final_trace_size_log_2 + 1;
                let mut challenges =
                    draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), num_challenges);
                let batching_challenge = challenges.pop().unwrap();
                let evaluation_point = challenges;
                let initial_claims = compute_initial_sumcheck_claims_from_explicit_evaluations(
                    &final_explicit_evaluations,
                    &evaluation_point,
                );
                let top_layer_claims =
                    build_top_layer_claims(&output_layer_for_sumcheck, initial_claims);
                let lookup_challenges = lookup_challenges_read_accessor.get();
                populate_backward_workflow_state(
                    &backward_shared_state,
                    initial_layer_for_sumcheck + 1,
                    top_layer_claims,
                    evaluation_point,
                    seed_accessor.get().clone(),
                    batching_challenge,
                    lookup_challenges[1],
                    lookup_challenges[2],
                );
            }
        },
        stream,
    )?;

    let backward_scheduled = backward_state.schedule_execute_backward_workflow_from_shared_state(
        compiled_circuit.clone(),
        Arc::clone(&backward_shared_state),
        context,
    )?;
    let base_layer_claims_scheduled = schedule_prepare_base_layer_claims_with_sources(
        compiled_circuit.layers[0].clone(),
        compiled_circuit.trace_len.trailing_zeros() as usize,
        {
            let backward_shared_state = Arc::clone(&backward_shared_state);
            move |dst| {
                fill_backward_claim_point_for_layer(&backward_shared_state, 0, dst);
            }
        },
        {
            let backward_shared_state = Arc::clone(&backward_shared_state);
            move || clone_backward_claims_for_layer(&backward_shared_state, 0)
        },
        &setup_transfer.trace_holder,
        &stage1_output.memory_trace_holder,
        &stage1_output.witness_trace_holder,
        context,
    )?;
    let base_layer_claims_shared_state = base_layer_claims_scheduled.shared_state_handle();
    let setup_base_caps_keepalive = setup_transfer.trace_holder.take_tree_caps_host();
    let whir_scheduled = schedule_gpu_whir_fold_with_sources(
        &mut stage1_output.memory_trace_holder,
        memory_base_caps_keepalive,
        {
            let base_layer_claims_shared_state = Arc::clone(&base_layer_claims_shared_state);
            move |dst| fill_mem_polys_claims(&base_layer_claims_shared_state, dst)
        },
        &mut stage1_output.witness_trace_holder,
        witness_base_caps_keepalive,
        {
            let base_layer_claims_shared_state = Arc::clone(&base_layer_claims_shared_state);
            move |dst| fill_wit_polys_claims(&base_layer_claims_shared_state, dst)
        },
        &mut setup_transfer.trace_holder,
        setup_base_caps_keepalive,
        {
            let base_layer_claims_shared_state = Arc::clone(&base_layer_claims_shared_state);
            move |dst| fill_setup_polys_claims(&base_layer_claims_shared_state, dst)
        },
        compiled_circuit.trace_len.trailing_zeros() as usize,
        {
            let backward_shared_state = Arc::clone(&backward_shared_state);
            move |dst| {
                fill_backward_claim_point_for_layer(&backward_shared_state, 0, dst);
            }
        },
        whir_schedule.base_lde_factor,
        {
            let backward_shared_state = Arc::clone(&backward_shared_state);
            move || current_backward_batching_challenge(&backward_shared_state)
        },
        whir_schedule.whir_steps_schedule.clone(),
        whir_schedule.whir_queries_schedule.clone(),
        whir_schedule.whir_steps_lde_factors.clone(),
        whir_schedule.whir_pow_schedule.clone(),
        {
            let backward_shared_state = Arc::clone(&backward_shared_state);
            move || current_backward_seed(&backward_shared_state)
        },
        whir_schedule.cap_size,
        compiled_circuit.trace_len.trailing_zeros() as usize,
        external_pow_challenges.map(|pow| pow.whir_pow_nonces),
        context,
    )?;
    let whir_shared_state = whir_scheduled.shared_state_handle();

    let backward_keepalive = backward_scheduled.into_host_keepalive();
    let setup_keepalive = setup_transfer.into_host_keepalive();

    callbacks.schedule(
        {
            let proof_slot = Arc::clone(&proof);
            let backward_shared_state = Arc::clone(&backward_shared_state);
            let whir_shared_state = Arc::clone(&whir_shared_state);
            let external_challenges = external_challenges.clone();
            move || {
                let final_explicit_evaluations = collect_explicit_evaluations_from_accessors(
                    &transcript_handoff_accessors_for_final,
                );
                let backward_execution =
                    take_backward_execution_from_shared_state(&backward_shared_state);
                let whir_proof = take_scheduled_whir_proof(&whir_shared_state);
                let grand_product_accumulator_computed =
                    grand_product_accumulator_from_explicit_evaluations(
                        &final_explicit_evaluations,
                    );
                *proof_slot.lock().unwrap() = Some(GKRProof {
                    external_challenges: external_challenges.clone(),
                    final_explicit_evaluations,
                    sumcheck_intermediate_values: backward_execution.proofs,
                    whir_proof,
                    grand_product_accumulator_computed,
                });
            }
        },
        stream,
    )?;

    {
        let event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
        event.record(stream)?;
        context
            .get_h2d_stream()
            .wait_event(&event, CudaStreamWaitEventFlags::DEFAULT)?;
    }

    proof_range.end(stream)?;
    ranges.push(proof_range);

    let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    is_finished_event.record(stream)?;
    Ok(GpuGKRProofJob {
        is_finished_event,
        callbacks,
        proof,
        ranges,
        keepalive: GpuGKRProofJobKeepalive {
            setup: setup_keepalive,
            forward_setup: forward_setup_keepalive,
            transcript_handoff,
            backward: backward_keepalive,
            base_layer_claims: base_layer_claims_scheduled,
            whir: whir_scheduled,
        },
    })
}

fn evaluate_ext_poly_with_eq<E: Field>(values: &[E], eq: &[E]) -> E {
    assert_eq!(values.len(), eq.len());
    let mut result = E::ZERO;
    for (value, eq_value) in values.iter().zip(eq.iter()) {
        let mut term = *value;
        term.mul_assign(eq_value);
        result.add_assign(&term);
    }

    result
}

fn make_eq_poly_in_full_serial<E: Field>(challenges: &[E]) -> Vec<E> {
    assert!(!challenges.is_empty());
    let mut layer = vec![E::ONE];
    for challenge in challenges.iter().rev().copied() {
        let mut next = vec![E::ZERO; layer.len() * 2];
        let (left, right) = next.split_at_mut(layer.len());
        for (src, (left_dst, right_dst)) in layer.iter().zip(left.iter_mut().zip(right.iter_mut()))
        {
            let mut right_value = *src;
            right_value.mul_assign(&challenge);
            let mut left_value = *src;
            left_value.sub_assign(&right_value);
            *left_dst = left_value;
            *right_dst = right_value;
        }
        layer = next;
    }

    layer
}

#[cfg(test)]
mod tests {
    use super::draw_query_bits_with_external_nonce;
    use prover::gkr::prover::transcript_utils::draw_query_bits;
    use prover::prover_stages::query_producer::assemble_query_index;
    use prover::transcript::Seed;
    use worker::Worker;

    #[test]
    fn external_nonce_query_bits_match_cpu_draw_query_bits() {
        let worker = Worker::new();
        let cases = [
            (Seed([1, 2, 3, 4, 5, 6, 7, 8]), 23usize, 22usize, 24u32),
            (Seed([11, 12, 13, 14, 15, 16, 17, 18]), 12usize, 21usize, 24u32),
            (Seed([21, 22, 23, 24, 25, 26, 27, 28]), 10usize, 18usize, 16u32),
            (Seed([31, 32, 33, 34, 35, 36, 37, 38]), 10usize, 14usize, 0u32),
        ];

        for (seed, num_queries, query_index_bits, pow_bits) in cases {
            let num_bits_for_queries = num_queries * query_index_bits;
            let mut cpu_seed = seed;
            let mut external_seed = seed;
            let (cpu_nonce, mut cpu_bits) =
                draw_query_bits(&mut cpu_seed, num_bits_for_queries, pow_bits, &worker);
            let (external_nonce, mut external_bits) = draw_query_bits_with_external_nonce(
                &mut external_seed,
                num_bits_for_queries,
                pow_bits,
                cpu_nonce,
            );

            assert_eq!(external_nonce, cpu_nonce, "external nonce changed");
            assert_eq!(external_seed, cpu_seed, "seed after external PoW diverged");

            let mut cpu_indexes = Vec::with_capacity(num_queries);
            let mut external_indexes = Vec::with_capacity(num_queries);
            for _ in 0..num_queries {
                cpu_indexes.push(assemble_query_index(query_index_bits, &mut cpu_bits));
                external_indexes.push(assemble_query_index(query_index_bits, &mut external_bits));
            }
            assert_eq!(
                external_indexes, cpu_indexes,
                "query indexes diverged for pow_bits={pow_bits}"
            );
        }
    }
}
