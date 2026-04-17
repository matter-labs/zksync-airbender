use std::collections::BTreeMap;

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
use prover::query_utils::BitSource;
use prover::transcript::Seed;

use crate::circuit_type::CircuitType;
use crate::ops::blake2s::Digest;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{
    HostAllocation, ProverContext, UnsafeAccessor, UnsafeMutAccessor,
};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::decoder::DecoderTableTransfer;
use crate::prover::gkr::backward::{
    apply_base_layer_extra_evaluations_to_workflow_state, clone_backward_claims_for_layer,
    current_backward_seed, fill_backward_claim_point_for_layer,
    make_deferred_backward_workflow_state, populate_backward_workflow_state,
    take_backward_execution_from_shared_state, GpuGKRBackwardHostKeepalive,
};
use crate::prover::gkr::base_layer_claims::{
    clone_base_layer_extra_evaluations_from_caching_relations,
    clone_base_layer_extra_evaluations_transcript_batches, fill_mem_polys_claims,
    fill_setup_polys_claims, fill_wit_polys_claims,
    schedule_prepare_base_layer_claims_with_sources, GpuGKRBaseLayerClaimsScheduledExecution,
};
use crate::prover::gkr::forward::schedule_forward_pass;
use crate::prover::gkr::setup::{
    schedule_forward_setup_for_shape, GpuGKRForwardSetupHostKeepalive, GpuGKRSetupTransfer,
    GpuGKRSetupTransferHostKeepalive,
};
use crate::prover::gkr::stage1::{GpuGKRStage1Keepalive, GpuGKRStage1Output, GpuGKRTraceGeometry};
use crate::prover::trace_holder::{
    allocate_tree_caps, allocate_trees, flatten_tree_caps, TraceHolder, TreesCacheMode,
    TreesHolder, PARTIAL_TREE_REDUCTION_LAYERS,
};
use crate::prover::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::prover::whir_fold::{
    schedule_gpu_whir_fold_with_sources, take_scheduled_whir_proof, GpuWhirFoldScheduledExecution,
};
use prover::merkle_trees::MerkleTreeCapVarLength;

struct GpuGKRProofJobKeepalive<'a> {
    _stage1: GpuGKRStage1Keepalive,
    _setup: Option<GpuGKRSetupTransferHostKeepalive<'a>>,
    _forward_setup: GpuGKRForwardSetupHostKeepalive<E4>,
    _backward: GpuGKRBackwardHostKeepalive<BF, E4>,
    _base_layer_claims: GpuGKRBaseLayerClaimsScheduledExecution<E4>,
    _whir: GpuWhirFoldScheduledExecution,
}

pub(crate) struct GpuGKRProofJob<'a> {
    pub(crate) is_finished_event: CudaEvent,
    pub(crate) callbacks: Callbacks<'a>,
    pub(crate) proof: Box<Option<GKRProof<BF, E4, DefaultTreeConstructor>>>,
    pub(crate) ranges: Vec<Range>,
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
            mut proof,
            ranges,
            keepalive,
        } = self;
        is_finished_event.synchronize()?;
        drop(callbacks);
        drop(keepalive);
        let proof = proof
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
        if let Some(explicit_evals) = final_explicit_evaluations.get(&key) {
            for poly in explicit_evals.iter() {
                evals.push(evaluate_ext_poly_with_eq(poly, &eq));
            }
        } else {
            evals.push(E::ZERO);
            evals.push(E::ZERO);
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
    let permutation_output = &output_layer_for_sumcheck[&OutputType::PermutationProduct];
    top_layer_claims.insert(permutation_output.output[0], claim_readset);
    top_layer_claims.insert(permutation_output.output[1], claim_writeset);
    if let Some(output) = output_layer_for_sumcheck.get(&OutputType::Lookup16Bits) {
        top_layer_claims.insert(output.output[0], claim_rangechecknum);
        top_layer_claims.insert(output.output[1], claim_rangecheckden);
    }
    if let Some(output) = output_layer_for_sumcheck.get(&OutputType::LookupTimestamps) {
        top_layer_claims.insert(output.output[0], claim_timechecknum);
        top_layer_claims.insert(output.output[1], claim_timecheckden);
    }
    if let Some(output) = output_layer_for_sumcheck.get(&OutputType::GenericLookup) {
        top_layer_claims.insert(output.output[0], claim_lookupnum);
        top_layer_claims.insert(output.output[1], claim_lookupden);
    }

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
    let mut grand_product_accumulator_computed = write_set_computed;
    grand_product_accumulator_computed.mul_assign(
        &read_set_computed
            .inverse()
            .expect("read-set accumulator must not be zero"),
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

fn canonical_inits_and_teardowns_top_bits(compiled_circuit: &GKRCircuitArtifact<BF>) -> Vec<u32> {
    (0..compiled_circuit.memory_layout.teardown_sets.len() as u32).collect()
}

fn build_initial_transcript_input(
    canonical_top_bits: &[u32],
    external_challenges: &GKRExternalChallenges<BF, E4>,
    flattened_setup_tree_caps: &[u32],
    flattened_memory_tree_caps: &[u32],
    flattened_witness_tree_caps: &[u32],
) -> Vec<u32> {
    let mut transcript_input = Vec::new();
    transcript_input.extend_from_slice(canonical_top_bits);
    external_challenges.flatten_into_buffer(&mut transcript_input);
    if !flattened_setup_tree_caps.is_empty() {
        transcript_input.extend_from_slice(flattened_setup_tree_caps);
    }
    if !flattened_memory_tree_caps.is_empty() {
        transcript_input.extend_from_slice(flattened_memory_tree_caps);
    }
    if !flattened_witness_tree_caps.is_empty() {
        transcript_input.extend_from_slice(flattened_witness_tree_caps);
    }

    transcript_input
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn prove<'a, A: GoodAllocator + 'a>(
    circuit_type: CircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
    external_challenges: GKRExternalChallenges<BF, E4>,
    whir_schedule: WhirSchedule,
    final_trace_size_log_2: usize,
    mut setup_transfer: Option<GpuGKRSetupTransfer<'a>>,
    mut decoder_transfer: Option<DecoderTableTransfer<'a>>,
    inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a, A>>,
    mut tracing_data_transfer: TracingDataTransfer<'a, A>,
    memory_tree_caps: &[MerkleTreeCapVarLength],
    context: &ProverContext,
) -> CudaResult<GpuGKRProofJob<'a>> {
    if let Some(setup_transfer) = setup_transfer.as_ref() {
        setup_transfer.ensure_transferred(context)?;
    }
    if let Some(decoder_transfer) = decoder_transfer.as_ref() {
        decoder_transfer.transfer.ensure_transferred(context)?;
    }
    if let Some(inits_and_teardowns_transfer) = inits_and_teardowns_transfer.as_ref() {
        inits_and_teardowns_transfer
            .transfer
            .ensure_transferred(context)?;
    }
    tracing_data_transfer.transfer.ensure_transferred(context)?;

    let stream = context.get_exec_stream();
    let mut callbacks = Callbacks::new();
    let mut proof = Box::new(None);
    let proof_handle = UnsafeMutAccessor::new(proof.as_mut());
    let mut ranges = Vec::new();
    let proof_range = Range::new("gkr.proof")?;
    proof_range.start(stream)?;

    context.reset_used_mem_peak();
    let setup_geometry = setup_transfer
        .as_ref()
        .map(|setup| GpuGKRTraceGeometry {
            log_domain_size: setup.trace_holder.log_domain_size,
            log_lde_factor: setup.trace_holder.log_lde_factor,
            log_rows_per_leaf: setup.trace_holder.log_rows_per_leaf,
            log_tree_cap_size: setup.trace_holder.log_tree_cap_size,
        })
        .unwrap_or(GpuGKRTraceGeometry {
            log_domain_size: compiled_circuit.trace_len.trailing_zeros(),
            log_lde_factor: whir_schedule.base_lde_factor.trailing_zeros(),
            log_rows_per_leaf: whir_schedule.whir_steps_schedule[0] as u32,
            log_tree_cap_size: whir_schedule.cap_size.trailing_zeros(),
        });
    let mut stage1_output = GpuGKRStage1Output::generate(
        circuit_type,
        &compiled_circuit,
        setup_geometry,
        setup_transfer
            .as_ref()
            .filter(|transfer| transfer.host.columns_count > 0)
            .map(|transfer| transfer.trace_holder.get_hypercube_evals()),
        decoder_transfer
            .as_ref()
            .map(|transfer| &transfer.data_device[..]),
        inits_and_teardowns_transfer
            .as_ref()
            .map(|transfer| &transfer.data_device),
        &tracing_data_transfer.data_device,
        context,
    )?;
    if let Some(decoder_transfer) = decoder_transfer {
        callbacks.extend(decoder_transfer.into_host_keepalive());
    }
    if let Some(inits_and_teardowns_transfer) = inits_and_teardowns_transfer {
        callbacks.extend(inits_and_teardowns_transfer.into_host_keepalive());
    }
    callbacks.extend(tracing_data_transfer.into_host_keepalive());
    let canonical_top_bits = canonical_inits_and_teardowns_top_bits(&compiled_circuit);
    let mut synthetic_setup_trace_holder = if setup_transfer.is_none() {
        Some(TraceHolder::new_without_cosets(
            setup_geometry.log_domain_size,
            setup_geometry.log_lde_factor,
            setup_geometry.log_rows_per_leaf,
            setup_geometry.log_tree_cap_size,
            0,
            TreesCacheMode::CachePartial,
            context,
        )?)
    } else {
        None
    };

    // Memory tree caps are provided externally — flatten eagerly for the transcript.
    let memory_log_lde_factor = stage1_output.memory_trace_holder.log_lde_factor;
    let memory_log_tree_cap_size = stage1_output.memory_trace_holder.log_tree_cap_size;
    let flattened_memory_tree_caps = flatten_tree_caps_from_slices(
        &memory_tree_caps
            .iter()
            .map(|c| c.cap.as_slice())
            .collect::<Vec<_>>(),
        memory_log_lde_factor,
    );

    // Clone memory tree caps into pool-managed HostAllocations for the WHIR fold (via callback
    // to respect the stream-ordered allocation contract).
    let mut memory_base_caps_keepalive =
        allocate_tree_caps(memory_log_lde_factor, memory_log_tree_cap_size, context);
    let memory_cap_dst_accessors = memory_base_caps_keepalive
        .iter_mut()
        .map(|h| h.get_mut_accessor())
        .collect::<Vec<_>>();
    let memory_tree_caps_owned: Vec<Vec<Digest>> = memory_tree_caps
        .iter()
        .map(|c| c.cap.clone())
        .collect::<Vec<_>>();
    callbacks.schedule(
        move || unsafe {
            for (src, dst) in memory_tree_caps_owned
                .iter()
                .zip(memory_cap_dst_accessors.iter())
            {
                dst.get_mut().copy_from_slice(src);
            }
        },
        stream,
    )?;

    let witness_base_caps_keepalive = stage1_output.witness_trace_holder.take_tree_caps_host();
    let witness_base_caps_accessors = witness_base_caps_keepalive
        .iter()
        .map(HostAllocation::get_accessor)
        .collect::<Vec<_>>();
    let witness_log_lde_factor = stage1_output.witness_trace_holder.log_lde_factor;
    let flattened_setup_tree_caps = setup_transfer
        .as_ref()
        .map(|setup_transfer| {
            flatten_tree_caps_from_slices(
                &setup_transfer
                    .host
                    .tree_caps
                    .iter()
                    .map(|cap| &cap[..])
                    .collect::<Vec<_>>(),
                setup_transfer.host.log_lde_factor,
            )
        })
        .unwrap_or_default();

    let mut seed_host = unsafe { context.alloc_host_uninit::<Seed>() };
    let seed_accessor = seed_host.get_mut_accessor();
    let mut lookup_challenges_host = unsafe { context.alloc_host_uninit_slice(3) };
    let lookup_challenges_write_accessor = lookup_challenges_host.get_mut_accessor();
    let external_challenges_for_seed = external_challenges.clone();
    callbacks.schedule(
        move || unsafe {
            let flattened_witness_tree_caps =
                flatten_tree_caps(&witness_base_caps_accessors, witness_log_lde_factor);
            let transcript_input = build_initial_transcript_input(
                &canonical_top_bits,
                &external_challenges_for_seed,
                &flattened_setup_tree_caps,
                &flattened_memory_tree_caps,
                &flattened_witness_tree_caps,
            );
            seed_accessor.write(Transcript::commit_initial(&transcript_input));
            let challenges = draw_random_field_els::<BF, E4>(seed_accessor.get_mut(), 3);
            lookup_challenges_write_accessor
                .get_mut()
                .copy_from_slice(&challenges);
        },
        stream,
    )?;

    let mut forward_setup = if let Some(setup_transfer) = setup_transfer.as_ref() {
        setup_transfer.schedule_forward_setup(
            &compiled_circuit,
            &lookup_challenges_host,
            context,
        )?
    } else {
        schedule_forward_setup_for_shape::<E4>(
            None,
            compiled_circuit.trace_len,
            compiled_circuit.generic_lookup_tables_width,
            compiled_circuit.total_tables_size,
            compiled_circuit.tables_ids_in_generic_lookups,
            &lookup_challenges_host,
            context,
        )?
    };
    let forward_output = schedule_forward_pass(
        setup_transfer.as_ref().map(|setup| &setup.trace_holder),
        synthetic_setup_trace_holder.as_ref(),
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
    let forward_setup_keepalive = forward_setup.into_host_keepalive();

    let mut backward_shared_state = make_deferred_backward_workflow_state();
    let backward_shared_state_handle = UnsafeMutAccessor::new(backward_shared_state.as_mut());
    let lookup_challenges_read_accessor = lookup_challenges_host.get_accessor();
    callbacks.schedule(
        {
            let backward_shared_state = backward_shared_state_handle;
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
                    backward_shared_state,
                    initial_layer_for_sumcheck + 1,
                    top_layer_claims,
                    evaluation_point,
                    seed_accessor.get().clone(),
                    batching_challenge,
                    lookup_challenges[0],
                    lookup_challenges[1],
                    lookup_challenges[2],
                );
            }
        },
        stream,
    )?;
    drop(lookup_challenges_host);

    let mut backward_scheduled = backward_state
        .schedule_execute_backward_workflow_from_shared_state(
            compiled_circuit.clone(),
            external_challenges.clone(),
            backward_shared_state,
            context,
        )?;
    let backward_shared_state = backward_scheduled.shared_state_handle();
    let setup_trace_holder = setup_transfer
        .as_ref()
        .map(|setup| &setup.trace_holder)
        .unwrap_or_else(|| {
            synthetic_setup_trace_holder
                .as_ref()
                .expect("setup-less proof path must materialize a synthetic setup holder")
        });
    let mut base_layer_claims_scheduled = schedule_prepare_base_layer_claims_with_sources(
        compiled_circuit.layers[0].clone(),
        compiled_circuit.trace_len.trailing_zeros() as usize,
        {
            let backward_shared_state = backward_shared_state;
            move |dst| {
                fill_backward_claim_point_for_layer(backward_shared_state, 0, dst);
            }
        },
        {
            let backward_shared_state = backward_shared_state;
            move || clone_backward_claims_for_layer(backward_shared_state, 0)
        },
        setup_trace_holder,
        &stage1_output.memory_trace_holder,
        &stage1_output.witness_trace_holder,
        context,
    )?;
    let base_layer_claims_shared_state = base_layer_claims_scheduled.shared_state_handle();
    callbacks.schedule(
        {
            let backward_shared_state = backward_shared_state;
            let base_layer_claims_shared_state = base_layer_claims_shared_state;
            move || {
                let extra_evaluations_from_caching_relations =
                    clone_base_layer_extra_evaluations_from_caching_relations(
                        base_layer_claims_shared_state,
                    );
                let extra_evaluations_transcript_batches =
                    clone_base_layer_extra_evaluations_transcript_batches(
                        base_layer_claims_shared_state,
                    );
                apply_base_layer_extra_evaluations_to_workflow_state(
                    backward_shared_state,
                    &extra_evaluations_from_caching_relations,
                    &extra_evaluations_transcript_batches,
                );
            }
        },
        stream,
    )?;
    // Materialize deferred cosets for setup and memory right before WHIR fold queries.
    // Setup: cosets allocated on demand; partial trees already transferred from host.
    let pre_whir_setup_cosets_range = Range::new("gkr.proof.pre_whir.setup_cosets")?;
    pre_whir_setup_cosets_range.start(stream)?;
    if let Some(setup_transfer) = setup_transfer.as_mut() {
        setup_transfer
            .trace_holder
            .ensure_cosets_materialized(context)?;
    } else {
        let setup_trace_holder = synthetic_setup_trace_holder
            .as_mut()
            .expect("setup-less proof path must materialize a synthetic setup holder");
        if setup_trace_holder.columns_count > 0 {
            setup_trace_holder.commit_all(context)?;
        }
    }
    pre_whir_setup_cosets_range.end(stream)?;
    ranges.push(pre_whir_setup_cosets_range);
    // Memory: cosets allocated on demand, then build and cache partial trees from cosets.
    let pre_whir_memory_commit_range = Range::new("gkr.proof.pre_whir.memory_commit")?;
    pre_whir_memory_commit_range.start(stream)?;
    stage1_output
        .memory_trace_holder
        .ensure_cosets_materialized(context)?;
    {
        let instances_count = 1usize << stage1_output.memory_trace_holder.log_lde_factor;
        stage1_output.memory_trace_holder.trees = TreesHolder::Partial(allocate_trees(
            instances_count,
            stage1_output.memory_trace_holder.log_domain_size - PARTIAL_TREE_REDUCTION_LAYERS,
            stage1_output.memory_trace_holder.log_rows_per_leaf,
            context,
        )?);
        stage1_output
            .memory_trace_holder
            .build_and_cache_partial_trees(context)?;
    }
    pre_whir_memory_commit_range.end(stream)?;
    ranges.push(pre_whir_memory_commit_range);

    let mut whir_scheduled = if let Some(setup_transfer) = setup_transfer.as_mut() {
        let setup_base_caps_keepalive = setup_transfer.trace_holder.take_tree_caps_host();
        schedule_gpu_whir_fold_with_sources(
            &mut stage1_output.memory_trace_holder,
            memory_base_caps_keepalive,
            {
                let base_layer_claims_shared_state = base_layer_claims_shared_state;
                move |dst| fill_mem_polys_claims(base_layer_claims_shared_state, dst)
            },
            &mut stage1_output.witness_trace_holder,
            witness_base_caps_keepalive,
            {
                let base_layer_claims_shared_state = base_layer_claims_shared_state;
                move |dst| fill_wit_polys_claims(base_layer_claims_shared_state, dst)
            },
            &mut setup_transfer.trace_holder,
            setup_base_caps_keepalive,
            {
                let base_layer_claims_shared_state = base_layer_claims_shared_state;
                move |dst| fill_setup_polys_claims(base_layer_claims_shared_state, dst)
            },
            compiled_circuit.trace_len.trailing_zeros() as usize,
            {
                let backward_shared_state = backward_shared_state;
                move |dst| {
                    fill_backward_claim_point_for_layer(backward_shared_state, 0, dst);
                }
            },
            whir_schedule.base_lde_factor,
            {
                let backward_shared_state = backward_shared_state;
                move || {
                    let mut seed = current_backward_seed(backward_shared_state);
                    draw_random_field_els::<BF, E4>(&mut seed, 1)[0]
                }
            },
            whir_schedule.whir_steps_schedule.clone(),
            whir_schedule.whir_queries_schedule.clone(),
            whir_schedule.whir_steps_lde_factors.clone(),
            whir_schedule.whir_pow_schedule.clone(),
            {
                let backward_shared_state = backward_shared_state;
                move || {
                    let mut seed = current_backward_seed(backward_shared_state);
                    let _whir_batching_challenge = draw_random_field_els::<BF, E4>(&mut seed, 1);
                    seed
                }
            },
            whir_schedule.cap_size,
            compiled_circuit.trace_len.trailing_zeros() as usize,
            context,
        )?
    } else {
        let setup_trace_holder = synthetic_setup_trace_holder
            .as_mut()
            .expect("setup-less proof path must materialize a synthetic setup holder");
        let setup_base_caps_keepalive = if setup_trace_holder.columns_count > 0 {
            setup_trace_holder.take_tree_caps_host()
        } else {
            Vec::new()
        };
        schedule_gpu_whir_fold_with_sources(
            &mut stage1_output.memory_trace_holder,
            memory_base_caps_keepalive,
            {
                let base_layer_claims_shared_state = base_layer_claims_shared_state;
                move |dst| fill_mem_polys_claims(base_layer_claims_shared_state, dst)
            },
            &mut stage1_output.witness_trace_holder,
            witness_base_caps_keepalive,
            {
                let base_layer_claims_shared_state = base_layer_claims_shared_state;
                move |dst| fill_wit_polys_claims(base_layer_claims_shared_state, dst)
            },
            setup_trace_holder,
            setup_base_caps_keepalive,
            {
                let base_layer_claims_shared_state = base_layer_claims_shared_state;
                move |dst| fill_setup_polys_claims(base_layer_claims_shared_state, dst)
            },
            compiled_circuit.trace_len.trailing_zeros() as usize,
            {
                let backward_shared_state = backward_shared_state;
                move |dst| {
                    fill_backward_claim_point_for_layer(backward_shared_state, 0, dst);
                }
            },
            whir_schedule.base_lde_factor,
            {
                let backward_shared_state = backward_shared_state;
                move || {
                    let mut seed = current_backward_seed(backward_shared_state);
                    draw_random_field_els::<BF, E4>(&mut seed, 1)[0]
                }
            },
            whir_schedule.whir_steps_schedule.clone(),
            whir_schedule.whir_queries_schedule.clone(),
            whir_schedule.whir_steps_lde_factors.clone(),
            whir_schedule.whir_pow_schedule.clone(),
            {
                let backward_shared_state = backward_shared_state;
                move || {
                    let mut seed = current_backward_seed(backward_shared_state);
                    let _whir_batching_challenge = draw_random_field_els::<BF, E4>(&mut seed, 1);
                    seed
                }
            },
            whir_schedule.cap_size,
            compiled_circuit.trace_len.trailing_zeros() as usize,
            context,
        )?
    };
    let whir_shared_state = whir_scheduled.shared_state_handle();

    let backward_keepalive = backward_scheduled.into_host_keepalive();
    let setup_keepalive = setup_transfer.map(GpuGKRSetupTransfer::into_host_keepalive);

    callbacks.schedule(
        {
            let proof_slot = proof_handle;
            let backward_shared_state = backward_shared_state;
            let whir_shared_state = whir_shared_state;
            let external_challenges = external_challenges.clone();
            move || {
                let final_explicit_evaluations = collect_explicit_evaluations_from_accessors(
                    &transcript_handoff_accessors_for_final,
                );
                let backward_execution =
                    take_backward_execution_from_shared_state(backward_shared_state);
                let whir_proof = take_scheduled_whir_proof(whir_shared_state);
                let grand_product_accumulator_computed =
                    grand_product_accumulator_from_explicit_evaluations(
                        &final_explicit_evaluations,
                    );
                unsafe { proof_slot.get_mut() }.replace(GKRProof {
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
    drop(transcript_handoff);

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
            _stage1: stage1_output.into_keepalive(),
            _setup: setup_keepalive,
            _forward_setup: forward_setup_keepalive,
            _backward: backward_keepalive,
            _base_layer_claims: base_layer_claims_scheduled,
            _whir: whir_scheduled,
        },
    })
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn prove_with_transfer_scheduling<'a, A: GoodAllocator + 'a>(
    circuit_type: CircuitType,
    compiled_circuit: GKRCircuitArtifact<BF>,
    external_challenges: GKRExternalChallenges<BF, E4>,
    whir_schedule: WhirSchedule,
    final_trace_size_log_2: usize,
    mut setup_transfer: Option<GpuGKRSetupTransfer<'a>>,
    mut decoder_transfer: Option<DecoderTableTransfer<'a>>,
    mut inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a, A>>,
    mut tracing_data_transfer: TracingDataTransfer<'a, A>,
    memory_tree_caps: &[MerkleTreeCapVarLength],
    context: &ProverContext,
) -> CudaResult<GpuGKRProofJob<'a>> {
    let h2d_stream = context.get_h2d_stream();
    let transfer_range = Range::new("gkr.proof.h2d_transfers")?;
    transfer_range.start(h2d_stream)?;
    if let Some(setup_transfer) = setup_transfer.as_mut() {
        setup_transfer.schedule_transfer(context)?;
    }
    if let Some(decoder_transfer) = decoder_transfer.as_mut() {
        decoder_transfer.schedule_transfer(context)?;
    }
    if let Some(inits_and_teardowns_transfer) = inits_and_teardowns_transfer.as_mut() {
        inits_and_teardowns_transfer.schedule_transfer(context)?;
    }
    tracing_data_transfer.schedule_transfer(context)?;
    transfer_range.end(h2d_stream)?;

    let mut proof_job = prove(
        circuit_type,
        compiled_circuit,
        external_challenges,
        whir_schedule,
        final_trace_size_log_2,
        setup_transfer,
        decoder_transfer,
        inits_and_teardowns_transfer,
        tracing_data_transfer,
        memory_tree_caps,
        context,
    )?;
    proof_job.ranges.insert(0, transfer_range);
    Ok(proof_job)
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
    use super::{build_initial_transcript_input, draw_query_bits_with_external_nonce};
    use crate::primitives::field::{BF, E4};
    use prover::definitions::Transcript;
    use prover::gkr::prover::transcript_utils::draw_query_bits;
    use prover::gkr::prover::GKRExternalChallenges;
    use prover::query_utils::assemble_query_index;
    use prover::transcript::Seed;
    use worker::Worker;

    #[test]
    fn external_nonce_query_bits_match_cpu_draw_query_bits() {
        let worker = Worker::new();
        let cases = [
            (Seed([1, 2, 3, 4, 5, 6, 7, 8]), 23usize, 22usize, 24u32),
            (
                Seed([11, 12, 13, 14, 15, 16, 17, 18]),
                12usize,
                21usize,
                24u32,
            ),
            (
                Seed([21, 22, 23, 24, 25, 26, 27, 28]),
                10usize,
                18usize,
                16u32,
            ),
            (
                Seed([31, 32, 33, 34, 35, 36, 37, 38]),
                10usize,
                14usize,
                0u32,
            ),
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

    #[test]
    fn initial_transcript_input_matches_cpu_order_with_and_without_setup_caps() {
        let external_challenges = GKRExternalChallenges {
            permutation_argument_linearization_challenges: std::array::from_fn(|idx| {
                E4::from_array_of_base([
                    BF::new(10 + idx as u32),
                    BF::new(20 + idx as u32),
                    BF::new(30 + idx as u32),
                    BF::new(40 + idx as u32),
                ])
            }),
            permutation_argument_additive_part: E4::from_array_of_base([
                BF::new(1),
                BF::new(2),
                BF::new(3),
                BF::new(4),
            ]),
            _marker: std::marker::PhantomData,
        };
        let canonical_top_bits = vec![0u32, 1, 2, 3];
        let setup_caps = vec![11u32, 12, 13, 14];
        let memory_caps = vec![21u32, 22, 23, 24];
        let witness_caps = vec![31u32, 32, 33, 34];

        let with_setup = build_initial_transcript_input(
            &canonical_top_bits,
            &external_challenges,
            &setup_caps,
            &memory_caps,
            &witness_caps,
        );
        let without_setup = build_initial_transcript_input(
            &canonical_top_bits,
            &external_challenges,
            &[],
            &memory_caps,
            &witness_caps,
        );

        let mut expected_with_setup = canonical_top_bits.clone();
        external_challenges.flatten_into_buffer(&mut expected_with_setup);
        expected_with_setup.extend_from_slice(&setup_caps);
        expected_with_setup.extend_from_slice(&memory_caps);
        expected_with_setup.extend_from_slice(&witness_caps);
        assert_eq!(with_setup, expected_with_setup);

        let mut expected_without_setup = canonical_top_bits.clone();
        external_challenges.flatten_into_buffer(&mut expected_without_setup);
        expected_without_setup.extend_from_slice(&memory_caps);
        expected_without_setup.extend_from_slice(&witness_caps);
        assert_eq!(without_setup, expected_without_setup);

        let with_setup_seed = Transcript::commit_initial(&with_setup);
        let mut expected_with_setup_seed = canonical_top_bits.clone();
        external_challenges.flatten_into_buffer(&mut expected_with_setup_seed);
        expected_with_setup_seed.extend_from_slice(&setup_caps);
        expected_with_setup_seed.extend_from_slice(&memory_caps);
        expected_with_setup_seed.extend_from_slice(&witness_caps);
        assert_eq!(
            with_setup_seed,
            Transcript::commit_initial(&expected_with_setup_seed)
        );

        let without_setup_seed = Transcript::commit_initial(&without_setup);
        let mut expected_without_setup_seed = canonical_top_bits;
        external_challenges.flatten_into_buffer(&mut expected_without_setup_seed);
        expected_without_setup_seed.extend_from_slice(&memory_caps);
        expected_without_setup_seed.extend_from_slice(&witness_caps);
        assert_eq!(
            without_setup_seed,
            Transcript::commit_initial(&expected_without_setup_seed)
        );
    }
}
