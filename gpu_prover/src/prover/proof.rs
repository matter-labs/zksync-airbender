use std::collections::{BTreeMap, BTreeSet};

use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use cs::definitions::GKRAddress;
use cs::definitions::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES;
use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStreamWaitEventFlags;
use fft::GoodAllocator;
use field::Field;
use prover::definitions::Transcript;
use prover::gkr::prover::transcript_utils::draw_random_field_els;
use prover::gkr::prover::{GKRExternalChallenges, GKRProof, WhirSchedule};
use prover::merkle_trees::DefaultTreeConstructor;
use prover::query_utils::BitSource;
use prover::transcript::Seed;

use crate::allocator::tracker::AllocationPlacement;
use crate::circuit_type::CircuitType;
use crate::ops::blake2s::Digest;
use crate::ops::blake2s::STATE_SIZE;
use crate::ops::cub::device_reduce::{
    get_reduce_temp_storage_bytes, reduce, ReduceOperation,
};
use crate::ops::cub::CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2;
use crate::ops::simple::mul;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{
    DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor, UnsafeMutAccessor,
};
use crate::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::decoder::DecoderTableTransfer;
use crate::prover::gkr::backward::{
    apply_base_layer_extra_evaluations_to_workflow_state, clone_backward_claims_for_layer,
    current_backward_seed, fill_backward_claim_point_for_layer,
    make_deferred_backward_workflow_state, populate_backward_workflow_state,
    take_backward_execution_from_shared_state, ClaimBufferLayout, GpuGKRBackwardHostKeepalive,
};
use crate::prover::gkr::backward_kernels::{eq_group_tables_len, launch_build_eq_values_from_point};
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
    allocate_trees, TraceHolder, TreesCacheMode, TreesHolder, PARTIAL_TREE_REDUCTION_LAYERS,
};
// TODO(init-teardown-port): re-add `InitsAndTeardownsTransfer,` once restored.
use crate::prover::tracing_data::TracingDataTransfer;
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
    /// Pinned host staging buffer that backs the single h2d_stream H2D used to upload
    /// canonical_top_bits ++ external_challenges ++ flattened_memory_caps for the initial
    /// transcript. Held here so the allocation outlives the H2D copy on h2d_stream.
    _initial_transcript_host_blob: HostAllocation<[u32]>,
    /// Pinned host mirror of the device-resident proof slab (Phase 4). Populated
    /// by the terminal D2H; read by the single assembly callback.
    #[allow(dead_code)]
    _proof_host_mirror: Option<HostAllocation<[u8]>>,
    /// Proof slab itself — held here so it outlives all scheduled writes and
    /// the terminal D2H.
    #[allow(dead_code)]
    _proof_slab: Option<DeviceAllocation<u8>>,
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

pub(crate) fn top_layer_claim_layout(
    output_layer_for_sumcheck: &BTreeMap<
        OutputType,
        prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput,
    >,
) -> ClaimBufferLayout {
    let mut addresses = BTreeSet::new();
    let permutation_output = &output_layer_for_sumcheck[&OutputType::PermutationProduct];
    addresses.insert(permutation_output.output[0]);
    addresses.insert(permutation_output.output[1]);
    if let Some(output) = output_layer_for_sumcheck.get(&OutputType::Lookup16Bits) {
        addresses.insert(output.output[0]);
        addresses.insert(output.output[1]);
    }
    if let Some(output) = output_layer_for_sumcheck.get(&OutputType::LookupTimestamps) {
        addresses.insert(output.output[0]);
        addresses.insert(output.output[1]);
    }
    if let Some(output) = output_layer_for_sumcheck.get(&OutputType::GenericLookup) {
        addresses.insert(output.output[0]);
        addresses.insert(output.output[1]);
    }
    ClaimBufferLayout::from_addresses(addresses.into_iter().collect())
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
    // TODO(init-teardown-port): restore once path is re-enabled.
    // inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a, A>>,
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
    // TODO(init-teardown-port): re-enable alongside the parameter.
    // if let Some(inits_and_teardowns_transfer) = inits_and_teardowns_transfer.as_ref() {
    //     inits_and_teardowns_transfer
    //         .transfer
    //         .ensure_transferred(context)?;
    // }
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

    // ---------------------------------------------------------------------
    // Initial Fiat-Shamir transcript: moved off exec_stream entirely.
    //
    // Pipeline:
    //  1. h2d_stream: pack canonical_top_bits ++ external_challenges ++ flattened memory caps
    //     into one pinned HostAllocation, then one H2D into `d_bucket2`. This is scheduled
    //     *before* stage 1 is queued on exec_stream, so `e_alloc` captures an empty exec_stream
    //     position and h2d_stream can run concurrently with stage 1 GPU compute.
    //  2. exec_stream: assemble the full flat transcript input `d_transcript_input`
    //     (canonical_top_bits ++ external_challenges ++ setup_caps ++ memory_caps ++ witness_caps)
    //     as contiguous device u32s after stage 1 finishes. Setup and witness caps are D2D-copied
    //     from their on-device tree buffers in bit-reversed LDE position order.
    //  3. Apply the "seed trick": carve the first STATE_SIZE u32 words of `d_transcript_input`
    //     as a `d_seed` then `transcript_commit(d_seed, rest)`. This computes a single
    //     `Blake2s(full_input)` which matches CPU `Transcript::commit_initial`.
    //  4. `transcript_squeeze(d_seed, d_lookup_challenges)` → 3 lookup challenges on device.
    //  5. D2H seed and lookup-challenges into existing host pinned slots for downstream
    //     host-side callbacks (backward workflow state population reads them back).
    // ---------------------------------------------------------------------

    // Sizes that are known at prove() entry (no stage1 output needed).
    let canonical_top_bits = canonical_inits_and_teardowns_top_bits(&compiled_circuit);
    let canonical_top_bits_len = canonical_top_bits.len();
    let external_challenges_u32_len = (NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1) * 4;
    let memory_caps_total_u32 = memory_tree_caps
        .iter()
        .map(|c| c.cap.len() * BLAKE2S_DIGEST_SIZE_U32_WORDS)
        .sum::<usize>();
    let memory_log_lde_factor = setup_geometry.log_lde_factor;
    let pre_setup_len = canonical_top_bits_len + external_challenges_u32_len;
    let bucket2_len = pre_setup_len + memory_caps_total_u32;

    // -------------- Step 1: h2d_stream consolidation (BEFORE stage 1) --------------
    // Pack canonical_top_bits ++ external_challenges ++ flattened_memory_caps into one pinned
    // HostAllocation, then a single H2D into `d_bucket2`. Scheduling this before stage 1's
    // kernels are queued on exec_stream keeps `e_alloc`'s captured stream position empty, so
    // h2d_stream's wait on it is effectively a no-op and packing + H2D run concurrently with
    // stage 1 compute on the GPU. Two-fence pattern per `docs/gpu_scheduling_contract.md#h2d-copies`.
    let h2d_stream = context.get_h2d_stream();
    let mut bucket2_host = unsafe { context.alloc_host_uninit_slice::<u32>(bucket2_len) };
    let bucket2_host_write_accessor = bucket2_host.get_mut_accessor();
    let mut d_bucket2: DeviceAllocation<u32> =
        context.alloc(bucket2_len, AllocationPlacement::BestFit)?;
    let external_challenges_for_h2d = external_challenges.clone();
    let memory_tree_caps_for_h2d: Vec<Vec<Digest>> = memory_tree_caps
        .iter()
        .map(|c| c.cap.clone())
        .collect::<Vec<_>>();

    let e_alloc = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    e_alloc.record(stream)?;
    h2d_stream.wait_event(&e_alloc, CudaStreamWaitEventFlags::DEFAULT)?;

    callbacks.schedule(
        move || unsafe {
            let dst = bucket2_host_write_accessor.get_mut();
            let mut offset = 0usize;
            dst[offset..offset + canonical_top_bits_len].copy_from_slice(&canonical_top_bits);
            offset += canonical_top_bits_len;
            let mut ext_buf: Vec<u32> = Vec::with_capacity(external_challenges_u32_len);
            external_challenges_for_h2d.flatten_into_buffer(&mut ext_buf);
            assert_eq!(ext_buf.len(), external_challenges_u32_len);
            dst[offset..offset + external_challenges_u32_len].copy_from_slice(&ext_buf);
            offset += external_challenges_u32_len;
            // memory caps in bit-reversed LDE position order, matching CPU flatten_tree_caps.
            let lde_factor = 1usize << memory_log_lde_factor;
            for stage1_pos in 0..lde_factor {
                let natural_coset_index =
                    stage1_pos.reverse_bits() >> (usize::BITS - memory_log_lde_factor);
                for digest in memory_tree_caps_for_h2d[natural_coset_index].iter() {
                    dst[offset..offset + BLAKE2S_DIGEST_SIZE_U32_WORDS].copy_from_slice(digest);
                    offset += BLAKE2S_DIGEST_SIZE_U32_WORDS;
                }
            }
            assert_eq!(offset, bucket2_len);
        },
        h2d_stream,
    )?;
    memory_copy_async(&mut d_bucket2, &bucket2_host, h2d_stream)?;

    // `e_xfer` records "h2d H2D complete". The exec-stream wait on it is deferred until just
    // before the first D2D that reads `d_bucket2` (after stage 1), so stage 1 compute isn't
    // artificially serialized behind the transfer.
    let e_xfer = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    e_xfer.record(h2d_stream)?;

    // -------------- Stage 1 on exec_stream (runs concurrently with h2d_stream packing+H2D) --------------
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
        // TODO(init-teardown-port): restore `inits_and_teardowns_transfer.as_ref().map(...)` arg.
        &tracing_data_transfer.data_device,
        context,
    )?;
    if let Some(decoder_transfer) = decoder_transfer {
        callbacks.extend(decoder_transfer.into_host_keepalive());
    }
    // TODO(init-teardown-port): re-enable alongside the parameter.
    // if let Some(inits_and_teardowns_transfer) = inits_and_teardowns_transfer {
    //     callbacks.extend(inits_and_teardowns_transfer.into_host_keepalive());
    // }
    callbacks.extend(tracing_data_transfer.into_host_keepalive());
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
    debug_assert_eq!(
        stage1_output.memory_trace_holder.log_lde_factor, memory_log_lde_factor,
        "memory trace holder LDE factor must match setup geometry used for the h2d pack",
    );

    // Memory tree caps come from the caller as plain heap Vecs. Keep a WHIR-side copy
    // (plain Vec<Vec<Digest>>) — no pool-managed HostAllocation and no exec-stream callback.
    let memory_tree_caps_owned_for_whir: Vec<Vec<Digest>> = memory_tree_caps
        .iter()
        .map(|c| c.cap.clone())
        .collect::<Vec<_>>();

    let witness_log_lde_factor = stage1_output.witness_trace_holder.log_lde_factor;
    let witness_base_caps_keepalive = stage1_output.witness_trace_holder.take_tree_caps_host();

    // Sizes that depend on stage1 output (witness tree caps).
    let setup_caps_total_u32 = setup_transfer
        .as_ref()
        .map(|setup_transfer| {
            setup_transfer
                .host
                .tree_caps
                .iter()
                .map(|cap| cap.len() * BLAKE2S_DIGEST_SIZE_U32_WORDS)
                .sum::<usize>()
        })
        .unwrap_or(0);
    let witness_caps_total_u32 = witness_base_caps_keepalive
        .iter()
        .map(|cap| unsafe { cap.get_accessor().get().len() } * BLAKE2S_DIGEST_SIZE_U32_WORDS)
        .sum::<usize>();

    let total_transcript_len =
        pre_setup_len + setup_caps_total_u32 + memory_caps_total_u32 + witness_caps_total_u32;

    // Offsets inside `d_transcript_input`.
    let offset_pre_setup = 0usize;
    let offset_setup = offset_pre_setup + pre_setup_len;
    let offset_memory = offset_setup + setup_caps_total_u32;
    let offset_witness = offset_memory + memory_caps_total_u32;
    debug_assert_eq!(
        offset_witness + witness_caps_total_u32,
        total_transcript_len
    );
    assert!(
        total_transcript_len >= STATE_SIZE,
        "transcript input must have at least STATE_SIZE words for the commit_initial seed trick",
    );

    // Exec must not read `d_bucket2` until the h2d_stream H2D has completed. Placing the wait
    // here (after stage 1 is queued) means stage 1 and the h2d transfer run concurrently; the
    // wait is only effective at the D2D copies below.
    stream.wait_event(&e_xfer, CudaStreamWaitEventFlags::DEFAULT)?;

    // -------------- Step 2: materialize d_transcript_input on exec_stream --------------
    let mut d_transcript_input: DeviceAllocation<u32> =
        context.alloc(total_transcript_len, AllocationPlacement::BestFit)?;

    // D2D: pre_setup_len words from d_bucket2[0..pre_setup_len] → d_transcript_input[0..]
    memory_copy_async(
        &mut d_transcript_input[offset_pre_setup..offset_pre_setup + pre_setup_len],
        &d_bucket2[0..pre_setup_len],
        stream,
    )?;
    // D2D: memory caps from d_bucket2[pre_setup_len..bucket2_len] → d_transcript_input[offset_memory..]
    memory_copy_async(
        &mut d_transcript_input[offset_memory..offset_memory + memory_caps_total_u32],
        &d_bucket2[pre_setup_len..bucket2_len],
        stream,
    )?;
    // D2D: setup caps from the on-device trace_holder trees.
    if setup_caps_total_u32 > 0 {
        let setup_transfer_ref = setup_transfer
            .as_ref()
            .expect("setup_caps_total_u32 > 0 requires a setup transfer");
        let setup_log_lde_factor = setup_transfer_ref.host.log_lde_factor;
        let setup_log_tree_cap_size = setup_transfer_ref.host.log_tree_cap_size;
        let log_subtree_cap_size = setup_log_tree_cap_size - setup_log_lde_factor;
        let lde_factor = 1usize << setup_log_lde_factor;
        let trees = match &setup_transfer_ref.trace_holder.trees {
            crate::prover::trace_holder::TreesHolder::Partial(trees)
            | crate::prover::trace_holder::TreesHolder::Full(trees) => trees,
            crate::prover::trace_holder::TreesHolder::None => {
                panic!("setup trace holder must cache trees for transcript cap extraction")
            }
        };
        let mut running_offset = offset_setup;
        for stage1_pos in 0..lde_factor {
            let natural_coset_index =
                stage1_pos.reverse_bits() >> (usize::BITS - setup_log_lde_factor);
            let cap_digests = crate::ops::blake2s::merkle_tree_cap(
                &trees[natural_coset_index][..],
                log_subtree_cap_size,
            );
            let cap_u32_len = cap_digests.len() * BLAKE2S_DIGEST_SIZE_U32_WORDS;
            // SAFETY: Digest is [u32; STATE_SIZE] — same layout as contiguous u32 array of
            // `cap_digests.len() * STATE_SIZE` words.
            let cap_u32 = unsafe { cap_digests.transmute::<u32>() };
            memory_copy_async(
                &mut d_transcript_input[running_offset..running_offset + cap_u32_len],
                cap_u32,
                stream,
            )?;
            running_offset += cap_u32_len;
        }
        debug_assert_eq!(running_offset, offset_setup + setup_caps_total_u32);
    }
    // D2D: witness caps from the stage1 witness_trace_holder trees, in bit-reversed order.
    if witness_caps_total_u32 > 0 {
        let witness_log_tree_cap_size = stage1_output.witness_trace_holder.log_tree_cap_size;
        let log_subtree_cap_size = witness_log_tree_cap_size - witness_log_lde_factor;
        let lde_factor = 1usize << witness_log_lde_factor;
        let trees = match &stage1_output.witness_trace_holder.trees {
            crate::prover::trace_holder::TreesHolder::Partial(trees)
            | crate::prover::trace_holder::TreesHolder::Full(trees) => trees,
            crate::prover::trace_holder::TreesHolder::None => {
                panic!("witness trace holder must cache trees for transcript cap extraction")
            }
        };
        let mut running_offset = offset_witness;
        for stage1_pos in 0..lde_factor {
            let natural_coset_index =
                stage1_pos.reverse_bits() >> (usize::BITS - witness_log_lde_factor);
            let cap_digests = crate::ops::blake2s::merkle_tree_cap(
                &trees[natural_coset_index][..],
                log_subtree_cap_size,
            );
            let cap_u32_len = cap_digests.len() * BLAKE2S_DIGEST_SIZE_U32_WORDS;
            let cap_u32 = unsafe { cap_digests.transmute::<u32>() };
            memory_copy_async(
                &mut d_transcript_input[running_offset..running_offset + cap_u32_len],
                cap_u32,
                stream,
            )?;
            running_offset += cap_u32_len;
        }
        debug_assert_eq!(running_offset, offset_witness + witness_caps_total_u32);
    }

    // -------------- Step 3: device-side commit_initial + draw 3 lookup challenges --------------
    // Seed trick: d_seed := d_transcript_input[0..STATE_SIZE], then commit the remainder.
    // That produces Blake2s(full_input), matching CPU `Transcript::commit_initial`.
    let mut d_seed: DeviceAllocation<u32> =
        context.alloc(STATE_SIZE, AllocationPlacement::BestFit)?;
    memory_copy_async(&mut d_seed, &d_transcript_input[0..STATE_SIZE], stream)?;
    crate::ops::blake2s::transcript_commit(
        &mut d_seed,
        &d_transcript_input[STATE_SIZE..total_transcript_len],
        stream,
    )?;

    // 2 E4 lookup challenges in Montgomery form, drawn via the device-side Fiat-Shamir path
    // (mirrors host `draw_random_field_els::<BF, E4>(seed, 2)` with `from_raw_repr_with_reduction`).
    let mut d_lookup_challenges: DeviceAllocation<E4> =
        context.alloc(2, AllocationPlacement::BestFit)?;
    crate::ops::blake2s::transcript_squeeze_e4(&mut d_seed, &mut d_lookup_challenges, stream)?;

    // D2H the 2 lookup challenges onto `d2h_stream` via a fork/join pair: exec records
    // `src_lookup_ready` after the squeeze; d2h waits, then copies. The local join
    // `d2h_lookup_done` is awaited on exec_stream before `forward_setup.into_host_keepalive()`
    // drops `d_lookup_challenges`, satisfying the fork/join/drop rule in
    // `docs/gpu_scheduling_contract.md`.
    let mut lookup_challenges_host = unsafe { context.alloc_host_uninit_slice::<E4>(2) };
    let src_lookup_ready = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    src_lookup_ready.record(stream)?;
    let d2h_stream = context.get_d2h_stream();
    d2h_stream.wait_event(&src_lookup_ready, CudaStreamWaitEventFlags::DEFAULT)?;
    memory_copy_async(&mut lookup_challenges_host, &d_lookup_challenges, d2h_stream)?;
    let d2h_lookup_done = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    d2h_lookup_done.record(d2h_stream)?;

    // `d_bucket2` and `d_transcript_input` can be dropped: exec_stream has queued all reads.
    drop(d_bucket2);
    drop(d_transcript_input);

    let mut forward_setup = if let Some(setup_transfer) = setup_transfer.as_ref() {
        setup_transfer.schedule_forward_setup(&compiled_circuit, d_lookup_challenges, context)?
    } else {
        schedule_forward_setup_for_shape::<E4>(
            None,
            compiled_circuit.trace_len,
            compiled_circuit.generic_lookup_tables_width,
            compiled_circuit.total_tables_size,
            compiled_circuit.tables_ids_in_generic_lookups,
            d_lookup_challenges,
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
    let transcript_handoff_accessors_for_final = transcript_handoff.explicit_evaluation_accessors();
    let initial_layer_for_sumcheck = forward_output.initial_layer_for_sumcheck;
    let output_layer_for_sumcheck =
        forward_output.dimension_reducing_inputs[&initial_layer_for_sumcheck].clone();

    // Device-resident proof image: allocate one `DeviceAllocation<u8>` sized by
    // `ProofLayout`. Phases 2b/3/4 rewire per-layer and WHIR kernel writes into
    // slab offsets via `ProofLayout` accessors; Phase 4 adds the single terminal
    // D2H + host-side parse.
    //
    // Allocation happens here because `build_proof_layout_inputs` reads
    // `forward_output.dimension_reducing_inputs` to populate per-layer
    // `final_step_eval_addresses`, and that field is still borrowable until
    // `.into_dimension_reducing_backward_state()` consumes `forward_output`
    // below. All base-layer Merkle geometry is available: memory + witness
    // share `setup_geometry` (stage1.rs:181-194); setup columns come from
    // `setup_transfer.trace_holder` or default to 0 for the
    // setup-transfer-less path (whir_fold.rs:1846 guard).
    let proof_layout_setup_columns_count = setup_transfer
        .as_ref()
        .map_or(0, |s| s.trace_holder.columns_count);
    let main_layer_input_addresses_per_layer =
        crate::prover::gkr::backward::collect_main_layer_input_addresses_per_layer::<E4>(
            &compiled_circuit,
            &external_challenges,
            &forward_output.storage,
        );
    // Per-layer geometry for the slab — witness/memory may have different
    // `log_lde_factor` / `log_tree_cap_size` than setup, so pass the actual
    // trace-holder geometry for each base layer rather than reusing
    // `setup_geometry`.
    let memory_layer_geometry = GpuGKRTraceGeometry {
        log_domain_size: stage1_output.memory_trace_holder.log_domain_size,
        log_lde_factor: stage1_output.memory_trace_holder.log_lde_factor,
        log_rows_per_leaf: stage1_output.memory_trace_holder.log_rows_per_leaf,
        log_tree_cap_size: stage1_output.memory_trace_holder.log_tree_cap_size,
    };
    let witness_layer_geometry = GpuGKRTraceGeometry {
        log_domain_size: stage1_output.witness_trace_holder.log_domain_size,
        log_lde_factor: stage1_output.witness_trace_holder.log_lde_factor,
        log_rows_per_leaf: stage1_output.witness_trace_holder.log_rows_per_leaf,
        log_tree_cap_size: stage1_output.witness_trace_holder.log_tree_cap_size,
    };
    let proof_layout_inputs = crate::prover::proof_layout::build_proof_layout_inputs(
        &compiled_circuit,
        &whir_schedule,
        final_trace_size_log_2,
        &forward_output.dimension_reducing_inputs,
        &main_layer_input_addresses_per_layer,
        crate::prover::proof_layout::ProofLayoutBaseLayerGeometry::from_geometry(
            memory_layer_geometry,
            compiled_circuit.memory_layout.total_width,
        ),
        crate::prover::proof_layout::ProofLayoutBaseLayerGeometry::from_geometry(
            witness_layer_geometry,
            compiled_circuit.witness_layout.total_width,
        ),
        crate::prover::proof_layout::ProofLayoutBaseLayerGeometry::from_geometry(
            setup_geometry,
            proof_layout_setup_columns_count,
        ),
    );
    let proof_layout = crate::prover::proof_layout::ProofLayout::new(&proof_layout_inputs);
    let proof_slab: Option<DeviceAllocation<u8>> = if proof_layout.total_bytes > 0 {
        let slab = context.alloc::<u8>(proof_layout.total_bytes, AllocationPlacement::Bottom)?;
        debug_assert_eq!(
            slab.as_ptr() as usize & 0xF,
            0,
            "proof slab base pointer must be 16-byte aligned for ProofLayout typed casts",
        );
        Some(slab)
    } else {
        None
    };

    // Phase 2b: D2D-copy per-OutputType reduced-output polynomials from the
    // packed forward-handoff flat buffer into the slab's `output_evaluations`
    // ranges. `transcript_handoff.device_flat_evaluations()` packs the polys
    // in BTreeMap iteration order of `dimension_reducing_inputs[..initial..]`
    // as `[read, write]` per OutputType (forward.rs:129-167); the slab layout
    // allocates `output_evaluations[ot] = {read_set, write_set}` in
    // BTreeMap key order of `compiled_circuit.global_output_map`, matching
    // this order exactly. Phase 4 will source `final_explicit_evaluations`
    // from the slab via the terminal D2H and retire the flat buffer.
    if let Some(slab) = proof_slab.as_ref() {
        let device_flat = transcript_handoff.device_flat_evaluations();
        let reduced_poly_len = 1usize << final_trace_size_log_2;
        let mut flat_offset = 0usize;
        for (&output_type, _) in output_layer_for_sumcheck.iter() {
            for half in 0..2usize {
                let (dst_ptr, dst_len) = unsafe {
                    if half == 0 {
                        proof_layout
                            .output_evaluations_read_device_mut(slab.as_ptr() as *mut u8, output_type)
                    } else {
                        proof_layout.output_evaluations_write_device_mut(
                            slab.as_ptr() as *mut u8,
                            output_type,
                        )
                    }
                };
                debug_assert_eq!(dst_len, reduced_poly_len);
                // SAFETY: dst_ptr is inside the live `slab` allocation at a
                // 16-byte-aligned offset, and ranges for distinct OutputTypes
                // + halves are disjoint by construction of `ProofLayout`.
                let dst = unsafe {
                    era_cudart::slice::DeviceSlice::from_raw_parts_mut(dst_ptr, dst_len)
                };
                let src =
                    &device_flat[flat_offset..flat_offset + reduced_poly_len];
                memory_copy_async(dst, src, stream)?;
                flat_offset += reduced_poly_len;
            }
        }
        debug_assert_eq!(flat_offset, device_flat.len());
    }

    // Device post-forward transcript: absorb flattened explicit evaluations into d_seed and
    // squeeze the evaluation point + batching challenge. Replaces the previous host pair
    // `commit_field_els` / `draw_random_field_els` on the host seed.
    //
    // SAFETY: `device_flat_evaluations` is a packed `DeviceAllocation<E4>` whose u32 byte
    // layout matches `commit_field_els::<BF, E4>` — E4 = 4 BF limbs, each limb stored as a
    // u32 in Montgomery form. The parity is covered by
    // `ops::blake2s::tests::transcript_squeeze_e4_parity_*`.
    let d_flat_evals_u32: &era_cudart::slice::DeviceSlice<u32> =
        unsafe { transcript_handoff.device_flat_evaluations().transmute::<u32>() };
    crate::ops::blake2s::transcript_commit(&mut d_seed, d_flat_evals_u32, stream)?;
    let num_challenges = final_trace_size_log_2 + 1;
    let mut d_evaluation_point_and_batching: DeviceAllocation<E4> =
        context.alloc(num_challenges, AllocationPlacement::BestFit)?;
    crate::ops::blake2s::transcript_squeeze_e4(
        &mut d_seed,
        &mut d_evaluation_point_and_batching,
        stream,
    )?;

    // Allocate the (evaluation_point || batching_challenge) pinned host slot; the D2H is
    // deferred to the post-forward fork/join window on d2h_stream. The device buffer itself
    // flows into the first backward layer as `initial_d_claim_point_and_batching` (claim_point
    // + batching challenge, matching the `round_scratch.claim_point` layout). The seed stays
    // on device and threads into the first backward layer as its `device_seed` — no D2H, no H2D.
    let mut evaluation_point_and_batching_host =
        unsafe { context.alloc_host_uninit_slice::<E4>(num_challenges) };

    let evaluation_point_and_batching_accessor = evaluation_point_and_batching_host.get_accessor();

    let backward_state = forward_output.into_dimension_reducing_backward_state();
    // Join before `forward_setup.into_host_keepalive()` drops `d_lookup_challenges`. The lookup
    // D2H was scheduled on `d2h_stream` above; exec_stream must wait on its completion before the
    // underlying pool block can be recycled by a subsequent exec-side alloc.
    stream.wait_event(&d2h_lookup_done, CudaStreamWaitEventFlags::DEFAULT)?;
    let forward_setup_keepalive = forward_setup.into_host_keepalive();
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
    let mut init_mul_temp: DeviceAllocation<E4> =
        context.alloc(poly_len, AllocationPlacement::Top)?;
    let init_reduce_temp_bytes =
        get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, poly_len as i32)?;
    let mut init_reduce_temp: DeviceAllocation<u8> = context
        .alloc_with_extra_alignment::<u8, CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2>(
            init_reduce_temp_bytes,
            AllocationPlacement::Top,
        )?;
    {
        let device_flat_evaluations = transcript_handoff.device_flat_evaluations();
        let mut poly_idx = 0usize;
        for (_output_type, reduced_io) in output_layer_for_sumcheck.iter() {
            for half in 0..2 {
                let address = reduced_io.output[half];
                let slot = top_layer_claim_layout.claim_idx(&address) as usize;
                let poly_chunk =
                    DeviceVectorChunk::new(device_flat_evaluations, poly_idx * poly_len, poly_len);
                let eq_chunk = DeviceVectorChunk::new(&eq_values_for_init, 0, poly_len);
                let mut temp_chunk = DeviceVectorChunkMut::new(&mut init_mul_temp, 0, poly_len);
                mul(&poly_chunk, &eq_chunk, &mut temp_chunk, stream)?;
                reduce(
                    ReduceOperation::Sum,
                    &mut init_reduce_temp,
                    &temp_chunk,
                    &mut initial_d_claims[slot],
                    stream,
                )?;
                poly_idx += 1;
            }
        }
    }

    // D2H the 8 device-computed claims and the (evaluation_point || batching_challenge) buffer
    // onto `d2h_stream`. Both sources are written on exec: `d_evaluation_point_and_batching` by
    // `transcript_squeeze_e4` above and `initial_d_claims` by the `mul`+`reduce` loop. A single
    // fork event after the last reduce covers both sources; d2h issues the two D2Hs in sequence.
    // The join (`d2h_setup_done`) is awaited on exec_stream before the consumer callback below.
    let mut initial_claims_host: HostAllocation<[E4]> =
        unsafe { context.alloc_host_uninit_slice::<E4>(num_top_claims) };
    let src_post_forward_ready =
        CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    src_post_forward_ready.record(stream)?;
    let d2h_stream = context.get_d2h_stream();
    d2h_stream.wait_event(&src_post_forward_ready, CudaStreamWaitEventFlags::DEFAULT)?;
    memory_copy_async(
        &mut evaluation_point_and_batching_host,
        &d_evaluation_point_and_batching,
        d2h_stream,
    )?;
    memory_copy_async(&mut initial_claims_host, &initial_d_claims, d2h_stream)?;
    let d2h_setup_done = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    d2h_setup_done.record(d2h_stream)?;
    let initial_claims_host_accessor = initial_claims_host.get_accessor();

    let mut backward_shared_state = make_deferred_backward_workflow_state();
    let backward_shared_state_handle = UnsafeMutAccessor::new(backward_shared_state.as_mut());
    let lookup_challenges_read_accessor = lookup_challenges_host.get_accessor();
    // Join d2h_stream back into exec_stream before the consumer callback reads the host slabs
    // and writes `backward_shared_state`. The callback stays on exec_stream (write-exclusive
    // access to shared state remains on exec).
    stream.wait_event(&d2h_setup_done, CudaStreamWaitEventFlags::DEFAULT)?;
    callbacks.schedule(
        {
            let backward_shared_state = backward_shared_state_handle;
            let top_layer_claim_layout = top_layer_claim_layout.clone();
            move || unsafe {
                let eval_point_and_batching =
                    evaluation_point_and_batching_accessor.get().to_vec();
                let (evaluation_point, batching_slice) =
                    eval_point_and_batching.split_at(num_challenges - 1);
                let evaluation_point = evaluation_point.to_vec();
                let batching_challenge = batching_slice[0];
                // Reconstruct `top_layer_claims` as a BTreeMap keyed by GKRAddress
                // using the same layout slot mapping that was used to write
                // claims into `initial_d_claims` on device.
                let claims_slice = initial_claims_host_accessor.get();
                let mut top_layer_claims = BTreeMap::new();
                for address in top_layer_claim_layout.addresses.iter().copied() {
                    let slot = top_layer_claim_layout.claim_idx(&address) as usize;
                    top_layer_claims.insert(address, claims_slice[slot]);
                }
                let lookup_challenges = lookup_challenges_read_accessor.get();
                // `workflow_state.seed` (host `Seed`) is initialized to `Seed::default()` —
                // the first backward layer's start callback reads the field but its value is
                // dead (overwritten at end-of-layer by the D2H'd advanced device seed). The
                // initial device seed is threaded separately into the first layer as
                // `initial_d_seed`.
                populate_backward_workflow_state(
                    backward_shared_state,
                    initial_layer_for_sumcheck + 1,
                    top_layer_claims,
                    evaluation_point,
                    Seed::default(),
                    batching_challenge,
                    lookup_challenges[0],
                    lookup_challenges[1],
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
            d_seed,
            d_evaluation_point_and_batching,
            initial_d_claims,
            top_layer_claim_layout,
            proof_slab.as_ref(),
            &proof_layout,
            context,
        )?;
    drop(initial_claims_host);
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
        proof_slab.as_ref(),
        &proof_layout,
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
            memory_tree_caps_owned_for_whir,
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
            proof_slab.as_ref(),
            &proof_layout,
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
            memory_tree_caps_owned_for_whir,
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
            proof_slab.as_ref(),
            &proof_layout,
            context,
        )?
    };
    let whir_shared_state = whir_scheduled.shared_state_handle();

    let backward_keepalive = backward_scheduled.into_host_keepalive();
    let setup_keepalive = setup_transfer.map(GpuGKRSetupTransfer::into_host_keepalive);

    // Phase 4a: terminal D2H of the whole proof slab into a pinned host
    // mirror, scheduled after all slab-write work above. Only when the slab
    // was actually allocated (placeholder test paths have
    // `proof_layout.total_bytes == 0` and skip). The mirror drives the
    // single host-side parse that replaces per-piece host bookkeeping.
    let proof_host_mirror: Option<HostAllocation<[u8]>> =
        if let Some(slab) = proof_slab.as_ref() {
            let mut mirror =
                unsafe { context.alloc_host_uninit_slice::<u8>(proof_layout.total_bytes) };
            memory_copy_async(
                unsafe { mirror.get_mut_accessor().get_mut() },
                slab,
                stream,
            )?;
            Some(mirror)
        } else {
            None
        };

    callbacks.schedule(
        {
            let proof_slot = proof_handle;
            let backward_shared_state = backward_shared_state;
            let whir_shared_state = whir_shared_state;
            let base_layer_claims_shared_state_for_final = base_layer_claims_shared_state;
            let external_challenges = external_challenges.clone();
            let proof_layout_for_parse = proof_layout.clone();
            let proof_host_mirror_accessor =
                proof_host_mirror.as_ref().map(|m| m.get_accessor());
            move || {
                // Phase 4b: when the slab is live, source both
                // `final_explicit_evaluations` and
                // `sumcheck_intermediate_values` from the terminal-D2H'd slab.
                // The legacy path via `transcript_handoff_accessors_for_final`
                // and `backward_shared_state.proofs` stays only for the
                // test paths that skip slab allocation.
                let (final_explicit_evaluations, sumcheck_intermediate_values) =
                    if let Some(accessor) = proof_host_mirror_accessor.as_ref() {
                        let slab_bytes = unsafe { accessor.get() };
                        let final_explicit_evaluations =
                            proof_layout_for_parse.parse_final_explicit_evaluations(slab_bytes);
                        let mut extra_by_layer = BTreeMap::new();
                        let base_layer_idx = 0usize;
                        let extra = clone_base_layer_extra_evaluations_from_caching_relations(
                            base_layer_claims_shared_state_for_final,
                        );
                        if !extra.is_empty() {
                            extra_by_layer.insert(base_layer_idx, extra);
                        }
                        let sumcheck_intermediate_values = proof_layout_for_parse
                            .parse_sumcheck_intermediate_values(slab_bytes, extra_by_layer);
                        (final_explicit_evaluations, sumcheck_intermediate_values)
                    } else {
                        let final_explicit_evaluations = collect_explicit_evaluations_from_accessors(
                            &transcript_handoff_accessors_for_final,
                        );
                        let backward_execution =
                            take_backward_execution_from_shared_state(backward_shared_state);
                        (final_explicit_evaluations, backward_execution.proofs)
                    };
                let whir_proof = take_scheduled_whir_proof(whir_shared_state);
                let grand_product_accumulator_computed =
                    grand_product_accumulator_from_explicit_evaluations(
                        &final_explicit_evaluations,
                    );
                unsafe { proof_slot.get_mut() }.replace(GKRProof {
                    external_challenges: external_challenges.clone(),
                    final_explicit_evaluations,
                    sumcheck_intermediate_values,
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
            _initial_transcript_host_blob: bucket2_host,
            _proof_host_mirror: proof_host_mirror,
            _proof_slab: proof_slab,
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
    // TODO(init-teardown-port): restore once path is re-enabled.
    // mut inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a, A>>,
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
    // TODO(init-teardown-port): re-enable alongside the parameter.
    // if let Some(inits_and_teardowns_transfer) = inits_and_teardowns_transfer.as_mut() {
    //     inits_and_teardowns_transfer.schedule_transfer(context)?;
    // }
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
        // TODO(init-teardown-port): restore `inits_and_teardowns_transfer,` arg.
        tracing_data_transfer,
        memory_tree_caps,
        context,
    )?;
    proof_job.ranges.insert(0, transfer_range);
    Ok(proof_job)
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
