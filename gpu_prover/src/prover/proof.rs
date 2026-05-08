use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
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
use crate::ops::blake2s::STATE_SIZE;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{
    DeviceAllocation, HostAllocation, ProverContext, SchedulerHostAllocation, UnsafeAccessor,
    UnsafeMutAccessor,
};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::prover::decoder::DecoderTableTransfer;
use crate::prover::gkr::backward::{
    current_backward_seed, make_deferred_backward_workflow_state, ClaimBufferLayout,
    GpuGKRBackwardHostKeepalive,
};
use crate::prover::gkr::backward_kernels::{
    eq_group_tables_len, launch_build_eq_values_from_point,
};
use crate::prover::gkr::base_layer_claims::{
    clone_base_layer_extra_evaluations_from_slab, schedule_prepare_base_layer_claims_with_sources,
    GpuGKRBaseLayerClaimsScheduledExecution,
};
use crate::prover::gkr::forward::{schedule_forward_pass, ForwardOutputSlabTarget};
use crate::prover::gkr::setup::{
    schedule_forward_setup_for_shape, GpuGKRForwardSetupHostKeepalive, GpuGKRSetupTransfer,
    GpuGKRSetupTransferHostKeepalive,
};
use crate::prover::gkr::stage1::{GpuGKRStage1Keepalive, GpuGKRStage1Output, GpuGKRTraceGeometry};
use crate::prover::memory_transfer::{GpuGKRMemoryTransfer, GpuGKRMemoryTransferHostKeepalive};
use crate::prover::trace_holder::{
    allocate_trees, TraceHolder, TreesCacheMode, TreesHolder, PARTIAL_TREE_REDUCTION_LAYERS,
};
use crate::prover::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::prover::whir_fold::{
    schedule_gpu_whir_fold_with_sources, take_scheduled_whir_proof, GpuWhirFoldScheduledExecution,
};

struct GpuGKRProofJobKeepalive<'a> {
    _stage1: GpuGKRStage1Keepalive,
    _setup: Option<GpuGKRSetupTransferHostKeepalive<'a>>,
    _memory: GpuGKRMemoryTransferHostKeepalive<'a>,
    _forward_setup: GpuGKRForwardSetupHostKeepalive<E4>,
    _backward: GpuGKRBackwardHostKeepalive<BF, E4>,
    _base_layer_claims: GpuGKRBaseLayerClaimsScheduledExecution<E4>,
    _whir: GpuWhirFoldScheduledExecution,
    /// Pinned host staging buffer backing the h2d_stream H2D that uploads the
    /// canonical top-bits prefix into the device-resident
    /// `d_canonical_top_bits` source consumed by `transcript_commit_initial_chunked`.
    _initial_transcript_canonical_top_bits_host: HostAllocation<[u32]>,
    /// Pinned host staging buffer and durable device buffer for the seven
    /// external challenges. The device buffer is the source of truth for both
    /// the transcript input span and GKR flat immediate evaluation.
    _external_challenges_host: HostAllocation<[E4]>,
    _external_challenges_device: DeviceAllocation<E4>,
    /// Pinned host mirror of the device-resident proof slab (Phase 4). Populated
    /// by the terminal D2H; read by the single assembly callback.
    #[allow(dead_code)]
    _proof_host_mirror: Option<HostAllocation<[u8]>>,
    /// Proof slab itself — held here so it outlives all scheduled writes and
    /// the terminal D2H.
    #[allow(dead_code)]
    _proof_slab: Option<Arc<DeviceAllocation<E4>>>,
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
    inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a>>,
    mut tracing_data_transfer: TracingDataTransfer<'a, A>,
    memory_transfer: GpuGKRMemoryTransfer<'a>,
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
    // Memory cap H2D was scheduled pre-prove on h2d_stream; the D2D into the
    // transcript input slot below needs the H2D to be visible on exec_stream.
    memory_transfer.ensure_transferred(context)?;

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
    //  1. h2d_stream: upload canonical_top_bits into `d_transcript_input` and
    //     external_challenges into a durable aligned 7-E4 device buffer. This is
    //     scheduled *before* stage 1 is queued on exec_stream, so `e_alloc`
    //     captures an empty exec_stream position and h2d_stream can run
    //     concurrently with stage 1 GPU compute.
    //  2. exec_stream: assemble the full flat transcript input `d_transcript_input`
    //     (canonical_top_bits ++ external_challenges ++ setup_caps ++ memory_caps ++ witness_caps)
    //     as contiguous device u32s after stage 1 finishes. Setup and witness caps are D2D-copied
    //     from their on-device tree buffers in bit-reversed LDE position order.
    //  3. `transcript_commit_initial(d_seed, d_transcript_input)` → `Blake2s(full_input)` from
    //     the IV in a single kernel launch (no D2D, no per-prefix `transcript_commit`).
    //     Matches CPU `Transcript::commit_initial`.
    //  4. `transcript_squeeze(d_seed, d_lookup_challenges)` → 3 lookup challenges on device.
    //  5. D2H seed and lookup-challenges into existing host pinned slots for downstream
    //     host-side callbacks (backward workflow state population reads them back).
    // ---------------------------------------------------------------------

    // Sizes that are known at prove() entry (no stage1 output needed).
    let canonical_top_bits = canonical_inits_and_teardowns_top_bits(&compiled_circuit);
    let canonical_top_bits_len = canonical_top_bits.len();
    let external_challenges_u32_len = (NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1) * 4;
    debug_assert_eq!(
        memory_transfer.host.log_lde_factor, setup_geometry.log_lde_factor,
        "memory transfer log_lde_factor must match setup geometry",
    );
    let memory_caps_total_u32 =
        (1usize << memory_transfer.host.log_tree_cap_size) * BLAKE2S_DIGEST_SIZE_U32_WORDS;
    // Setup and witness caps share `setup_geometry.log_tree_cap_size` (stage1 builds
    // both holders from `setup_geometry`, see stage1.rs:185-194), so the cap-bytes
    // total is `(1 << log_tree_cap_size) * BLAKE2S_DIGEST_SIZE_U32_WORDS` per layer.
    // Setup caps are 0 when the setup transfer is absent (synthetic-setup path).
    let setup_caps_total_u32 = if setup_transfer.is_some() {
        (1usize << setup_geometry.log_tree_cap_size) * BLAKE2S_DIGEST_SIZE_U32_WORDS
    } else {
        0
    };
    let witness_caps_total_u32 =
        (1usize << setup_geometry.log_tree_cap_size) * BLAKE2S_DIGEST_SIZE_U32_WORDS;
    let total_transcript_len = canonical_top_bits_len
        + external_challenges_u32_len
        + setup_caps_total_u32
        + memory_caps_total_u32
        + witness_caps_total_u32;
    assert!(
        total_transcript_len > 0,
        "transcript input must be non-empty for commit_initial",
    );

    // -------------- Step 1: h2d_stream pack of the small device-side sources for the chunked commit --------------
    // The transcript-input concat is now performed inside the
    // `transcript_commit_initial_chunked` kernel directly over the existing
    // device-resident sources (external_challenges + per-holder unified caps).
    // The only host-origin words still needed on device are canonical_top_bits
    // (a tiny prefix) and the external-challenges buffer — both H2D'd here on
    // h2d_stream behind an `e_alloc` fence so packing runs concurrently with
    // stage 1 compute on exec_stream.
    let h2d_stream = context.get_h2d_stream();
    let mut d_canonical_top_bits: DeviceAllocation<u32> =
        context.alloc(canonical_top_bits_len.max(1), AllocationPlacement::BestFit)?;
    let mut canonical_top_bits_host =
        unsafe { context.alloc_host_uninit_slice::<u32>(canonical_top_bits_len.max(1)) };
    let canonical_top_bits_host_write_accessor = canonical_top_bits_host.get_mut_accessor();
    let mut external_challenges_host = unsafe {
        context.alloc_host_uninit_slice::<E4>(NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1)
    };
    let external_challenges_host_write_accessor = external_challenges_host.get_mut_accessor();
    let external_challenges_for_h2d = external_challenges.clone();
    let mut d_external_challenges_e4: DeviceAllocation<E4> = context.alloc(
        NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1,
        AllocationPlacement::BestFit,
    )?;

    let e_alloc = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    e_alloc.record(stream)?;
    h2d_stream.wait_event(&e_alloc, CudaStreamWaitEventFlags::DEFAULT)?;

    callbacks.schedule(
        move || unsafe {
            canonical_top_bits_host_write_accessor.get_mut()[..canonical_top_bits_len]
                .copy_from_slice(&canonical_top_bits);
            let dst = external_challenges_host_write_accessor.get_mut();
            dst[..NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES].copy_from_slice(
                &external_challenges_for_h2d.permutation_argument_linearization_challenges,
            );
            dst[NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES] =
                external_challenges_for_h2d.permutation_argument_additive_part;
        },
        h2d_stream,
    )?;
    if canonical_top_bits_len > 0 {
        memory_copy_async(
            &mut d_canonical_top_bits[..canonical_top_bits_len],
            &canonical_top_bits_host,
            h2d_stream,
        )?;
    }
    memory_copy_async(
        &mut d_external_challenges_e4,
        &external_challenges_host,
        h2d_stream,
    )?;

    // `e_xfer` records "pre-prove H2D complete". The exec-stream wait on it is
    // deferred until just before the chunked transcript-commit kernel reads
    // canonical_top_bits + external_challenges, so stage 1 compute isn't
    // artificially serialized behind these tiny copies.
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
        stage1_output.memory_trace_holder.log_lde_factor, memory_transfer.host.log_lde_factor,
        "memory trace holder LDE factor must match the memory transfer geometry",
    );

    debug_assert_eq!(
        stage1_output.witness_trace_holder.unified_device_cap().len()
            * BLAKE2S_DIGEST_SIZE_U32_WORDS,
        witness_caps_total_u32,
        "stage1 witness unified cap size must match the structurally-derived witness_caps_total_u32",
    );

    // Build the proof slab layout structurally (no forward output required) and
    // allocate the slab now — placing it before forward keeps it at a stable,
    // bottom-of-pool offset across the whole prove() invocation. Per-layer
    // backward kernels and base-layer claim writes target slab offsets
    // computed from this layout. After forward returns we re-derive the layout
    // from `forward_output.dimension_reducing_inputs` + the storage-aware
    // address collection and assert equivalence in debug builds.
    let proof_layout_setup_columns_count = setup_transfer
        .as_ref()
        .map_or(0, |s| s.trace_holder.columns_count);
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
    let proof_layout_inputs_structural =
        crate::prover::proof_layout::build_proof_layout_inputs_structural::<E4>(
            &compiled_circuit,
            &external_challenges,
            &whir_schedule,
            final_trace_size_log_2,
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
    let proof_layout =
        crate::prover::proof_layout::ProofLayout::new(&proof_layout_inputs_structural);
    let proof_slab: Option<Arc<DeviceAllocation<E4>>> = if proof_layout.total_bytes > 0 {
        assert_eq!(
            proof_layout.total_bytes % std::mem::size_of::<E4>(),
            0,
            "proof slab size must be E4-aligned",
        );
        let slab = context.alloc_with_extra_alignment::<E4, 4>(
            proof_layout.total_bytes / std::mem::size_of::<E4>(),
            AllocationPlacement::Bottom,
        )?;
        debug_assert_eq!(
            slab.as_ptr() as usize & 0xF,
            0,
            "proof slab base pointer must be 16-byte aligned for ProofLayout typed casts",
        );
        Some(Arc::new(slab))
    } else {
        None
    };

    // Exec must not read the h2d-populated canonical_top_bits / external_challenges
    // until the h2d_stream H2D has completed. Placing the wait here (after stage 1
    // is queued) means stage 1 and the H2D pack run concurrently; the wait only
    // fences the chunked transcript-commit kernel below.
    stream.wait_event(&e_xfer, CudaStreamWaitEventFlags::DEFAULT)?;

    // -------------- Step 2: device-side chunked commit_initial --------------
    // `commit_initial(canonical_top_bits || external_challenges || setup_cap ||
    // memory_cap || witness_cap)` = Blake2s(concat) from the IV, evaluated by a
    // single chunked kernel launch over the existing device-resident sources.
    // No `d_transcript_input` allocation and no per-source D2D into a contiguous
    // pack are needed — the kernel streams the chunks directly. Source lifetimes:
    //   - canonical_top_bits: `_initial_transcript_canonical_top_bits_host` keepalive.
    //   - external_challenges: `_external_challenges_device` keepalive.
    //   - setup unified cap: `setup_transfer` keepalive (pre-prove H2D, fenced by
    //     `setup_transfer.ensure_transferred` at the top of `prove()`).
    //   - memory unified cap: `memory_transfer` keepalive (pre-prove H2D, fenced
    //     by `memory_transfer.ensure_transferred` at the top of `prove()`).
    //   - witness unified cap: `stage1_output.witness_trace_holder` keepalive
    //     (assembled in stage 1 on exec_stream — same stream as the kernel below).
    let mut chunks: Vec<(*const u32, u32)> = Vec::with_capacity(5);
    if canonical_top_bits_len > 0 {
        chunks.push((d_canonical_top_bits.as_ptr(), canonical_top_bits_len as u32));
    }
    {
        let external_u32 = unsafe { d_external_challenges_e4.transmute::<u32>() };
        debug_assert_eq!(external_u32.len(), external_challenges_u32_len);
        chunks.push((external_u32.as_ptr(), external_challenges_u32_len as u32));
    }
    if setup_caps_total_u32 > 0 {
        let setup_transfer_ref = setup_transfer
            .as_ref()
            .expect("setup_caps_total_u32 > 0 requires a setup transfer");
        let src_u32 = unsafe { setup_transfer_ref.unified_device_cap().transmute::<u32>() };
        debug_assert_eq!(src_u32.len(), setup_caps_total_u32);
        chunks.push((src_u32.as_ptr(), setup_caps_total_u32 as u32));
    }
    {
        let src_u32 = unsafe { memory_transfer.unified_device_cap().transmute::<u32>() };
        debug_assert_eq!(src_u32.len(), memory_caps_total_u32);
        chunks.push((src_u32.as_ptr(), memory_caps_total_u32 as u32));
    }
    {
        let src_u32 = unsafe {
            stage1_output
                .witness_trace_holder
                .unified_device_cap()
                .transmute::<u32>()
        };
        debug_assert_eq!(src_u32.len(), witness_caps_total_u32);
        chunks.push((src_u32.as_ptr(), witness_caps_total_u32 as u32));
    }
    let mut d_seed: DeviceAllocation<u32> =
        context.alloc(STATE_SIZE, AllocationPlacement::BestFit)?;
    crate::ops::blake2s::transcript_commit_initial_chunked(&mut d_seed, &chunks, stream)?;
    // Chunks have all been scheduled into the kernel; raw pointers are pinned
    // at scheduling time. Drop the canonical-top-bits device buffer now (its
    // pool free is exec-stream-ordered after the kernel) — every other source
    // is held by an outer keepalive.
    drop(d_canonical_top_bits);

    // 2 E4 lookup challenges in Montgomery form, drawn via the device-side Fiat-Shamir path
    // (mirrors host `draw_random_field_els::<BF, E4>(seed, 2)` with `from_raw_repr_with_reduction`).
    // The same buffer feeds forward (consumed by `schedule_forward_setup`) and backward
    // (extracted via `into_host_keepalive_taking_lookup_challenges` after forward) — no
    // separate `d_lookup_challenges_for_backward` allocation or D2D (Opp. 3).
    let mut d_lookup_challenges: DeviceAllocation<E4> =
        context.alloc(2, AllocationPlacement::BestFit)?;
    crate::ops::blake2s::transcript_squeeze_e4(&mut d_seed, &mut d_lookup_challenges, stream)?;

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
    let output_evaluations_slab = proof_slab.as_ref().and_then(|slab| {
        let (ptr, len) =
            unsafe { proof_layout.output_evaluations_device_mut(slab.as_ptr() as *mut u8) }?;
        assert_eq!(
            ptr,
            slab.as_ptr() as *mut E4,
            "output_evaluations must be the proof slab prefix for direct forward writes",
        );
        Some(ForwardOutputSlabTarget {
            backing: Arc::clone(slab),
            len,
        })
    });
    let forward_output = schedule_forward_pass(
        setup_transfer.as_ref().map(|setup| &setup.trace_holder),
        synthetic_setup_trace_holder.as_ref(),
        &mut stage1_output,
        &mut forward_setup,
        &compiled_circuit,
        &external_challenges,
        final_trace_size_log_2,
        output_evaluations_slab,
        context,
    )?;
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

    // Regression-guard: re-derive the layout from `forward_output` and assert it
    // matches the structurally-derived layout we already used to size the slab.
    // The structural derivation must match every dim-reducing layer's IO map
    // and every main-layer's input address set; if it diverges, the slab is
    // improperly sized and writes overflow.
    #[cfg(debug_assertions)]
    {
        let main_layer_input_addresses_per_layer_storage_aware =
            crate::prover::gkr::backward::collect_main_layer_input_addresses_per_layer::<E4>(
                &compiled_circuit,
                &external_challenges,
                &forward_output.storage,
            );
        let proof_layout_inputs_storage_aware =
            crate::prover::proof_layout::build_proof_layout_inputs(
                &compiled_circuit,
                &whir_schedule,
                final_trace_size_log_2,
                &forward_output.dimension_reducing_inputs,
                &main_layer_input_addresses_per_layer_storage_aware,
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
        let proof_layout_storage_aware =
            crate::prover::proof_layout::ProofLayout::new(&proof_layout_inputs_storage_aware);
        debug_assert_eq!(
            proof_layout.total_bytes, proof_layout_storage_aware.total_bytes,
            "structural and storage-aware proof layouts disagree on total_bytes",
        );
    }

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
    // `derive_dimension_reducing_inputs_structural` in the *same* iteration
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
        crate::ops::gkr_initial_inner_products::initial_inner_product_e4(
            device_flat_evaluations.as_ptr(),
            num_top_claims,
            &eq_values_for_init,
            poly_len as u32,
            &mut initial_d_claims,
            stream,
        )?;
    };

    // No host mirror of the initial claims / evaluation_point / batching / seed / lookup
    // challenges is needed on the hot path: backward consumes them as device buffers, and
    // post-backward overwrites the layer-0 host fields that downstream base-layer / WHIR
    // setup reads. `backward_shared_state` is created empty and populated by the
    // post-backward handoff for layer 0.
    let backward_shared_state = make_deferred_backward_workflow_state();
    post_forward_handoff_range.end(stream)?;
    ranges.push(post_forward_handoff_range);

    let mut backward_scheduled = backward_state
        .schedule_execute_backward_workflow_from_shared_state(
            compiled_circuit.clone(),
            external_challenges.clone(),
            d_external_challenges_e4.as_ptr(),
            backward_shared_state,
            d_seed,
            d_evaluation_point_and_batching,
            initial_d_claims,
            top_layer_claim_layout,
            d_lookup_challenges_for_backward,
            false,
            proof_slab.as_deref(),
            &proof_layout,
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
    let final_claim_addresses = backward_scheduled.final_claim_addresses().to_vec();
    let (final_device_seed, final_device_claim_point) =
        backward_scheduled.final_device_seed_and_claim_point_mut();
    let mut base_layer_claims_scheduled = schedule_prepare_base_layer_claims_with_sources(
        compiled_circuit.layers[0].clone(),
        final_device_claim_point,
        // Layer-1 incoming claim addresses are schedule-time-known (the
        // `ClaimBufferLayout` built when backward staged its final claims),
        // so the base-layer extras plan is built at schedule time without
        // waiting for the backward post-handoff callback to materialize a
        // host BTreeMap.
        &final_claim_addresses,
        setup_trace_holder,
        &stage1_output.memory_trace_holder,
        &stage1_output.witness_trace_holder,
        proof_slab.as_deref(),
        &proof_layout,
        Some(final_device_seed),
        context,
    )?;
    let base_layer_claims_shared_state = base_layer_claims_scheduled.shared_state_handle();
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

    let post_backward_handoff_range = Range::new("gkr.proof.post_backward_handoff")?;
    post_backward_handoff_range.start(stream)?;
    let post_backward_callbacks = backward_scheduled.schedule_post_backward_handoff(context)?;
    post_backward_handoff_range.end(stream)?;
    ranges.push(post_backward_handoff_range);
    callbacks.extend(post_backward_callbacks);

    let mut whir_scheduled = {
        let setup_trace_holder = if let Some(setup_transfer) = setup_transfer.as_mut() {
            &mut setup_transfer.trace_holder
        } else {
            synthetic_setup_trace_holder
                .as_mut()
                .expect("setup-less proof path must materialize a synthetic setup holder")
        };
        schedule_gpu_whir_fold_with_sources(
            &mut stage1_output.memory_trace_holder,
            memory_transfer.unified_device_cap(),
            &mut stage1_output.witness_trace_holder,
            setup_trace_holder,
            backward_scheduled.final_device_claim_point(),
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
            true, // use_hypercube_evals_for_batching
            proof_slab.as_deref(),
            &proof_layout,
            Some(base_layer_claims_scheduled.take_pending_aggregation()),
            context,
        )?
    };
    let whir_shared_state = whir_scheduled.shared_state_handle();

    let backward_keepalive = backward_scheduled.into_host_keepalive();
    let setup_keepalive = setup_transfer.map(GpuGKRSetupTransfer::into_host_keepalive);
    let memory_keepalive = memory_transfer.into_host_keepalive();

    // Terminal D2H of the whole proof slab into a pinned host mirror, scheduled
    // after all slab-write work above. The mirror drives the single host-side
    // parse that replaces per-piece host bookkeeping.
    let slab = proof_slab
        .as_ref()
        .expect("proof slab must be allocated for prove()");
    let mut mirror = unsafe { context.alloc_host_uninit_slice::<u8>(proof_layout.total_bytes) };
    let slab_u8 = unsafe {
        era_cudart::slice::DeviceSlice::from_raw_parts(
            slab.as_ptr() as *const u8,
            proof_layout.total_bytes,
        )
    };
    memory_copy_async(
        unsafe { mirror.get_mut_accessor().get_mut() },
        slab_u8,
        stream,
    )?;
    let proof_host_mirror_accessor = mirror.get_accessor();
    let proof_host_mirror = Some(mirror);
    callbacks.schedule(
        {
            let proof_slot = proof_handle;
            let whir_shared_state = whir_shared_state;
            let base_layer_claims_shared_state_for_final = base_layer_claims_shared_state;
            let external_challenges = external_challenges.clone();
            let proof_layout_for_parse = proof_layout.clone();
            move || {
                // Phase 4: source all device-produced proof fields from the
                // terminal-D2H'd slab — including `final_explicit_evaluations`,
                // which final forward dim-reduction wrote directly into the
                // slab's `output_evaluations` block.
                let slab_bytes = unsafe { proof_host_mirror_accessor.get() };
                let final_explicit_evaluations =
                    proof_layout_for_parse.parse_final_explicit_evaluations(slab_bytes);
                let mut extra_by_layer = BTreeMap::new();
                let base_layer_idx = 0usize;
                let extra = clone_base_layer_extra_evaluations_from_slab(
                    base_layer_claims_shared_state_for_final,
                    &proof_layout_for_parse,
                    slab_bytes,
                );
                if !extra.is_empty() {
                    extra_by_layer.insert(base_layer_idx, extra);
                }
                let sumcheck_intermediate_values = proof_layout_for_parse
                    .parse_sumcheck_intermediate_values(slab_bytes, extra_by_layer);
                let mut whir_proof = proof_layout_for_parse.parse_whir_proof(slab_bytes);
                let host_whir_proof = take_scheduled_whir_proof(whir_shared_state);
                whir_proof.setup_commitment.queries = host_whir_proof.setup_commitment.queries;
                whir_proof.memory_commitment.queries = host_whir_proof.memory_commitment.queries;
                whir_proof.witness_commitment.queries = host_whir_proof.witness_commitment.queries;
                whir_proof.final_monomials = host_whir_proof.final_monomials;
                whir_proof.intermediate_whir_oracles = host_whir_proof.intermediate_whir_oracles;
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
            _memory: memory_keepalive,
            _forward_setup: forward_setup_keepalive,
            _backward: backward_keepalive,
            _base_layer_claims: base_layer_claims_scheduled,
            _whir: whir_scheduled,
            _initial_transcript_canonical_top_bits_host: canonical_top_bits_host,
            _external_challenges_host: external_challenges_host,
            _external_challenges_device: d_external_challenges_e4,
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
    mut inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a>>,
    mut tracing_data_transfer: TracingDataTransfer<'a, A>,
    mut memory_transfer: GpuGKRMemoryTransfer<'a>,
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
    memory_transfer.schedule_transfer(context)?;
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
        memory_transfer,
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
