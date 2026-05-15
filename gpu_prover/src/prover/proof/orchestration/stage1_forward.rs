use std::sync::Arc;

use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::STATE_SIZE;
use crate::primitives::callbacks::Callbacks;
use crate::primitives::circuit_type::CircuitType;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::setup::{
    schedule_forward_setup_for_shape, GpuGKRForwardSetup, GpuGKRSetupTransfer,
};
use crate::prover::gkr::stage1::{GpuGKRStage1Output, GpuGKRTraceGeometry};
use crate::prover::proof::layout::{
    build_proof_layout_inputs, ProofLayout, ProofLayoutBaseLayerGeometry,
};
use crate::prover::trace::decoder::DecoderTableTransfer;
use crate::prover::trace::holder::{TraceHolder, TreesCacheMode};
use crate::prover::trace::memory_transfer::GpuGKRMemoryTransfer;
use crate::prover::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::upstream::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES;
use crate::upstream::{GKRCircuitArtifact, GKRExternalChallenges, ProverConfig, WhirSchedule};

use super::canonical_inits_and_teardowns_top_bits;

pub(in crate::prover::proof) struct Stage1AndForwardPreparation {
    pub(in crate::prover::proof) stage1_output: GpuGKRStage1Output,
    pub(in crate::prover::proof) synthetic_setup_trace_holder: Option<TraceHolder<BF>>,
    pub(in crate::prover::proof) proof_layout: ProofLayout,
    pub(in crate::prover::proof) proof_slab: Option<Arc<DeviceAllocation<E4>>>,
    pub(in crate::prover::proof) forward_setup: GpuGKRForwardSetup<E4>,
    pub(in crate::prover::proof) d_seed: DeviceAllocation<u32>,
    pub(in crate::prover::proof) d_external_challenges_e4: DeviceAllocation<E4>,
    pub(in crate::prover::proof) canonical_top_bits_host: HostAllocation<[u32]>,
    pub(in crate::prover::proof) external_challenges_host: HostAllocation<[E4]>,
}

#[allow(clippy::too_many_arguments)]
pub(in crate::prover::proof) fn prepare_stage1_and_forward_setup<'a, A: GoodAllocator + 'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: usize,
    whir_schedule: &WhirSchedule,
    setup_transfer: &Option<GpuGKRSetupTransfer<'a>>,
    decoder_transfer: Option<DecoderTableTransfer<'a>>,
    inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a>>,
    tracing_data_transfer: Option<TracingDataTransfer<'a, A>>,
    memory_transfer: &GpuGKRMemoryTransfer<'a>,
    callbacks: &mut Callbacks<'a>,
    context: &ProverContext,
) -> CudaResult<Stage1AndForwardPreparation> {
    let stream = context.get_exec_stream();
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
            // No setup transfer means the setup precomputation step was
            // skipped (zero-column setup, e.g. InitsAndTeardowns). Match the
            // geometry that `commit_memory_inner` and `memory_transfer` use
            // for this circuit — both read from `prover_config`, so stage1's
            // memory/witness trace holders end up with the same cap size as
            // the pre-built memory caps we'll D2D into them.
            log_lde_factor: prover_config.lde_factor.trailing_zeros(),
            log_rows_per_leaf: prover_config.base_oracles_values_per_leaf.trailing_zeros(),
            log_tree_cap_size: prover_config.cap_size.trailing_zeros(),
        });

    let canonical_top_bits = canonical_inits_and_teardowns_top_bits(compiled_circuit);
    let canonical_top_bits_len = canonical_top_bits.len();
    let external_challenges_u32_len = (NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES + 1) * 4;
    debug_assert_eq!(
        memory_transfer.host.log_lde_factor, setup_geometry.log_lde_factor,
        "memory transfer log_lde_factor must match setup geometry",
    );
    let memory_caps_total_u32 =
        (1usize << memory_transfer.host.log_tree_cap_size) * BLAKE2S_DIGEST_SIZE_U32_WORDS;
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
        stream,
    )?;
    if canonical_top_bits_len > 0 {
        memory_copy_async(
            &mut d_canonical_top_bits[..canonical_top_bits_len],
            &canonical_top_bits_host,
            stream,
        )?;
    }
    memory_copy_async(
        &mut d_external_challenges_e4,
        &external_challenges_host,
        stream,
    )?;

    let stage1_output = GpuGKRStage1Output::generate(
        circuit_type,
        compiled_circuit,
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
        tracing_data_transfer
            .as_ref()
            .map(|transfer| &transfer.data_device),
        context,
    )?;
    if let Some(decoder_transfer) = decoder_transfer {
        callbacks.extend(decoder_transfer.into_host_keepalive());
    }
    if let Some(inits_and_teardowns_transfer) = inits_and_teardowns_transfer {
        callbacks.extend(inits_and_teardowns_transfer.into_host_keepalive());
    }
    if let Some(tracing_data_transfer) = tracing_data_transfer {
        callbacks.extend(tracing_data_transfer.into_host_keepalive());
    }
    let synthetic_setup_trace_holder = if setup_transfer.is_none() {
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
    let proof_layout_inputs = build_proof_layout_inputs::<E4>(
        compiled_circuit,
        external_challenges,
        whir_schedule,
        final_trace_size_log_2,
        ProofLayoutBaseLayerGeometry::from_geometry(
            memory_layer_geometry,
            compiled_circuit.memory_layout.total_width,
        ),
        ProofLayoutBaseLayerGeometry::from_geometry(
            witness_layer_geometry,
            compiled_circuit.witness_layout.total_width,
        ),
        ProofLayoutBaseLayerGeometry::from_geometry(
            setup_geometry,
            proof_layout_setup_columns_count,
        ),
    );
    let proof_layout = ProofLayout::new(&proof_layout_inputs);
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
    drop(d_canonical_top_bits);

    let mut d_lookup_challenges: DeviceAllocation<E4> =
        context.alloc(2, AllocationPlacement::BestFit)?;
    crate::ops::blake2s::transcript_squeeze_e4(&mut d_seed, &mut d_lookup_challenges, stream)?;

    let forward_setup = if let Some(setup_transfer) = setup_transfer.as_ref() {
        setup_transfer.schedule_forward_setup(compiled_circuit, d_lookup_challenges, context)?
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

    Ok(Stage1AndForwardPreparation {
        stage1_output,
        synthetic_setup_trace_holder,
        proof_layout,
        proof_slab,
        forward_setup,
        d_seed,
        d_external_challenges_e4,
        canonical_top_bits_host,
        external_challenges_host,
    })
}
