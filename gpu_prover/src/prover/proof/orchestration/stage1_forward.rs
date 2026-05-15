use std::sync::Arc;

use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use era_cudart::result::CudaResult;
use fft::GoodAllocator;

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::STATE_SIZE;
use crate::primitives::circuit_type::CircuitType;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::setup::{
    schedule_forward_setup_for_shape, GpuGKRForwardSetup, GpuGKRSetupTransfer,
};
use crate::prover::gkr::stage1::{GpuGKRStage1Output, GpuGKRTraceGeometry};
use crate::prover::proof::inputs::EXTERNAL_CHALLENGES_E4_LEN;
use crate::prover::proof::layout::{
    build_proof_layout_inputs, ProofLayout, ProofLayoutBaseLayerGeometry,
};
use crate::prover::trace::decoder::DecoderTableTransfer;
use crate::prover::trace::holder::{TraceHolder, TreesCacheMode};
use crate::prover::trace::memory_transfer::GpuGKRMemoryTransfer;
use crate::prover::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};
use crate::upstream::{GKRCircuitArtifact, GKRExternalChallenges, ProverConfig, WhirSchedule};

pub(in crate::prover::proof) struct Stage1AndForwardPreparation {
    pub(in crate::prover::proof) stage1_output: GpuGKRStage1Output,
    pub(in crate::prover::proof) synthetic_setup_trace_holder: Option<TraceHolder<BF>>,
    pub(in crate::prover::proof) proof_layout: ProofLayout,
    pub(in crate::prover::proof) proof_slab: Option<Arc<DeviceAllocation<E4>>>,
    pub(in crate::prover::proof) forward_setup: GpuGKRForwardSetup<E4>,
    pub(in crate::prover::proof) d_seed: DeviceAllocation<u32>,
}

/// Pre-prepared device buffers that this function consumes via references
/// (their owning wrappers live in the bundle keepalive for the proof job's
/// lifetime).
pub(in crate::prover::proof) struct BundleDeviceRefs<'b, 'a> {
    pub setup: Option<&'b GpuGKRSetupTransfer<'a>>,
    pub decoder: Option<&'b DecoderTableTransfer<'a>>,
    pub inits_and_teardowns: Option<&'b InitsAndTeardownsTransfer<'a>>,
    pub memory: &'b GpuGKRMemoryTransfer<'a>,
    pub canonical_top_bits_device: Option<&'b DeviceAllocation<u32>>,
    pub external_challenges_device: &'b DeviceAllocation<E4>,
}

#[allow(clippy::too_many_arguments)]
pub(in crate::prover::proof) fn prepare_stage1_and_forward_setup<'a, A: GoodAllocator + 'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E4>,
    prover_config: &ProverConfig,
    final_trace_size_log_2: usize,
    whir_schedule: &WhirSchedule,
    bundle: BundleDeviceRefs<'_, 'a>,
    tracing_data_transfer: Option<&TracingDataTransfer<'a, A>>,
    context: &ProverContext,
) -> CudaResult<Stage1AndForwardPreparation> {
    let stream = context.get_exec_stream();
    let setup_geometry = bundle
        .setup
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

    let canonical_top_bits_len = bundle
        .canonical_top_bits_device
        .map(|d| d.len())
        .unwrap_or(0);
    let external_challenges_u32_len = EXTERNAL_CHALLENGES_E4_LEN * 4;
    debug_assert_eq!(
        bundle.memory.host.log_lde_factor, setup_geometry.log_lde_factor,
        "memory transfer log_lde_factor must match setup geometry",
    );
    let memory_caps_total_u32 =
        (1usize << bundle.memory.host.log_tree_cap_size) * BLAKE2S_DIGEST_SIZE_U32_WORDS;
    let setup_caps_total_u32 = if bundle.setup.is_some() {
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

    let stage1_output = GpuGKRStage1Output::generate(
        circuit_type,
        compiled_circuit,
        setup_geometry,
        bundle
            .setup
            .filter(|transfer| transfer.host.columns_count > 0)
            .map(|transfer| transfer.trace_holder.get_hypercube_evals()),
        bundle.decoder.map(|transfer| &transfer.data_device[..]),
        bundle
            .inits_and_teardowns
            .map(|transfer| &transfer.data_device),
        tracing_data_transfer.map(|transfer| &transfer.data_device),
        context,
    )?;
    let synthetic_setup_trace_holder = if bundle.setup.is_none() {
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
        stage1_output.memory_trace_holder.log_lde_factor, bundle.memory.host.log_lde_factor,
        "memory trace holder LDE factor must match the memory transfer geometry",
    );
    debug_assert_eq!(
        stage1_output.witness_trace_holder.unified_device_cap().len()
            * BLAKE2S_DIGEST_SIZE_U32_WORDS,
        witness_caps_total_u32,
        "stage1 witness unified cap size must match the structurally-derived witness_caps_total_u32",
    );

    let proof_layout_setup_columns_count = bundle.setup.map_or(0, |s| s.trace_holder.columns_count);
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
    if let Some(d_canonical_top_bits) = bundle.canonical_top_bits_device {
        chunks.push((d_canonical_top_bits.as_ptr(), canonical_top_bits_len as u32));
    }
    {
        let external_u32 = unsafe { bundle.external_challenges_device.transmute::<u32>() };
        debug_assert_eq!(external_u32.len(), external_challenges_u32_len);
        chunks.push((external_u32.as_ptr(), external_challenges_u32_len as u32));
    }
    if setup_caps_total_u32 > 0 {
        let setup_transfer_ref = bundle
            .setup
            .expect("setup_caps_total_u32 > 0 requires a setup transfer");
        let src_u32 = unsafe { setup_transfer_ref.unified_device_cap().transmute::<u32>() };
        debug_assert_eq!(src_u32.len(), setup_caps_total_u32);
        chunks.push((src_u32.as_ptr(), setup_caps_total_u32 as u32));
    }
    {
        let src_u32 = unsafe { bundle.memory.unified_device_cap().transmute::<u32>() };
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

    let mut d_lookup_challenges: DeviceAllocation<E4> =
        context.alloc(2, AllocationPlacement::BestFit)?;
    crate::ops::blake2s::transcript_squeeze_e4(&mut d_seed, &mut d_lookup_challenges, stream)?;

    let forward_setup = if let Some(setup_transfer) = bundle.setup {
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
    })
}
