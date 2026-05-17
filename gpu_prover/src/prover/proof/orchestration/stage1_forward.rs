use std::sync::Arc;

use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
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
    build_proof_layout_inputs, ProofLayout, ProofLayoutBaseLayerGeometry, WhirBaseLayerKind,
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
    pub(in crate::prover::proof) proof_slab: Arc<DeviceAllocation<E4>>,
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

    // Build proof_layout from bundle/host geometry before stage 1 runs.
    // The geometries used here come from `bundle.memory.host`, the optional
    // setup transfer, and `setup_geometry` (which is derived from
    // `prover_config` when the setup transfer is absent). Each of these is
    // structurally identical to what stage 1's trace holders will report —
    // an invariant the debug_asserts below verify after stage 1 runs.
    let proof_layout_setup_columns_count = bundle.setup.map_or(0, |s| s.trace_holder.columns_count);
    let memory_layer_geometry = GpuGKRTraceGeometry {
        log_domain_size: compiled_circuit.trace_len.trailing_zeros(),
        log_lde_factor: bundle.memory.host.log_lde_factor,
        log_rows_per_leaf: prover_config.base_oracles_values_per_leaf.trailing_zeros(),
        log_tree_cap_size: bundle.memory.host.log_tree_cap_size,
    };
    let witness_layer_geometry = setup_geometry;
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
    assert!(
        proof_layout.total_bytes > 0,
        "proof layout must have non-zero bytes",
    );
    assert_eq!(
        proof_layout.total_bytes % std::mem::size_of::<E4>(),
        0,
        "proof slab size must be E4-aligned",
    );
    let proof_slab = {
        let slab = context.alloc_with_extra_alignment::<E4, 4>(
            proof_layout.total_bytes / std::mem::size_of::<E4>(),
            AllocationPlacement::Bottom,
        )?;
        debug_assert_eq!(
            slab.as_ptr() as usize & 0xF,
            0,
            "proof slab base pointer must be 16-byte aligned for ProofLayout typed casts",
        );
        Arc::new(slab)
    };

    // Resolve slab cap destinations now that the slab is live. Stage 1 will
    // write the witness cap directly into `whir.witness.cap`; the memory and
    // setup caps land in `whir.memory.cap` / `whir.setup.cap` via the H2Ds
    // scheduled immediately below.
    let slab_base = proof_slab.as_ptr() as *mut u8;
    let (witness_cap_ptr, witness_cap_len_u32) =
        unsafe { proof_layout.whir_base_cap_device_mut(slab_base, WhirBaseLayerKind::Witness) };
    debug_assert_eq!(witness_cap_len_u32, witness_caps_total_u32);
    let (memory_cap_ptr, memory_cap_len_u32) =
        unsafe { proof_layout.whir_base_cap_device_mut(slab_base, WhirBaseLayerKind::Memory) };
    debug_assert_eq!(memory_cap_len_u32, memory_caps_total_u32);
    let (setup_cap_ptr, setup_cap_len_u32) =
        unsafe { proof_layout.whir_base_cap_device_mut(slab_base, WhirBaseLayerKind::Setup) };
    debug_assert_eq!(setup_cap_len_u32, setup_caps_total_u32);

    // Memory cap D2D: per-transfer `unified_device_cap` → slab
    // `whir.memory.cap`. The unified cap was H2D'd from pinned host on
    // `h2d_stream` pre-prove (overlapped with the prior proof's exec work,
    // outside the WHIR hot range); here we just copy it into the slab on
    // `exec_stream` — a few hundred bytes on-device, far cheaper than a
    // fresh H2D inside the hot range would be.
    {
        let src = unsafe { bundle.memory.unified_device_cap().transmute::<u32>() };
        debug_assert_eq!(src.len(), memory_cap_len_u32);
        let dst = unsafe { DeviceSlice::from_raw_parts_mut(memory_cap_ptr, memory_cap_len_u32) };
        memory_copy_async(dst, src, stream)?;
    }
    if setup_cap_len_u32 > 0 {
        let setup_transfer_ref = bundle
            .setup
            .expect("setup_caps_total_u32 > 0 requires a setup transfer");
        let src = unsafe { setup_transfer_ref.unified_device_cap().transmute::<u32>() };
        debug_assert_eq!(src.len(), setup_cap_len_u32);
        let dst = unsafe { DeviceSlice::from_raw_parts_mut(setup_cap_ptr, setup_cap_len_u32) };
        memory_copy_async(dst, src, stream)?;
    }

    // SAFETY: `witness_cap_ptr` points at the slab's `whir.witness.cap`
    // range (4-byte aligned, live for the slab's lifetime, disjoint from
    // every other slab region). Stage 1's witness commit kernel writes
    // exclusively to this range on `exec_stream`; downstream transcript
    // reads are stream-ordered after the gather.
    let mut witness_cap_dst =
        unsafe { DeviceSlice::from_raw_parts_mut(witness_cap_ptr, witness_cap_len_u32) };

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
        Some(&mut witness_cap_dst),
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
        chunks.push((setup_cap_ptr as *const u32, setup_caps_total_u32 as u32));
    }
    {
        chunks.push((memory_cap_ptr as *const u32, memory_caps_total_u32 as u32));
    }
    {
        chunks.push((witness_cap_ptr as *const u32, witness_caps_total_u32 as u32));
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
