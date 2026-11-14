use crate::proof::memory_policy::{PartialTreePolicy, WitnessMemoryPolicy, WitnessOpeningStrategy};
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::GoodAllocator;

use crate::proof::inputs::EXTERNAL_CHALLENGES_E4_LEN;
use crate::upstream::{BaseCommitmentGeometry, BaseOracleRole, ProverConfig, WhirSchedule};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::proof_layout::build_proof_layout_inputs_for_geometry;
use gpu_gkr::proof_layout::{GpuGKRTraceGeometry, ProofLayout, WhirBaseLayerKind};
use gpu_gkr::setup::{schedule_forward_setup_for_shape, GpuGKRForwardSetup, GpuGKRSetupTransfer};
use gpu_gkr::stage1::GpuGKRStage1Output;
use gpu_hash::blake2s::STATE_SIZE;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use gpu_trace::trace::memory_cap::GpuGKRMemoryCapTransfer;
use gpu_trace::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};

pub(in crate::proof) struct Stage1WitnessPreparation {
    pub(in crate::proof) stage1_output: GpuGKRStage1Output,
    pub(in crate::proof) synthetic_setup_trace_holder: Option<TraceHolder<BF>>,
    pub(in crate::proof) proof_layout: ProofLayout,
    pub(in crate::proof) proof_slab: Arc<DeviceAllocation<E4>>,
    initial_chunks: Vec<(*const u32, u32)>,
}

pub(in crate::proof) struct ForwardChallengePreparation {
    pub(in crate::proof) forward_setup: GpuGKRForwardSetup,
    pub(in crate::proof) d_seed: DeviceAllocation<u32>,
}

/// Device buffers owned by the proof job's keepalive.
pub(in crate::proof) struct BundleDeviceRefs<'b, 'a, A: GoodAllocator> {
    pub setup: Option<&'b GpuGKRSetupTransfer<'a>>,
    pub decoder: Option<&'b DecoderTableTransfer<'a>>,
    pub inits_and_teardowns: Option<&'b InitsAndTeardownsTransfer<'a, A>>,
    pub memory: &'b GpuGKRMemoryCapTransfer<'a>,
    pub top_bits_device: Option<&'b DeviceAllocation<u32>>,
    pub external_challenges_device: &'b DeviceAllocation<E4>,
}

// Only references, so copyable whatever `A` is; the derive would require `A: Copy`.
impl<A: GoodAllocator> Clone for BundleDeviceRefs<'_, '_, A> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<A: GoodAllocator> Copy for BundleDeviceRefs<'_, '_, A> {}

fn allocate_proof_slab(
    context: &ProverContext,
    total_bytes: usize,
) -> CudaResult<DeviceAllocation<E4>> {
    let slab = context.alloc_with_extra_alignment::<E4, 5>(
        total_bytes / std::mem::size_of::<E4>(),
        AllocationPlacement::Bottom,
    )?;
    assert_eq!(
        slab.as_ptr() as usize & 0x1f,
        0,
        "proof slab base pointer must be 32-byte aligned for ProofLayout typed casts",
    );
    Ok(slab)
}

pub(in crate::proof) fn prepare_witness_and_commitment<'a, A: GoodAllocator + 'a>(
    gkr_programs: &gpu_gkr::GkrPrograms,
    prover_config: &ProverConfig,
    base_geometry: BaseCommitmentGeometry,
    final_trace_size_log_2: u32,
    whir_schedule: &WhirSchedule,
    bundle: BundleDeviceRefs<'_, 'a, A>,
    tracing_data_transfer: Option<&TracingDataTransfer<'a, A>>,
    witness_policy: WitnessMemoryPolicy,
    partial_trees: PartialTreePolicy,
    context: &ProverContext,
) -> CudaResult<Stage1WitnessPreparation> {
    let circuit_type = gkr_programs.circuit_type();
    let compiled_circuit = gkr_programs.compiled_circuit().as_ref();
    let stream = context.get_exec_stream();
    bundle.memory.host.validate_for_geometry(&base_geometry);
    if let Some(setup) = bundle.setup {
        setup.host.validate_for_geometry(&base_geometry);
    }
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
            // Setup-less circuits use the same geometry as memory and witness.
            log_lde_factor: prover_config.lde_factor().trailing_zeros(),
            log_rows_per_leaf: prover_config
                .base_oracles_values_per_leaf()
                .trailing_zeros(),
            log_tree_cap_size: prover_config.cap_size.trailing_zeros(),
        });

    let top_bits_len = bundle.top_bits_device.map(|d| d.len()).unwrap_or(0);
    let external_challenges_u32_len = EXTERNAL_CHALLENGES_E4_LEN * 4;
    if let Some(setup) = bundle.setup {
        assert!(
            setup.trace_holder.columns_count > 0,
            "zero-width setup must be represented by no setup transfer"
        );
    }
    let proof_layout_inputs = build_proof_layout_inputs_for_geometry(
        gkr_programs,
        whir_schedule,
        final_trace_size_log_2,
        base_geometry,
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
        let slab = allocate_proof_slab(context, proof_layout.total_bytes)?;
        // The slab is shared only within the proof's scheduling thread.
        #[allow(clippy::arc_with_non_send_sync)]
        {
            Arc::new(slab)
        }
    };

    let slab_base = proof_slab.as_ptr() as *mut u8;
    let (witness_cap_ptr, witness_cap_len_u32) =
        unsafe { proof_layout.whir_base_cap_device_mut(slab_base, WhirBaseLayerKind::Witness) };
    let (memory_cap_ptr, memory_cap_len_u32) =
        unsafe { proof_layout.whir_base_cap_device_mut(slab_base, WhirBaseLayerKind::Memory) };
    let (setup_cap_ptr, setup_cap_len_u32) =
        unsafe { proof_layout.whir_base_cap_device_mut(slab_base, WhirBaseLayerKind::Setup) };

    if memory_cap_len_u32 > 0 {
        let src = unsafe { bundle.memory.unified_device_cap().transmute::<u32>() };
        assert_eq!(src.len(), memory_cap_len_u32);
        let dst = unsafe { DeviceSlice::from_raw_parts_mut(memory_cap_ptr, memory_cap_len_u32) };
        memory_copy_async(dst, src, stream)?;
    }
    if let Some(setup_transfer_ref) = bundle.setup {
        let src = unsafe { setup_transfer_ref.unified_device_cap().transmute::<u32>() };
        assert_eq!(src.len(), setup_cap_len_u32);
        let dst = unsafe { DeviceSlice::from_raw_parts_mut(setup_cap_ptr, setup_cap_len_u32) };
        memory_copy_async(dst, src, stream)?;
    }

    // SAFETY: the layout owns this live, disjoint u32 range in the slab.
    let mut witness_cap_dst =
        unsafe { DeviceSlice::from_raw_parts_mut(witness_cap_ptr, witness_cap_len_u32) };

    let mut stage1_output = GpuGKRStage1Output::generate_for_geometry(
        circuit_type,
        compiled_circuit,
        setup_geometry,
        base_geometry,
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
        witness_policy.commitment,
        witness_policy.post_commitment,
        partial_trees,
        context,
    )?;
    if let WitnessOpeningStrategy::Recompute(opening) = witness_policy.opening {
        stage1_output
            .witness_trace_holder
            .defer_materialization_until_queries(opening);
    }
    let synthetic_setup_trace_holder = if bundle.setup.is_none() {
        Some(TraceHolder::new_base_without_cosets(
            base_geometry,
            BaseOracleRole::Setup,
            TreesCacheMode::CacheNone,
            partial_trees.setup,
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
    if let Some(d_top_bits) = bundle.top_bits_device {
        chunks.push((d_top_bits.as_ptr(), top_bits_len as u32));
    }
    {
        let external_u32 = unsafe { bundle.external_challenges_device.transmute::<u32>() };
        debug_assert_eq!(external_u32.len(), external_challenges_u32_len);
        chunks.push((external_u32.as_ptr(), external_challenges_u32_len as u32));
    }
    // Match the CPU transcript by omitting caps for zero-width base layers.
    if setup_cap_len_u32 > 0 {
        chunks.push((setup_cap_ptr as *const u32, setup_cap_len_u32 as u32));
    }
    if memory_cap_len_u32 > 0 {
        chunks.push((memory_cap_ptr as *const u32, memory_cap_len_u32 as u32));
    }
    if witness_cap_len_u32 > 0 {
        chunks.push((witness_cap_ptr as *const u32, witness_cap_len_u32 as u32));
    }
    Ok(Stage1WitnessPreparation {
        stage1_output,
        synthetic_setup_trace_holder,
        proof_layout,
        proof_slab,
        initial_chunks: chunks,
    })
}

pub(in crate::proof) fn prepare_challenges_and_forward_setup<'a, A: GoodAllocator + 'a>(
    gkr_programs: &gpu_gkr::GkrPrograms,
    prover_config: &ProverConfig,
    bundle: BundleDeviceRefs<'_, 'a, A>,
    preparation: &Stage1WitnessPreparation,
    context: &ProverContext,
) -> CudaResult<ForwardChallengePreparation> {
    let compiled_circuit = gkr_programs.compiled_circuit().as_ref();
    let stream = context.get_exec_stream();
    let proof_layout = &preparation.proof_layout;
    let slab_base = preparation.proof_slab.as_ptr() as *mut u8;
    let chunks = &preparation.initial_chunks;
    let mut d_seed: DeviceAllocation<u32> =
        context.alloc(STATE_SIZE, AllocationPlacement::BestFit)?;
    gpu_hash::blake2s::transcript_commit_initial_chunked(&mut d_seed, chunks, stream)?;

    let mut d_lookup_challenges: DeviceAllocation<E4> =
        context.alloc(2, AllocationPlacement::BestFit)?;
    let lookup_pow_bits = crate::upstream::pow_bits::lookup_challenges_pow_bits::<BF, E4>(
        prover_config.security_level.security_bits(),
        crate::upstream::pow_bits::lookup_identity_degree(compiled_circuit),
    );
    // SAFETY: the layout owns this live, disjoint u64 slot in the slab.
    let (lookup_nonce_ptr, _lookup_nonce_len) =
        unsafe { proof_layout.lookup_pow_nonce_device_mut(slab_base) };
    let lookup_nonce_dst: &mut era_cudart::slice::DeviceVariable<u64> =
        unsafe { era_cudart::slice::DeviceVariable::from_raw_parts_mut(lookup_nonce_ptr) };
    gpu_whir::pow::schedule_draw_e4_challenges_with_pow(
        &mut d_seed,
        &mut d_lookup_challenges,
        lookup_pow_bits,
        lookup_nonce_dst,
        context,
    )?;

    let forward_setup = if let Some(setup_transfer) = bundle.setup {
        setup_transfer.schedule_forward_setup(compiled_circuit, d_lookup_challenges, context)?
    } else {
        schedule_forward_setup_for_shape(
            None,
            compiled_circuit.trace_len,
            compiled_circuit.generic_lookup_tables_width,
            compiled_circuit.total_tables_size,
            compiled_circuit.tables_ids_in_generic_lookups,
            compiled_circuit.generic_lookup_padding,
            d_lookup_challenges,
            context,
        )?
    };

    Ok(ForwardChallengePreparation {
        forward_setup,
        d_seed,
    })
}
