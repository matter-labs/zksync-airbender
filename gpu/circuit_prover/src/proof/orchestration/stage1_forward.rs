use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::GoodAllocator;

use crate::proof::inputs::EXTERNAL_CHALLENGES_E4_LEN;
use crate::upstream::{ProverConfig, WhirSchedule};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr::proof_layout::build_proof_layout_inputs;
use gpu_gkr::proof_layout::{
    GpuGKRTraceGeometry, ProofLayout, ProofLayoutBaseLayerGeometry, WhirBaseLayerKind,
};
use gpu_gkr::setup::{schedule_forward_setup_for_shape, GpuGKRForwardSetup, GpuGKRSetupTransfer};
use gpu_gkr::stage1::GpuGKRStage1Output;
use gpu_hash::blake2s::STATE_SIZE;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::decoder::DecoderTableTransfer;
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use gpu_trace::trace::memory_transfer::GpuGKRMemoryTransfer;
use gpu_trace::trace::tracing_data::{InitsAndTeardownsTransfer, TracingDataTransfer};

pub(in crate::proof) struct Stage1AndForwardPreparation {
    pub(in crate::proof) stage1_output: GpuGKRStage1Output,
    pub(in crate::proof) synthetic_setup_trace_holder: Option<TraceHolder<BF>>,
    pub(in crate::proof) proof_layout: ProofLayout,
    pub(in crate::proof) proof_slab: Arc<DeviceAllocation<E4>>,
    pub(in crate::proof) forward_setup: GpuGKRForwardSetup,
    pub(in crate::proof) d_seed: DeviceAllocation<u32>,
}

/// Device buffers owned by the proof job's keepalive.
#[derive(Clone, Copy)]
pub(in crate::proof) struct BundleDeviceRefs<'b, 'a> {
    pub setup: Option<&'b GpuGKRSetupTransfer<'a>>,
    pub decoder: Option<&'b DecoderTableTransfer<'a>>,
    pub inits_and_teardowns: Option<&'b InitsAndTeardownsTransfer<'a>>,
    pub memory: &'b GpuGKRMemoryTransfer<'a>,
    pub canonical_top_bits_device: Option<&'b DeviceAllocation<u32>>,
    pub external_challenges_device: &'b DeviceAllocation<E4>,
}

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

pub(in crate::proof) fn prepare_stage1_and_forward_setup<'a, A: GoodAllocator + 'a>(
    gkr_programs: &gpu_gkr::GkrPrograms,
    prover_config: &ProverConfig,
    final_trace_size_log_2: u32,
    whir_schedule: &WhirSchedule,
    bundle: BundleDeviceRefs<'_, 'a>,
    tracing_data_transfer: Option<&TracingDataTransfer<'a, A>>,
    context: &ProverContext,
) -> CudaResult<Stage1AndForwardPreparation> {
    let circuit_type = gkr_programs.circuit_type();
    let compiled_circuit = gkr_programs.compiled_circuit().as_ref();
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
            // Setup-less circuits use the same geometry as memory and witness.
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
    let setup_columns_count = bundle.setup.map_or(0, |setup| {
        assert!(
            setup.trace_holder.columns_count > 0,
            "zero-width setup must be represented by no setup transfer",
        );
        setup.trace_holder.columns_count
    });

    let memory_layer_geometry = GpuGKRTraceGeometry {
        log_domain_size: compiled_circuit.trace_len.trailing_zeros(),
        log_lde_factor: bundle.memory.host.log_lde_factor,
        log_rows_per_leaf: prover_config.base_oracles_values_per_leaf.trailing_zeros(),
        log_tree_cap_size: bundle.memory.host.log_tree_cap_size,
    };
    let witness_layer_geometry = setup_geometry;
    let proof_layout_inputs = build_proof_layout_inputs(
        gkr_programs,
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
        ProofLayoutBaseLayerGeometry::from_geometry(setup_geometry, setup_columns_count),
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
    let mut d_seed: DeviceAllocation<u32> =
        context.alloc(STATE_SIZE, AllocationPlacement::BestFit)?;
    gpu_hash::blake2s::transcript_commit_initial_chunked(&mut d_seed, &chunks, stream)?;

    let mut d_lookup_challenges: DeviceAllocation<E4> =
        context.alloc(2, AllocationPlacement::BestFit)?;
    let lookup_pow_bits =
        crate::config::lookup_challenges_pow_bits(prover_config, compiled_circuit);
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

#[cfg(test)]
mod tests {
    use super::*;
    use gpu_prover_context::ProverContextConfig;

    #[test]
    fn proof_slab_allocation_is_32_byte_aligned_with_16_byte_allocator_chunks() {
        let config = ProverContextConfig {
            allocator_block_log_size: 10,
            device_slack_static_bytes: 1,
            device_slack_per_thread_bytes: 0,
            max_device_allocation_blocks_count: Some(4),
            host_allocator_block_log_size: 5,
            host_allocator_blocks_count: 1,
            small_allocator_log_chunk_size: Some(4),
            small_allocator_pool_blocks: 1,
            ..Default::default()
        };
        let context = ProverContext::new(&config).unwrap();

        // Force the next unconstrained allocation to be 16 mod 32.
        let leading_slot = context.alloc::<E4>(1, AllocationPlacement::Bottom).unwrap();
        assert_eq!(
            leading_slot.as_ptr() as usize & 0x1f,
            0,
            "test requires a 32-byte-aligned small-pool base",
        );

        let slab = allocate_proof_slab(&context, 2 * std::mem::size_of::<E4>()).unwrap();
        assert_eq!(
            slab.as_ptr() as usize & 0x1f,
            0,
            "proof slab allocation must request 32-byte alignment",
        );
    }
}
