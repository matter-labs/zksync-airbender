use std::sync::Arc;

use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::{memory_copy_async, memory_set_async};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStreamWaitEventFlags;
use fft::GoodAllocator;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{HostAllocation, UnsafeMutAccessor};
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::PR;
use gpu_gkr::proth120::backward::DrTailProofPlanPr;
use gpu_gkr::proth120::inputs::Proth120GkrWitnessInputs;
use gpu_gkr::proth120::packed_challenges::{self, PackedChallengeConfig, PackedChallenges};
use gpu_gkr::proth120::programs::GkrProgramsPr;
use gpu_gkr::proth120::proof_layout::{M6ProofFields, ProofLayoutPr, ProofSlabPr};
use gpu_gkr::proth120::{schedule_gkr, GkrOutputPr};
use gpu_gkr::setup::{L1WrapSetupHost, PackedSetupSource};
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use gpu_trace::trace::packed::{PackedCommitConfig, PackedCosetRecomputeOracle};
use gpu_trace::trace::tracing_data::{TracingDataDevice, UnrolledTracingDataDevice};
use gpu_trace::witness::proth120::{
    generate_fused_values, generate_inits_and_teardowns, generate_lookup_multiplicities,
    prepare_lookup_relations, Proth120LookupRelations, Proth120WitnessBuffers,
};
use gpu_trace::witness::trace_unrolled::PAGE_SIZE_LOG2;
use gpu_whir::proth120::{
    schedule_l1_whir_fold, L1WhirInputs, L1WhirProof, L1WhirScheduled, L1WhirShape,
    L1_WHIR_TILE_BYTES,
};

use super::{
    l1_wrap_batching_pow_bits, validate_l1_wrap_preconditions, L1Proof, L1WrapGeometry,
    L1WrapInputs,
};
use crate::proof::memory_policy::{PartialTreePolicy, ProofMemoryPolicy};
use crate::upstream::{
    CommitmentMode, GKRCircuitArtifact, L1WrapResult, ProverConfig, TIMESTAMP_COLUMNS_NUM_BITS,
};

pub struct GpuL1WrapProofJob<'a> {
    is_finished_event: CudaEvent,
    callbacks: Callbacks<'a>,
    m6_fields: Box<Option<M6ProofFields>>,
    whir: Option<L1WhirScheduled>,
    top_bits_host: Vec<u32>,
    commitment_mode: CommitmentMode,
    ranges: Vec<Range>,
    keepalive: GpuL1WrapProofJobKeepalive<'a>,
}

pub(crate) struct GpuL1WrapProofJobKeepalive<'a> {
    _setup_host: Arc<L1WrapSetupHost>,
    _input_callbacks: Callbacks<'a>,
    _setup_callbacks: Callbacks<'a>,
    _relations: Proth120LookupRelations,
    _challenges: PackedChallenges,
    _gkr: GkrOutputPr,
    _proof_host_mirror: HostAllocation<[u8]>,
}

/// Until disarmed, an early exit makes exec_stream wait for everything queued on h2d_stream,
/// so pool blocks of a dropped upload destination are not reused under an in-flight copy.
struct H2dJoinOnDrop<'c> {
    context: &'c ProverContext,
    event: CudaEvent,
    armed: bool,
}

impl<'c> H2dJoinOnDrop<'c> {
    fn new(context: &'c ProverContext) -> CudaResult<Self> {
        Ok(Self {
            context,
            event: CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?,
            armed: true,
        })
    }
}

impl Drop for H2dJoinOnDrop<'_> {
    fn drop(&mut self) {
        if !self.armed {
            return;
        }
        self.event
            .record(self.context.get_h2d_stream())
            .and_then(|()| {
                self.context
                    .get_exec_stream()
                    .wait_event(&self.event, CudaStreamWaitEventFlags::DEFAULT)
            })
            .expect("L1Wrap: cannot order exec_stream after the pending h2d_stream uploads");
    }
}

fn phase(name: &str, context: &ProverContext) -> CudaResult<Range> {
    let range = Range::new(name)?;
    range.start(context.get_exec_stream())?;
    Ok(range)
}

fn end_phase(range: Range, phases: &mut Vec<Range>, context: &ProverContext) -> CudaResult<()> {
    range.end(context.get_exec_stream())?;
    phases.push(range);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn prove<'a, A: GoodAllocator + 'a>(
    programs: &Arc<GkrProgramsPr>,
    circuit: &Arc<GKRCircuitArtifact<PR>>,
    geometry: &L1WrapGeometry,
    config: &ProverConfig,
    commitment_mode: CommitmentMode,
    inputs: L1WrapInputs<'a, A>,
    dr_tail_plan: &DrTailProofPlanPr,
    policy: ProofMemoryPolicy,
    partial_trees: PartialTreePolicy,
    context: &ProverContext,
) -> CudaResult<GpuL1WrapProofJob<'a>> {
    partial_trees.assert_valid();
    inputs.transfer.ensure_transferred(context)?;
    context.reset_used_mem_peak();
    validate_l1_wrap_preconditions(
        geometry,
        config,
        &commitment_mode,
        policy,
        context.proth120_ntt_device_context().log_max_domain(),
    );
    geometry.assert_artifact(circuit);
    let circuit_type = geometry.circuit_type;
    let batching_pow_bits = geometry.batching_pow_bits;
    assert_eq!(
        l1_wrap_batching_pow_bits(config, circuit, geometry.pack_log2),
        batching_pow_bits,
        "{circuit_type:?} batching PoW bits disagree with the geometry"
    );
    let cfg =
        PackedCommitConfig::from_prover_config(config, geometry.log_message, partial_trees.memory);
    let rows = geometry.rows;
    let memory_columns = geometry.memory_columns;
    let witness_columns = geometry.witness_columns;
    assert_eq!(
        inputs.top_bits_host.len(),
        geometry.num_it_sets,
        "{circuit_type:?} inits-and-teardowns top bits count mismatch"
    );
    assert_eq!(
        inputs.setup_host.log_rows, geometry.trace_log,
        "{circuit_type:?} setup trace log mismatch"
    );
    assert_eq!(
        inputs.setup_host.columns_count, geometry.setup_columns,
        "{circuit_type:?} setup columns mismatch"
    );
    assert_eq!(
        inputs.setup_host.pack_log2, geometry.pack_log2,
        "{circuit_type:?} setup pack_log2 mismatch"
    );
    assert!(
        inputs.setup_host.cfg.same_protocol_geometry(&cfg),
        "{circuit_type:?} setup commitment config mismatch"
    );
    let multiplicity_start = circuit
        .witness_layout
        .multiplicities_columns_for_range_check_16
        .start;
    let multiplicity_end = circuit
        .witness_layout
        .multiplicities_columns_for_generic_lookup
        .end;
    let L1WrapInputs {
        transfer,
        decoder,
        inits_and_teardowns,
        tracing_data,
        top_bits,
        top_bits_host,
        setup_host,
        coefficient_tables,
    } = inputs;
    let decoder = decoder.expect("L1Wrap requires a decoder table");
    let stream = context.get_exec_stream();
    let range = Range::new("l1_wrap.proof")?;
    range.start(stream)?;
    let mut callbacks = Callbacks::new();
    let mut phases: Vec<Range> = Vec::new();
    let p = phase("l1_wrap.setup_transfer", context)?;
    let mut setup = PackedSetupSource::new(Arc::clone(&setup_host), partial_trees.setup, context)?;
    let mut setup_upload_guard = H2dJoinOnDrop::new(context)?;
    let mut setup_raw_transfer = Transfer::new()?;
    setup_raw_transfer.record_allocated(context)?;
    setup.schedule_raw_transfer(&mut setup_raw_transfer, context)?;
    setup_raw_transfer.record_transferred(context)?;
    let mut setup_transfer = Transfer::new()?;
    setup_transfer.record_allocated(context)?;
    setup.schedule_commitment_transfer(&mut setup_transfer, context)?;
    setup_transfer.record_transferred(context)?;
    end_phase(p, &mut phases, context)?;
    let p = phase("l1_wrap.witness", context)?;
    let mut raw = TraceHolder::<PR>::new_without_cosets(
        geometry.trace_log,
        cfg.log_lde_factor,
        cfg.log_values_per_leaf,
        cfg.cap_log,
        memory_columns + witness_columns,
        TreesCacheMode::CacheNone,
        gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
        context,
    )?;
    let mut scratch = context.alloc::<PR>(
        circuit.scratch_space_size * rows,
        AllocationPlacement::BestFit,
    )?;
    let mut generic = context.alloc::<u32>(
        (circuit.generic_lookups.len() + 1) * rows,
        AllocationPlacement::BestFit,
    )?;
    let mut range16 = context.alloc::<u32>(
        circuit.range_check_16_lookup_expressions.len() * rows,
        AllocationPlacement::BestFit,
    )?;
    let mut timestamp = context.alloc::<u32>(
        circuit.timestamp_range_check_lookup_expressions.len() * rows,
        AllocationPlacement::BestFit,
    )?;
    let relations = prepare_lookup_relations(circuit, context)?;
    {
        let (memory, witness) = raw
            .get_uninit_hypercube_evals_mut()
            .split_at_mut(memory_columns * rows);
        let (generic_mapping, decoder_mapping) =
            generic.split_at_mut(circuit.generic_lookups.len() * rows);
        let mut buffers = Proth120WitnessBuffers {
            memory: DeviceMatrixMut::new(memory, rows),
            witness: DeviceMatrixMut::new(witness, rows),
            scratch: DeviceMatrixMut::new(&mut scratch, rows),
            generic_lookup_mapping: DeviceMatrixMut::new(generic_mapping, rows),
            range_check_16_lookup_mapping: DeviceMatrixMut::new(&mut range16, rows),
            range_check_timestamp_lookup_mapping: DeviceMatrixMut::new(&mut timestamp, rows),
            decoder_lookup_mapping: decoder_mapping,
        };
        generate_inits_and_teardowns(
            &circuit.memory_layout,
            geometry.trace_log,
            PAGE_SIZE_LOG2,
            &inits_and_teardowns.data_device,
            &mut buffers.memory,
            stream,
        )?;
        let TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Unified(trace)) =
            &tracing_data.data_device
        else {
            panic!("L1Wrap requires unrolled unified tracing data");
        };
        setup_raw_transfer.ensure_transferred(context)?;
        generate_fused_values(
            circuit,
            &decoder.data_device,
            trace,
            &DeviceMatrix::new(setup.raw().get_hypercube_evals(), rows),
            &relations,
            &mut buffers,
            stream,
        )?;
    }
    {
        let witness = &mut raw.get_uninit_hypercube_evals_mut()[memory_columns * rows..];
        for (mapping, columns, active_counts_len) in [
            (
                &mut generic,
                circuit
                    .witness_layout
                    .multiplicities_columns_for_generic_lookup
                    .clone(),
                circuit.total_tables_size,
            ),
            (
                &mut range16,
                circuit
                    .witness_layout
                    .multiplicities_columns_for_range_check_16
                    .clone(),
                1 << 16,
            ),
            (
                &mut timestamp,
                circuit
                    .witness_layout
                    .multiplicities_columns_for_timestamp_range_check
                    .clone(),
                1 << TIMESTAMP_COLUMNS_NUM_BITS,
            ),
        ] {
            generate_lookup_multiplicities(
                &mut DeviceMatrixMut::new(mapping, rows),
                &mut DeviceMatrixMut::new(
                    &mut witness[columns.start * rows..columns.end * rows],
                    rows,
                ),
                active_counts_len,
                context,
            )?;
        }
    }
    end_phase(p, &mut phases, context)?;
    drop(tracing_data);
    drop(inits_and_teardowns);
    drop(decoder);
    let p = phase("l1_wrap.pack", context)?;
    let mut base = PackedCosetRecomputeOracle::pack_from_columns(raw, geometry.pack_log2, context)?;
    end_phase(p, &mut phases, context)?;
    let p = phase("l1_wrap.commit", context)?;
    base.commit(&cfg, context)?;
    end_phase(p, &mut phases, context)?;
    let p = phase("l1_wrap.challenges", context)?;
    let mut seed = context.alloc::<u8>(32, AllocationPlacement::BestFit)?;
    memory_set_async(&mut seed, 0, stream)?;
    let challenge_config = PackedChallengeConfig::new(circuit, config, &commitment_mode, true);
    setup_transfer.ensure_transferred(context)?;
    setup_upload_guard.armed = false;
    let challenges = packed_challenges::derive(
        &mut seed,
        &commitment_mode,
        &top_bits.device,
        setup.cap(),
        base.cap(),
        &challenge_config,
        context,
    )?;
    drop(top_bits);
    end_phase(p, &mut phases, context)?;
    let p = phase("l1_wrap.gkr", context)?;
    let layout = Arc::new(ProofLayoutPr::new(
        programs,
        config,
        geometry.pack_log2 as usize,
    ));
    let mut slab = ProofSlabPr::new(Arc::clone(&layout), context)?;
    #[allow(clippy::arc_with_non_send_sync)]
    let witness = Proth120GkrWitnessInputs::new(
        circuit,
        Arc::new(scratch),
        circuit.scratch_space_size,
        rows,
        DeviceMatrix::new(&generic[..circuit.generic_lookups.len() * rows], rows),
        DeviceMatrix::new(&range16, rows),
        DeviceMatrix::new(&timestamp, rows),
        &generic[circuit.generic_lookups.len() * rows..],
        DeviceMatrix::new(
            &base.raw().get_hypercube_evals()[(memory_columns + multiplicity_start) * rows
                ..(memory_columns + multiplicity_end) * rows],
            rows,
        ),
    );
    let mut gkr = schedule_gkr(
        Arc::clone(programs),
        &base,
        &setup,
        witness,
        &top_bits_host,
        &challenges,
        config,
        batching_pow_bits,
        seed,
        &mut slab,
        dr_tail_plan,
        None,
        Some(coefficient_tables),
        &mut callbacks,
        context,
    )?;
    drop(generic);
    drop(range16);
    drop(timestamp);
    end_phase(p, &mut phases, context)?;
    let p = phase("l1_wrap.whir", context)?;
    let shape = L1WhirShape::from_schedule(
        &config.whir_schedule,
        geometry.log_message,
        geometry.log_base_lde,
        geometry.log_base_values_per_leaf,
        L1_WHIR_TILE_BYTES,
    );
    let pending = {
        let handoff = gkr.whir_handoff();
        schedule_l1_whir_fold(
            &mut base,
            &mut setup,
            handoff.seed,
            L1WhirInputs {
                claims: handoff.claims,
                base_layer_point: handoff.base_layer_point,
                batching_challenge: handoff.batching_challenge,
            },
            &config.whir_schedule,
            &shape,
            context,
        )?
    };
    end_phase(p, &mut phases, context)?;
    let p = phase("l1_wrap.readback", context)?;
    let whir = {
        let handoff = gkr.whir_handoff();
        pending.schedule_readback(
            L1WhirInputs {
                claims: handoff.claims,
                base_layer_point: handoff.base_layer_point,
                batching_challenge: handoff.batching_challenge,
            },
            base.cap_digests(),
            setup.oracle().cap_digests(),
            context,
        )?
    };
    let mut mirror = unsafe { context.alloc_host_uninit_slice::<u8>(layout.bytes_len()) };
    let slab_bytes = unsafe {
        DeviceSlice::from_raw_parts(slab.backing.as_ptr().cast::<u8>(), layout.bytes_len())
    };
    memory_copy_async(&mut mirror, slab_bytes, stream)?;
    let mirror_accessor = mirror.get_accessor();
    let mut m6_fields = Box::new(None);
    let m6_accessor = UnsafeMutAccessor::new(&mut *m6_fields);
    callbacks.schedule(
        move || {
            let fields = layout.parse_m6_fields(unsafe { mirror_accessor.get() });
            unsafe { m6_accessor.get_mut() }.replace(fields);
        },
        stream,
    )?;
    drop(slab);
    end_phase(p, &mut phases, context)?;
    let h2d_join = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    h2d_join.record(stream)?;
    context
        .get_h2d_stream()
        .wait_event(&h2d_join, CudaStreamWaitEventFlags::DEFAULT)?;
    range.end(stream)?;
    let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    is_finished_event.record(stream)?;
    Ok(GpuL1WrapProofJob {
        is_finished_event,
        callbacks,
        m6_fields,
        whir: Some(whir),
        top_bits_host,
        commitment_mode,
        ranges: {
            phases.push(range);
            phases
        },
        keepalive: GpuL1WrapProofJobKeepalive {
            _setup_host: setup_host,
            _input_callbacks: transfer.into_callbacks(),
            _setup_callbacks: {
                let mut callbacks = setup_raw_transfer.into_callbacks();
                callbacks.extend(setup_transfer.into_callbacks());
                callbacks
            },
            _relations: relations,
            _challenges: challenges,
            _gkr: gkr,
            _proof_host_mirror: mirror,
        },
    })
}

impl GpuL1WrapProofJob<'_> {
    pub fn finish(self) -> CudaResult<L1WrapResult> {
        let Self {
            is_finished_event,
            callbacks,
            mut m6_fields,
            mut whir,
            top_bits_host,
            commitment_mode,
            ranges,
            keepalive,
        } = self;
        is_finished_event.synchronize()?;
        let fields = m6_fields
            .take()
            .expect("L1Wrap M6 readback did not complete");
        let whir = whir
            .take()
            .expect("L1Wrap WHIR job missing")
            .into_proof_after_completion();
        let result = assemble_l1_proof(fields, whir, top_bits_host, commitment_mode);
        for range in &ranges {
            log::debug!("{}: {} ms", range.name(), range.elapsed()?);
        }
        drop(callbacks);
        drop(keepalive);
        Ok(result)
    }
}

pub fn assemble_l1_proof(
    m6: M6ProofFields,
    whir: L1WhirProof,
    top_bits: Vec<u32>,
    commitment_mode: CommitmentMode,
) -> L1WrapResult {
    L1WrapResult {
        proof: L1Proof {
            external_challenges: m6.external_challenges,
            final_explicit_evaluations: m6.final_explicit_evaluations,
            sumcheck_intermediate_values: m6.sumcheck_intermediate_values,
            whir_proof: whir,
            grand_product_accumulator_computed: m6.grand_product_accumulator_computed,
            inits_and_teardowns_top_bits: top_bits,
            intermediate_transcript_seed: Some(m6.intermediate_transcript_seed),
            lookup_challenges_pow_nonce: m6.lookup_challenges_pow_nonce,
            batched_proximity_check_pow_nonce: m6.batched_proximity_check_pow_nonce,
        },
        commitment_mode,
    }
}
