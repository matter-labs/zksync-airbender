use std::sync::Arc;

use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::{memory_copy_async, memory_set_async};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStreamWaitEventFlags;
use fft::GoodAllocator;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::{DeviceAllocation, HostAllocation, UnsafeMutAccessor};
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::device_tracing::Range;
use gpu_core::primitives::field::PR;
use gpu_core::primitives::nvtx::scoped_range;
use gpu_gkr::proth120::backward::{DrTailProofPlanPr, GKRBackwardStageSnapshotSinkPr};
use gpu_gkr::proth120::inputs::Proth120GkrWitnessInputs;
use gpu_gkr::proth120::packed_challenges::{self, PackedChallengeConfig, PackedChallenges};
use gpu_gkr::proth120::programs::GkrProgramsPr;
use gpu_gkr::proth120::proof_layout::{GkrProofFields, ProofLayoutPr, ProofSlabPr};
use gpu_gkr::proth120::{schedule_gkr, GkrOutputPr, GkrPreparedInputsPr};
use gpu_gkr::setup::{L1WrapSetupHost, PackedSetupSource};
use gpu_ntt::proth120::TwiddleDescriptor;
use gpu_prover_context::transfer::{Transfer, TransferKeepalive};
use gpu_prover_context::ProverContext;
use gpu_trace::trace::holder::{TraceHolder, TreesCacheMode};
use gpu_trace::trace::packed::{PackedCommitConfig, PackedCosetRecomputeOracle};
use gpu_trace::trace::tracing_data::{TracingDataDevice, UnrolledTracingDataDevice};
use gpu_trace::witness::proth120::{
    generate_fused_values, generate_inits_and_teardowns, generate_lookup_multiplicities,
    Proth120WitnessBuffers,
};
use gpu_trace::witness::trace_unrolled::PAGE_SIZE_LOG2;
use gpu_whir::proth120::{
    schedule_l1_whir_fold, L1WhirInputs, L1WhirKeepalive, L1WhirPendingReadback, L1WhirProof,
};

use super::{L1Proof, L1WrapGeometry, L1WrapInputs};
use crate::proof::memory_policy::PartialTreePolicy;
use crate::upstream::{
    GKRCircuitArtifact, L1WrapResult, OperationMode, ProverConfig, TIMESTAMP_COLUMNS_NUM_BITS,
};

use super::L1WrapConstantsHost;
use crate::proof::pipeline::{self, ProofPipeline, ProofWork};
use crate::proof::{ProofJob, ProofRequest};
pub struct GpuL1WrapProofJobKeepalive<'a> {
    _setup_host: Arc<L1WrapSetupHost>,
    _input_transfer: TransferKeepalive<'a>,
    _challenges: PackedChallenges,
    _gkr: GkrOutputPr,
    _whir: L1WhirKeepalive,
    _proof_host_mirror: HostAllocation<[u8]>,
    _twiddle_tables: DeviceAllocation<PR>,
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

pub type GpuL1WrapProofJob<'a> = ProofJob<'a, L1WrapResult, GpuL1WrapProofJobKeepalive<'a>>;

struct Parameters<'r> {
    programs: &'r Arc<GkrProgramsPr>,
    circuit: &'r Arc<GKRCircuitArtifact<PR>>,
    geometry: &'r L1WrapGeometry,
    config: &'r ProverConfig,
    operation_mode: OperationMode,
    dr_tail_plan: &'r DrTailProofPlanPr,
    partial_trees: PartialTreePolicy,
}

pub struct L1WrapProofRequest<'r, 'a, A: GoodAllocator> {
    params: Parameters<'r>,
    inputs: L1WrapInputs<'a, A>,
    stage_snapshots: Option<Box<GKRBackwardStageSnapshotSinkPr>>,
}

impl<'r, 'a, A: GoodAllocator + 'a> L1WrapProofRequest<'r, 'a, A> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        programs: &'r Arc<GkrProgramsPr>,
        circuit: &'r Arc<GKRCircuitArtifact<PR>>,
        geometry: &'r L1WrapGeometry,
        config: &'r ProverConfig,
        operation_mode: OperationMode,
        inputs: L1WrapInputs<'a, A>,
        dr_tail_plan: &'r DrTailProofPlanPr,
        partial_trees: PartialTreePolicy,
    ) -> Self {
        Self {
            params: Parameters {
                programs,
                circuit,
                geometry,
                config,
                operation_mode,
                dr_tail_plan,
                partial_trees,
            },
            inputs,
            stage_snapshots: None,
        }
    }
}

impl<A: GoodAllocator> crate::proof::sealed::Sealed for L1WrapProofRequest<'_, '_, A> {}
impl<'a, A: GoodAllocator + 'a> ProofRequest for L1WrapProofRequest<'_, 'a, A> {
    type Job = GpuL1WrapProofJob<'a>;
    fn enqueue(self, context: &ProverContext) -> CudaResult<Self::Job> {
        pipeline::prove(self, context)
    }
    fn collect_stage_snapshots(mut self) -> Self {
        self.stage_snapshots = Some(Box::default());
        self
    }
}

pub(crate) struct Joined<'r, 'a, A: GoodAllocator> {
    request: L1WrapProofRequest<'r, 'a, A>,
    work: ProofWork<'a, L1WrapResult>,
}
struct State<'r, 'a> {
    params: Parameters<'r>,
    work: ProofWork<'a, L1WrapResult>,
    transfer: Transfer<'a>,
    top_bits_host: Vec<u32>,
    setup_host: Arc<L1WrapSetupHost>,
    setup: PackedSetupSource<'a>,
    constants: Arc<L1WrapConstantsHost>,
    twiddle_tables: DeviceAllocation<PR>,
    twiddles: TwiddleDescriptor,
    request_range: Option<Range>,
    stage_snapshots: Option<Box<GKRBackwardStageSnapshotSinkPr>>,
}
struct Witness {
    base: PackedCosetRecomputeOracle<PR>,
    scratch: DeviceAllocation<PR>,
    generic: DeviceAllocation<u32>,
    range16: DeviceAllocation<u32>,
    timestamp: DeviceAllocation<u32>,
}
pub(crate) struct Committed<'r, 'a> {
    state: State<'r, 'a>,
    witness: Witness,
    transcript_prefix: DeviceAllocation<u32>,
}
pub(crate) struct Challenged<'r, 'a> {
    state: State<'r, 'a>,
    witness: Witness,
    challenges: PackedChallenges,
    seed: DeviceAllocation<u8>,
}
pub(crate) struct Gkr<'r, 'a> {
    state: State<'r, 'a>,
    base: PackedCosetRecomputeOracle<PR>,
    layout: Arc<ProofLayoutPr>,
    slab: ProofSlabPr,
    challenges: PackedChallenges,
    gkr: GkrOutputPr,
}
pub(crate) struct Whir<'r, 'a> {
    gkr: Gkr<'r, 'a>,
    output: L1WhirPendingReadback,
}

impl<'r, 'a, A: GoodAllocator + 'a> ProofPipeline for L1WrapProofRequest<'r, 'a, A> {
    type Joined = Joined<'r, 'a, A>;
    type Committed = Committed<'r, 'a>;
    type Challenged = Challenged<'r, 'a>;
    type Gkr = Gkr<'r, 'a>;
    type Whir = Whir<'r, 'a>;
    type Job = GpuL1WrapProofJob<'a>;

    fn join(self, context: &ProverContext) -> CudaResult<Self::Joined> {
        self.inputs.transfer.ensure_transferred(context)?;
        context.reset_used_mem_peak();
        self.inputs
            .decoder
            .as_ref()
            .expect("L1Wrap requires a decoder table");
        let work = ProofWork::new("l1_wrap.proof", context)?;
        Ok(Joined {
            request: self,
            work,
        })
    }

    fn witness_commit(
        joined: Self::Joined,
        context: &ProverContext,
    ) -> CudaResult<Self::Committed> {
        let Joined {
            request:
                L1WrapProofRequest {
                    params,
                    inputs,
                    stage_snapshots,
                },
            mut work,
        } = joined;
        let circuit = params.circuit;
        let geometry = params.geometry;
        let cfg =
            PackedCommitConfig::from_prover_config(params.config, params.partial_trees.memory);
        let rows = geometry.rows;
        let memory_columns = geometry.memory_columns;
        let witness_columns = geometry.witness_columns;
        let L1WrapInputs {
            transfer,
            decoder,
            inits_and_teardowns,
            tracing_data,
            transcript_prefix,
            transcript_prefix_host: _,
            top_bits_host,
            setup_host,
            setup,
            constants,
            request_range,
        } = inputs;
        let decoder = decoder.expect("L1Wrap requires a decoder table");
        let stream = context.get_exec_stream();
        let p = phase("l1_wrap.witness", context)?;
        let mut raw = TraceHolder::<PR>::new_without_cosets_padded(
            geometry.trace_log,
            cfg.log_lde_factor,
            cfg.log_values_per_leaf,
            cfg.cap_log,
            memory_columns + witness_columns,
            geometry.pack_log2,
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
            generate_fused_values(
                circuit,
                &decoder.data_device,
                trace,
                &DeviceMatrix::new(setup.raw().get_hypercube_evals(), rows),
                &constants.relations,
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
        end_phase(p, &mut work.ranges, context)?;
        drop(tracing_data);
        drop(inits_and_teardowns);
        drop(decoder);
        let p = phase("l1_wrap.pack", context)?;
        let mut base =
            PackedCosetRecomputeOracle::pack_from_columns(raw, geometry.pack_log2, context)?;
        end_phase(p, &mut work.ranges, context)?;
        let p = phase("l1_wrap.commit", context)?;
        // Build one pair of forward tables for this proof's commitments and openings.
        let mut twiddle_tables =
            context.alloc::<PR>(gpu_ntt::proth120::TABLE_LEN, AllocationPlacement::Bottom)?;
        let mut twiddle_factors =
            context.alloc::<PR>(gpu_ntt::proth120::FACTOR_LEN, AllocationPlacement::BestFit)?;
        let twiddles = gpu_ntt::proth120::prepare_proof_twiddles(
            &mut twiddle_tables,
            &mut twiddle_factors,
            context.get_exec_stream(),
        )?;
        drop(twiddle_factors);
        base.commit(&cfg, twiddles, context)?;
        end_phase(p, &mut work.ranges, context)?;
        Ok(Committed {
            state: State {
                params,
                work,
                transfer,
                top_bits_host,
                setup_host,
                setup,
                constants,
                twiddle_tables,
                twiddles,
                request_range,
                stage_snapshots,
            },
            witness: Witness {
                base,
                scratch,
                generic,
                range16,
                timestamp,
            },
            transcript_prefix,
        })
    }

    fn challenges(
        committed: Self::Committed,
        context: &ProverContext,
    ) -> CudaResult<Self::Challenged> {
        let Committed {
            mut state,
            witness,
            transcript_prefix,
        } = committed;
        let circuit = state.params.circuit;
        let config = state.params.config;
        let operation_mode = &state.params.operation_mode;
        let setup = &state.setup;
        let base = &witness.base;
        let stream = context.get_exec_stream();
        let p = phase("l1_wrap.challenges", context)?;
        let mut seed = context.alloc::<u8>(32, AllocationPlacement::BestFit)?;
        memory_set_async(&mut seed, 0, stream)?;
        let challenge_config = PackedChallengeConfig::new(circuit, config, operation_mode, true);
        let challenges = packed_challenges::derive(
            &mut seed,
            &transcript_prefix,
            setup.cap(),
            base.cap(),
            &challenge_config,
            context,
        )?;
        drop(transcript_prefix);
        end_phase(p, &mut state.work.ranges, context)?;
        Ok(Challenged {
            state,
            witness,
            challenges,
            seed,
        })
    }

    fn gkr(challenged: Self::Challenged, context: &ProverContext) -> CudaResult<Self::Gkr> {
        let Challenged {
            mut state,
            witness:
                Witness {
                    base,
                    scratch,
                    generic,
                    range16,
                    timestamp,
                },
            challenges,
            seed,
        } = challenged;
        let programs = state.params.programs;
        let circuit = state.params.circuit;
        let geometry = state.params.geometry;
        let config = state.params.config;
        let dr_tail_plan = state.params.dr_tail_plan;
        let setup = &state.setup;
        let top_bits_host = &state.top_bits_host;
        let constants = &state.constants;
        let batching_pow_bits = geometry.batching_pow_bits;
        let rows = geometry.rows;
        let memory_columns = geometry.memory_columns;
        let multiplicity_start = circuit
            .witness_layout
            .multiplicities_columns_for_range_check_16
            .start;
        let multiplicity_end = circuit
            .witness_layout
            .multiplicities_columns_for_generic_lookup
            .end;
        let p = phase("l1_wrap.gkr", context)?;
        let layout = Arc::new(ProofLayoutPr::new(programs, config));
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
        let gkr = schedule_gkr(
            Arc::clone(programs),
            &base,
            setup,
            witness,
            top_bits_host,
            &challenges,
            config,
            batching_pow_bits,
            seed,
            &mut slab,
            dr_tail_plan,
            state
                .stage_snapshots
                .as_deref_mut()
                .map(UnsafeMutAccessor::new),
            GkrPreparedInputsPr {
                base_claim_indices: constants.base_claim_indices,
            },
            &mut state.work.callbacks,
            context,
        )?;
        drop(generic);
        drop(range16);
        drop(timestamp);
        end_phase(p, &mut state.work.ranges, context)?;
        Ok(Gkr {
            state,
            base,
            layout,
            slab,
            challenges,
            gkr,
        })
    }

    fn whir(mut gkr: Self::Gkr, context: &ProverContext) -> CudaResult<Self::Whir> {
        let config = gkr.state.params.config;
        let p = phase("l1_wrap.whir", context)?;
        let handoff = gkr.gkr.whir_handoff();
        let whir = schedule_l1_whir_fold(
            &mut gkr.base,
            &mut gkr.state.setup,
            handoff.seed,
            L1WhirInputs {
                twiddles: gkr.state.twiddles,
                claims: handoff.claims,
                base_layer_point: handoff.base_layer_point,
                batching_challenge: handoff.batching_challenge,
            },
            &config.whir_schedule,
            gkr.slab.whir_target(),
            context,
        )?;
        end_phase(p, &mut gkr.state.work.ranges, context)?;
        Ok(Whir { gkr, output: whir })
    }

    fn readback(state: Self::Whir, context: &ProverContext) -> CudaResult<Self::Job> {
        let Whir {
            gkr:
                Gkr {
                    state:
                        State {
                            params,
                            mut work,
                            transfer,
                            top_bits_host,
                            setup_host,
                            setup,
                            constants: _,
                            twiddle_tables,
                            twiddles: _,
                            request_range,
                            stage_snapshots,
                        },
                    base,
                    layout,
                    slab,
                    challenges,
                    gkr,
                },
            output: whir,
        } = state;
        let operation_mode = params.operation_mode;
        let stream = context.get_exec_stream();
        let p = phase("l1_wrap.readback", context)?;
        let mut mirror = unsafe { context.alloc_host_uninit_slice::<u8>(layout.bytes_len()) };
        let slab_bytes = unsafe {
            DeviceSlice::from_raw_parts(slab.backing.as_ptr().cast::<u8>(), layout.bytes_len())
        };
        memory_copy_async(&mut mirror, slab_bytes, stream)?;
        let mirror_accessor = mirror.get_accessor();
        let whir_readback = whir.readback();
        let result_accessor = UnsafeMutAccessor::new(work.result.as_mut());
        work.callbacks.schedule(
            move || {
                let _range = scoped_range(Some("ab"), "l1_wrap.assembly");
                let bytes = unsafe { mirror_accessor.get() };
                let fields = layout.parse_gkr_fields(bytes);
                let (memory_claims, setup_claims) = &fields.merged_claims;
                let whir = whir_readback.assemble(
                    bytes,
                    memory_claims,
                    setup_claims,
                    fields.batched_proximity_check_pow_nonce,
                );
                let proof = assemble_l1_proof(fields, whir, top_bits_host.clone(), operation_mode);
                unsafe { result_accessor.get_mut() }.replace(proof);
            },
            stream,
        )?;
        drop(slab);
        end_phase(p, &mut work.ranges, context)?;
        if let Some(request_range) = request_range {
            end_phase(request_range, &mut work.ranges, context)?;
        }
        let h2d_join = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
        h2d_join.record(stream)?;
        context
            .get_h2d_stream()
            .wait_event(&h2d_join, CudaStreamWaitEventFlags::DEFAULT)?;
        work.proof_range.end(stream)?;
        let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
        is_finished_event.record(stream)?;
        work.ranges.push(work.proof_range);
        let job = ProofJob {
            is_finished_event,
            callbacks: work.callbacks,
            result: work.result,
            stage_snapshots,
            ranges: work.ranges,
            keepalive: GpuL1WrapProofJobKeepalive {
                _setup_host: setup_host,
                _input_transfer: transfer.into_keepalive(),
                _challenges: challenges,
                _gkr: gkr,
                _whir: whir.into_keepalive(),
                _proof_host_mirror: mirror,
                _twiddle_tables: twiddle_tables,
            },
        };
        drop(base);
        drop(setup);
        Ok(job)
    }
}

pub fn assemble_l1_proof(
    gkr: GkrProofFields,
    mut whir: L1WhirProof,
    top_bits: Vec<u32>,
    operation_mode: OperationMode,
) -> L1WrapResult {
    whir.batching_challenge_pow_nonce = gkr.batched_proximity_check_pow_nonce;
    L1WrapResult {
        proof: L1Proof {
            external_challenges: gkr.external_challenges,
            final_explicit_evaluations: gkr.final_explicit_evaluations,
            sumcheck_intermediate_values: gkr.sumcheck_intermediate_values,
            whir_proof: whir,
            grand_product_accumulator_computed: gkr.grand_product_accumulator_computed,
            inits_and_teardowns_top_bits: top_bits,
            lookup_challenges_pow_nonce: gkr.lookup_challenges_pow_nonce,
        },
        operation_mode,
    }
}
