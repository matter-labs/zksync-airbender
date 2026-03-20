use super::gkr::{
    backward::{
        GpuGKRDimensionReducingBackwardState, GpuGKRDimensionReducingSumcheckLayerPlan,
        GpuGKRMainLayerKernelKind, GpuGKRMainLayerSumcheckLayerPlan,
    },
    base_layer_claims::prepare_base_layer_claims,
    forward::schedule_forward_pass,
    setup::{GpuGKRSetupHost, GpuGKRSetupTransfer},
    stage1::GpuGKRStage1Output,
    GpuGKRStorage,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::{set_by_ref, SetByRef};
use crate::primitives::circuit_type::{
    CircuitType, UnrolledCircuitType, UnrolledNonMemoryCircuitType,
};
use crate::primitives::context::ProverContext;
use crate::primitives::field::{BF, E4};
use crate::primitives::nvtx_registered::start_registered_range;
use crate::primitives::static_host::alloc_static_pinned_box_from_slice;
use crate::prover::decoder::DecoderTableTransfer;
use crate::prover::proof::{
    prove, prove_with_transfer_scheduling, GkrExternalPowChallenges, GpuGKRProofJob,
};
use crate::prover::test_utils::make_test_context;
use crate::prover::trace_holder::TraceHolder;
use crate::prover::tracing_data::{
    TracingDataDevice, TracingDataHost, TracingDataTransfer, UnrolledTracingDataDevice,
    UnrolledTracingDataHost,
};
use crate::prover::whir::GpuWhirExtensionOracle;
use crate::prover::whir_fold::{
    clone_scheduled_whir_pre_pow_seeds, debug_apply_initial_fold_challenge_for_test,
    debug_build_initial_batched_main_domain_poly_for_test, debug_build_initial_fold_state_for_test,
    debug_build_initial_state_for_test, debug_build_initial_state_snapshots_for_test,
    debug_initial_round_checkpoint_for_test, gpu_whir_fold_supported_path,
    gpu_whir_fold_supported_path_with_external_pow, schedule_gpu_whir_fold_with_sources,
};
use crate::witness::trace::ChunkedTraceHolder;
use crate::witness::trace_unrolled::{ExecutorFamilyDecoderData, UnrolledNonMemoryTraceDevice};
use cs::definitions::*;
use cs::gkr_circuits::{
    add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr,
    add_sub_lui_auipc_mop_table_addition_fn,
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    process_binary_into_separate_tables_ext,
};
use cs::gkr_compiler::compile_unrolled_circuit_state_transition_into_gkr;
use cs::gkr_compiler::{GKRCircuitArtifact, GKRLayerDescription, NoFieldGKRRelation, OutputType};
use cs::tables::TableDriver;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::{
    batch_inverse_inplace, bitreverse_enumeration_inplace, domain_generator_for_size,
    materialize_powers_serial_starting_with_elem, materialize_powers_serial_starting_with_one,
    Twiddles,
};
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::{Field, FieldExtension, PrimeField};
use itertools::Itertools;
use nvtx::range;
use prover::definitions::Transcript;
use prover::gkr::prover::dimension_reduction::{self, forward::DimensionReducingInputOutput};
use prover::gkr::prover::forward_loop;
use prover::gkr::prover::prove_configured_with_gkr;
use prover::gkr::prover::setup::GKRSetup;
use prover::gkr::prover::stages::stage1;
use prover::gkr::prover::stages::stage1::ColumnMajorCosetBoundTracePart;
use prover::gkr::prover::sumcheck_loop;
use prover::gkr::prover::transcript_utils::{
    add_whir_commitment_to_transcript, commit_field_els, draw_query_bits, draw_random_field_els,
};
use prover::gkr::prover::utils::flatten_merkle_caps_iter_into;
use prover::gkr::prover::{GKRExternalChallenges, GKRProof, WhirSchedule};
use prover::gkr::sumcheck::access_and_fold::GKRStorage;
use prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full;
use prover::gkr::sumcheck::evaluate_small_univariate_poly;
use prover::gkr::sumcheck::evaluation_kernels::{
    BaseFieldCopyGKRRelation, BatchConstraintEvalGKRRelation, BatchedGKRKernel,
    ExtensionCopyGKRRelation, GKRInputs, LookupBaseExtMinusBaseExtGKRRelation,
    LookupBaseMinusMultiplicityByBaseGKRRelation, LookupBasePairGKRRelation, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation, MaskIntoIdentityProductGKRRelation,
    SameSizeProductGKRRelation,
};
use prover::gkr::whir::{
    whir_fold, ColumnMajorBaseOracleForLDE, ColumnMajorExtensionOracleForCoset,
    ColumnMajorExtensionOracleForLDE, WhirCommitment, WhirPolyCommitProof,
};
use prover::gkr::witness_gen::family_circuits::{
    evaluate_gkr_memory_witness_for_executor_family, evaluate_gkr_witness_for_executor_family,
    GKRFullWitnessTrace, GKRMemoryOnlyWitnessTrace,
};
use prover::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
use prover::merkle_trees::{
    ColumnMajorMerkleTreeConstructor, DefaultTreeConstructor, MerkleTreeCapVarLength,
};
use prover::query_utils::assemble_query_index;
use prover::transcript::Seed;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{
    Counters, DelegationsAndFamiliesCounters, RamWithRomRegion, ReplayBuffer, SimpleSnapshotter,
    SimpleTape, State, VM,
};
use riscv_transpiler::witness::{NonMemDestinationHolder, NonMemoryOpcodeTracingDataWithTimestamp};
use serial_test::serial;
use std::alloc::Global;
use std::collections::BTreeMap;
use std::ops::DerefMut;
use std::path::PathBuf;
use std::sync::Arc;
use worker::Worker;

const NUM_INIT_AND_TEARDOWN_SETS: usize = 6;

fn test_artifact_path(relative_path: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(relative_path)
}

fn ensure_memory_trace_consistency<F: PrimeField>(
    memory_trace: &GKRMemoryOnlyWitnessTrace<
        F,
        impl std::alloc::Allocator + Clone,
        impl std::alloc::Allocator + Clone,
    >,
    witness_trace: &GKRFullWitnessTrace<
        F,
        impl std::alloc::Allocator + Clone,
        impl std::alloc::Allocator + Clone,
    >,
) {
    assert_eq!(
        memory_trace.column_major_trace.len(),
        witness_trace.column_major_memory_trace.len()
    );
    for (col, from_mem) in memory_trace.column_major_trace.iter().enumerate() {
        let from_wit = &witness_trace.column_major_memory_trace[col];
        assert_eq!(from_mem.len(), from_wit.len());
        for (row, (a, b)) in from_mem.iter().zip(from_wit.iter()).enumerate() {
            assert_eq!(*a, *b, "diverged for column {}, row {}", col, row);
        }
    }
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

fn evaluate_base_poly_with_eq<F: PrimeField, E: FieldExtension<F> + Field>(
    values: &[F],
    eq: &[E],
) -> E {
    assert_eq!(values.len(), eq.len());
    let mut result = E::ZERO;
    for (value, eq_value) in values.iter().zip(eq.iter()) {
        let mut term = *eq_value;
        term.mul_assign_by_base(value);
        result.add_assign(&term);
    }
    result
}

fn compute_initial_sumcheck_claims_for_test<F: PrimeField, E: FieldExtension<F> + Field>(
    gkr_storage: &GKRStorage<F, E>,
    eval_point: &[E],
    output_layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    worker: &Worker,
) -> [E; 8] {
    let eq_precomputed = make_eq_poly_in_full::<E>(eval_point, worker);
    let eq = eq_precomputed.last().unwrap();

    let mut evals = vec![];
    for key in [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        let addresses = &output_layer[&key];
        for address in addresses.output.iter() {
            let poly = gkr_storage.get_ext_poly(*address);
            evals.push(evaluate_ext_poly_with_eq(poly, &eq[..]));
        }
    }

    evals.try_into().unwrap()
}

fn collect_final_explicit_evaluations_for_test<F: PrimeField, E: FieldExtension<F> + Field>(
    gkr_storage: &GKRStorage<F, E>,
    output_layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    expected_poly_len: usize,
) -> (BTreeMap<OutputType, [Vec<E>; 2]>, Vec<E>) {
    let mut final_explicit_evaluations = BTreeMap::new();
    let mut flattened = Vec::new();
    for (output_type, reduced_io) in output_layer.iter() {
        let [first_addr, second_addr]: [GKRAddress; 2] = reduced_io
            .output
            .clone()
            .try_into()
            .expect("final explicit evaluation extraction expects exactly two outputs");
        let first_poly = gkr_storage.get_ext_poly(first_addr);
        let second_poly = gkr_storage.get_ext_poly(second_addr);
        assert_eq!(first_poly.len(), expected_poly_len);
        assert_eq!(second_poly.len(), expected_poly_len);
        flattened.extend_from_slice(first_poly);
        flattened.extend_from_slice(second_poly);
        final_explicit_evaluations
            .insert(*output_type, [first_poly.to_vec(), second_poly.to_vec()]);
    }

    (final_explicit_evaluations, flattened)
}

fn compute_initial_sumcheck_claims_from_explicit_evaluations_for_test<E: Field>(
    final_explicit_evaluations: &BTreeMap<OutputType, [Vec<E>; 2]>,
    eval_point: &[E],
    worker: &Worker,
) -> [E; 8] {
    let eq_precomputed = make_eq_poly_in_full::<E>(eval_point, worker);
    let eq = eq_precomputed.last().unwrap();

    let mut evals = vec![];
    for key in [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        let explicit_evals = &final_explicit_evaluations[&key];
        for poly in explicit_evals.iter() {
            evals.push(evaluate_ext_poly_with_eq(poly, &eq[..]));
        }
    }

    evals.try_into().unwrap()
}

fn make_decoder_table_host_for_test(
    witness_gen_data: &[cs::gkr_circuits::ExecutorFamilyDecoderData],
) -> Arc<crate::primitives::static_host::StaticPinnedBox<ExecutorFamilyDecoderData>> {
    let data: Vec<_> = witness_gen_data
        .iter()
        .copied()
        .map(ExecutorFamilyDecoderData::from)
        .collect();
    Arc::new(
        alloc_static_pinned_box_from_slice(&data)
            .expect("decoder table should fit in static pinned host memory"),
    )
}

fn make_non_memory_tracing_host_for_test(
    buffer: Vec<NonMemoryOpcodeTracingDataWithTimestamp>,
) -> TracingDataHost<Global> {
    TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(ChunkedTraceHolder {
        chunks: vec![Arc::new(buffer)],
    }))
}

pub(crate) struct BasicUnrolledFixture {
    pub(crate) context: ProverContext,
    pub(crate) circuit_type: CircuitType,
    pub(crate) compiled_circuit: GKRCircuitArtifact<BF>,
    pub(crate) external_challenges: GKRExternalChallenges<BF, E4>,
    pub(crate) whir_schedule: WhirSchedule,
    pub(crate) final_trace_size_log_2: usize,
    pub(crate) gpu_setup_host: Arc<GpuGKRSetupHost>,
    pub(crate) decoder_table_host:
        Arc<crate::primitives::static_host::StaticPinnedBox<ExecutorFamilyDecoderData>>,
    pub(crate) tracing_data_host: TracingDataHost<Global>,
}

struct BasicUnrolledTransfers<'a> {
    setup_transfer: GpuGKRSetupTransfer<'a>,
    decoder_transfer: Option<DecoderTableTransfer<'a>>,
    tracing_data_transfer: TracingDataTransfer<'a, Global>,
}

impl<'a> BasicUnrolledTransfers<'a> {
    fn schedule(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.setup_transfer.schedule_transfer(context)?;
        if let Some(decoder_transfer) = self.decoder_transfer.as_mut() {
            decoder_transfer.schedule_transfer(context)?;
        }
        self.tracing_data_transfer.schedule_transfer(context)
    }
}

pub(crate) struct BasicUnrolledProofFixture {
    pub(crate) base: BasicUnrolledFixture,
    pub(crate) expected_cpu_proof: GKRProof<BF, E4, DefaultTreeConstructor>,
}

impl BasicUnrolledFixture {
    fn create_transfers(&self) -> CudaResult<BasicUnrolledTransfers<'static>> {
        self.create_transfers_for_context(&self.context)
    }

    fn create_transfers_for_context(
        &self,
        context: &ProverContext,
    ) -> CudaResult<BasicUnrolledTransfers<'static>> {
        let setup_transfer = GpuGKRSetupTransfer::new(Arc::clone(&self.gpu_setup_host), context)?;
        let decoder_transfer = if self.compiled_circuit.has_decoder_lookup {
            Some(DecoderTableTransfer::new(
                Arc::clone(&self.decoder_table_host),
                context,
            )?)
        } else {
            None
        };
        let tracing_data_transfer =
            TracingDataTransfer::new(self.tracing_data_host.clone(), context)?;

        Ok(BasicUnrolledTransfers {
            setup_transfer,
            decoder_transfer,
            tracing_data_transfer,
        })
    }

    fn schedule_transfers(&self) -> CudaResult<BasicUnrolledTransfers<'static>> {
        let mut transfers = self.create_transfers()?;
        transfers.schedule(&self.context)?;
        Ok(transfers)
    }

    fn prove(
        &self,
        transfers: BasicUnrolledTransfers<'static>,
        external_pow_challenges: Option<GkrExternalPowChallenges>,
    ) -> CudaResult<GpuGKRProofJob<'static>> {
        let BasicUnrolledTransfers {
            setup_transfer,
            decoder_transfer,
            tracing_data_transfer,
        } = transfers;

        prove::<Global>(
            self.circuit_type,
            self.compiled_circuit.clone(),
            self.external_challenges,
            self.whir_schedule.clone(),
            self.final_trace_size_log_2,
            setup_transfer,
            decoder_transfer,
            None,
            tracing_data_transfer,
            external_pow_challenges,
            &self.context,
        )
    }

    fn schedule_prove(
        &self,
        external_pow_challenges: Option<GkrExternalPowChallenges>,
    ) -> CudaResult<GpuGKRProofJob<'static>> {
        let BasicUnrolledTransfers {
            setup_transfer,
            decoder_transfer,
            tracing_data_transfer,
        } = self.create_transfers()?;

        prove_with_transfer_scheduling::<Global>(
            self.circuit_type,
            self.compiled_circuit.clone(),
            self.external_challenges,
            self.whir_schedule.clone(),
            self.final_trace_size_log_2,
            setup_transfer,
            decoder_transfer,
            None,
            tracing_data_transfer,
            external_pow_challenges,
            &self.context,
        )
    }
}

impl BasicUnrolledProofFixture {
    fn override_pow_challenges(&self) -> GkrExternalPowChallenges {
        GkrExternalPowChallenges {
            whir_pow_nonces: self.expected_cpu_proof.whir_proof.pow_nonces.clone(),
        }
    }

    fn parity_pow_challenges(&self) -> Option<GkrExternalPowChallenges> {
        #[cfg(feature = "deterministic_pow")]
        {
            None
        }
        #[cfg(not(feature = "deterministic_pow"))]
        {
            Some(self.override_pow_challenges())
        }
    }

    fn schedule_prove(
        &self,
        external_pow_challenges: Option<GkrExternalPowChallenges>,
    ) -> CudaResult<GpuGKRProofJob<'static>> {
        self.base.schedule_prove(external_pow_challenges)
    }
}

struct BasicUnrolledFixtureBuildConfig<'a> {
    binary_path: &'a str,
    text_path: &'a str,
    non_determinism_reads: &'a [u32],
    compute_cpu_reference: bool,
}

fn prepare_basic_unrolled_fixture(
    build_config: BasicUnrolledFixtureBuildConfig<'_>,
) -> (
    BasicUnrolledFixture,
    Option<GKRProof<BF, E4, DefaultTreeConstructor>>,
) {
    type CountersT = DelegationsAndFamiliesCounters;

    const TRACE_LEN_LOG2: usize = 24;
    const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
    const FINAL_TRACE_SIZE_LOG_2: usize = 4;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;

    let binary = std::fs::read(test_artifact_path(build_config.binary_path)).unwrap();
    assert_eq!(binary.len() % 4, 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let text_section = std::fs::read(test_artifact_path(build_config.text_path)).unwrap();
    assert_eq!(text_section.len() % 4, 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);
    let cycles_bound = 1 << 20;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter =
        SimpleSnapshotter::<CountersT, { ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(
            cycles_bound,
            state,
        );
    let mut non_determinism =
        QuasiUARTSource::new_with_reads(build_config.non_determinism_reads.to_vec());

    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<_, _, _, BF>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_program_finished);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;
    let mut preprocessing_data = process_binary_into_separate_tables_ext::<
        BF,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
        ],
    );

    let compiled_circuit = compile_unrolled_circuit_state_transition_into_gkr::<BF>(
        &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
        &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        1 << 20,
        TRACE_LEN_LOG2,
    );

    let num_calls =
        counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();
    let mut replay_state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _, BF>(
        &mut replay_state,
        &mut replay_ram,
        &tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    drop(replay_ram);
    drop(snapshotter);
    drop(ram);
    drop(non_determinism);
    drop(tape);
    drop(instructions);
    drop(text_section);
    drop(binary);

    let decoder_table_data = preprocessing_data
        .remove(&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX)
        .expect("fixture must contain preprocessed data for the add/sub family");
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();
    drop(preprocessing_data);

    let memory_argument_alpha =
        E4::from_array_of_base([BF::new(2), BF::new(5), BF::new(42), BF::new(123)]);
    let permutation_argument_additive_part =
        E4::from_array_of_base([BF::new(7), BF::new(11), BF::new(1024), BF::new(8000)]);
    let permutation_argument_linearization_challenges: [E4; NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();
    let external_challenges: GKRExternalChallenges<BF, E4> = GKRExternalChallenges {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    };

    let whir_schedule = WhirSchedule::default_for_tests_80_bits();
    let setup = GKRSetup::construct(
        &TableDriver::new(),
        &decoder_table_data,
        trace_len,
        &compiled_circuit,
    );
    let context = make_test_context(64 * 1024, 1024);
    let gpu_setup_host = Arc::new(
        GpuGKRSetupHost::precompute_from_cpu_setup(
            &setup,
            whir_schedule.base_lde_factor.trailing_zeros(),
            1,
            whir_schedule.cap_size.trailing_zeros(),
            &context,
        )
        .unwrap(),
    );
    let decoder_table_host = make_decoder_table_host_for_test(&witness_gen_data);
    eprintln!("fixture: decoder host ready");

    let expected_cpu_proof = if build_config.compute_cpu_reference {
        let worker = Worker::new_with_num_threads(8);
        let oracle = NonMemoryCircuitOracle {
            inner: &buffer[..],
            decoder_table: &witness_gen_data,
            default_pc_value_in_padding: 4,
        };

        let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BF, _, _, _>(
            &compiled_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
            Global,
        );
        let full_trace = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
            &compiled_circuit,
            add_sub_lui_auipc_mod::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &TableDriver::new(),
            &worker,
            Global,
            Global,
        );
        ensure_memory_trace_consistency(&memory_trace, &full_trace);
        drop(memory_trace);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let setup_commitment = setup.commit(
            &twiddles,
            whir_schedule.base_lde_factor,
            whir_schedule.whir_steps_schedule[0],
            whir_schedule.cap_size,
            trace_len.trailing_zeros() as usize,
            &worker,
        );
        let expected_cpu_proof = prove_configured_with_gkr::<BF, E4, DefaultTreeConstructor>(
            &compiled_circuit,
            &external_challenges,
            full_trace,
            &setup,
            &setup_commitment,
            &twiddles,
            &whir_schedule,
            None,
            trace_len,
            &worker,
        );
        eprintln!("fixture: cpu proof ready");
        Some(expected_cpu_proof)
    } else {
        None
    };

    let tracing_data_host = make_non_memory_tracing_host_for_test(buffer);
    eprintln!("fixture: tracing host ready");

    (
        BasicUnrolledFixture {
            context,
            circuit_type: CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
            )),
            compiled_circuit,
            external_challenges,
            whir_schedule,
            final_trace_size_log_2: FINAL_TRACE_SIZE_LOG_2,
            gpu_setup_host,
            decoder_table_host,
            tracing_data_host,
        },
        expected_cpu_proof,
    )
}

pub(crate) fn prepare_basic_unrolled_proof_fixture() -> BasicUnrolledProofFixture {
    let (base, expected_cpu_proof) =
        prepare_basic_unrolled_fixture(BasicUnrolledFixtureBuildConfig {
            binary_path: "examples/hashed_fibonacci/app.bin",
            text_path: "examples/hashed_fibonacci/app.text",
            non_determinism_reads: &[15, 1],
            compute_cpu_reference: true,
        });
    BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: expected_cpu_proof
            .expect("proof fixture must include the CPU reference proof"),
    }
}

fn prepare_basic_unrolled_profiling_fixture() -> BasicUnrolledFixture {
    let (fixture, expected_cpu_proof) =
        prepare_basic_unrolled_fixture(BasicUnrolledFixtureBuildConfig {
            binary_path: "examples/basic_fibonacci/app.bin",
            text_path: "examples/basic_fibonacci/app.text",
            non_determinism_reads: &[],
            compute_cpu_reference: false,
        });
    assert!(
        expected_cpu_proof.is_none(),
        "profiling fixture must not compute the CPU reference proof",
    );
    fixture
}

fn compute_column_major_lde_from_monomial_form_for_test(
    monomial_coeffs: &[E4],
    twiddles: &Twiddles<BF, Global>,
    lde_factor: usize,
) -> Vec<(Box<[E4]>, BF)> {
    let trace_len_log2 = monomial_coeffs.len().trailing_zeros() as usize;
    let next_root = domain_generator_for_size::<BF>(((1 << trace_len_log2) * lde_factor) as u64);
    let root_powers =
        materialize_powers_serial_starting_with_one::<BF, Global>(next_root, lde_factor);
    let selected_twiddles = &twiddles.forward_twiddles[..(1 << (trace_len_log2 - 1))];

    (0..lde_factor)
        .map(|i| {
            let mut evals = monomial_coeffs.to_vec();
            let offset = root_powers[i];
            if i != 0 {
                fft::distribute_powers_serial(&mut evals[..], BF::ONE, offset);
            }
            bitreverse_enumeration_inplace(&mut evals[..]);
            fft::naive::serial_ct_ntt_bitreversed_to_natural(
                &mut evals[..],
                trace_len_log2 as u32,
                selected_twiddles,
            );
            (evals.into_boxed_slice(), offset)
        })
        .collect()
}

fn compute_column_major_monomial_form_from_main_domain_owned_for_test(
    source_domain: Vec<E4>,
    twiddles: &Twiddles<BF, Global>,
) -> Vec<E4> {
    let trace_len_log2 = source_domain.len().trailing_zeros();
    let mut ifft = source_domain;
    let size_inv = BF::from_u32_unchecked(1 << trace_len_log2)
        .inverse()
        .unwrap();
    fft::naive::cache_friendly_ntt_natural_to_bitreversed(
        &mut ifft[..],
        trace_len_log2,
        &twiddles.inverse_twiddles[..],
    );
    for el in ifft.iter_mut() {
        el.mul_assign_by_base(&size_inv);
    }
    bitreverse_enumeration_inplace(&mut ifft[..]);

    ifft
}

fn build_cpu_recursive_whir_oracle_for_test(
    monomial_coeffs: &[E4],
    twiddles: &Twiddles<BF, Global>,
    lde_factor: usize,
    values_per_leaf: usize,
    tree_cap_size: usize,
    worker: &Worker,
) -> ColumnMajorExtensionOracleForLDE<BF, E4, DefaultTreeConstructor> {
    let cosets =
        compute_column_major_lde_from_monomial_form_for_test(monomial_coeffs, twiddles, lde_factor);
    let trace_len_log2 = monomial_coeffs.len().trailing_zeros() as usize;
    let mut wrapped_cosets = Vec::with_capacity(cosets.len());
    for (column, offset) in cosets.iter() {
        wrapped_cosets.push(ColumnMajorExtensionOracleForCoset {
            values_normal_order: ColumnMajorCosetBoundTracePart {
                column: column.clone().into(),
                offset: *offset,
            },
        });
    }
    let source: Vec<_> = wrapped_cosets
        .iter()
        .map(|coset| vec![&coset.values_normal_order.column[..]])
        .collect();
    let source_ref: Vec<_> = source.iter().map(|entry| &entry[..]).collect();
    let tree =
        <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::construct_from_cosets::<
            E4,
            Global,
        >(
            &source_ref,
            values_per_leaf,
            tree_cap_size,
            true,
            true,
            false,
            worker,
        );

    ColumnMajorExtensionOracleForLDE {
        cosets: wrapped_cosets,
        tree,
        values_per_leaf,
        trace_len_log2,
    }
}

fn fold_monomial_form_for_test(input: &mut Vec<E4>, challenge: E4) {
    assert!(input.len().is_power_of_two());
    let mut buffer = Vec::with_capacity(input.len() / 2);
    for [c0, c1] in input.as_chunks::<2>().0.iter() {
        let mut result = *c1;
        result.mul_assign(&challenge);
        result.add_assign(c0);
        buffer.push(result);
    }
    *input = buffer;
}

fn fold_evaluation_form_for_test(input: &mut Vec<E4>, challenge: E4) {
    assert!(input.len().is_power_of_two());
    let half_len = input.len() / 2;
    let (first_half, second_half) = input.split_at_mut(half_len);
    for (a, b) in first_half.iter_mut().zip(second_half.iter()) {
        let mut t = *b;
        t.sub_assign(a);
        t.mul_assign(&challenge);
        a.add_assign(&t);
    }
    input.truncate(half_len);
}

fn fold_eq_poly_for_test(eq_poly: &mut Vec<E4>, challenge: E4) {
    fold_evaluation_form_for_test(eq_poly, challenge);
}

fn special_three_point_eval_for_test(a: &[E4], b: &[E4]) -> (E4, E4, E4) {
    assert_eq!(a.len(), b.len());
    let half = a.len() / 2;
    let quart = BF::from_u32_unchecked(4).inverse().unwrap();
    let (a_low, a_high) = a.split_at(half);
    let (b_low, b_high) = b.split_at(half);
    let mut f0 = E4::ZERO;
    let mut f1 = E4::ZERO;
    let mut f_half = E4::ZERO;
    for ((a0, a1), (b0, b1)) in a_low
        .iter()
        .zip(a_high.iter())
        .zip(b_low.iter().zip(b_high.iter()))
    {
        let mut t0 = *a0;
        t0.mul_assign(b0);
        f0.add_assign(&t0);

        let mut t1 = *a1;
        t1.mul_assign(b1);
        f1.add_assign(&t1);

        let mut t_half = *a0;
        t_half.add_assign(a1);
        let mut eq_half = *b0;
        eq_half.add_assign(b1);
        t_half.mul_assign(&eq_half);
        f_half.add_assign(&t_half);
    }
    f_half.mul_assign_by_base(&quart);
    (f0, f1, f_half)
}

fn special_lagrange_interpolate_for_test(
    eval_at_0: E4,
    eval_at_1: E4,
    eval_at_random: E4,
    random_point: E4,
) -> [E4; 3] {
    let mut coeffs_for_0 = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_0[1] = E4::ONE;
    coeffs_for_0[1].add_assign(&random_point);
    coeffs_for_0[1].negate();
    coeffs_for_0[0] = random_point;

    let mut coeffs_for_1 = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_1[1] = random_point;
    coeffs_for_1[1].negate();

    let mut coeffs_for_random = [E4::ZERO, E4::ZERO, E4::ONE];
    coeffs_for_random[1] = E4::ONE;
    coeffs_for_random[1].negate();

    let mut dens = [E4::ONE, E4::ONE, E4::ONE];
    let mut t = E4::ZERO;
    t.sub_assign(&E4::ONE);
    dens[0].mul_assign(&t);
    let mut t = E4::ZERO;
    t.sub_assign(&random_point);
    dens[0].mul_assign(&t);

    let mut t = E4::ONE;
    t.sub_assign(&random_point);
    dens[1].mul_assign(&t);

    let mut t = random_point;
    dens[2].mul_assign(&t);
    let mut t = random_point;
    t.sub_assign(&E4::ONE);
    dens[2].mul_assign(&t);

    let mut buffer = [E4::ZERO; 3];
    batch_inverse_inplace(&mut dens, &mut buffer);

    let mut result = [E4::ZERO; 3];
    for (eval, den, coeffs) in [
        (eval_at_0, dens[0], coeffs_for_0),
        (eval_at_1, dens[1], coeffs_for_1),
        (eval_at_random, dens[2], coeffs_for_random),
    ] {
        for (dst, coeff) in result.iter_mut().zip(coeffs.into_iter()) {
            let mut term = coeff;
            term.mul_assign(&den);
            term.mul_assign(&eval);
            dst.add_assign(&term);
        }
    }

    result
}

fn make_pows_for_test(mut el: E4, num_powers: usize) -> Vec<E4> {
    let mut result = Vec::with_capacity(num_powers);
    for _ in 0..num_powers {
        result.push(el);
        el.square();
    }
    result
}

fn update_eq_poly_for_test(
    eq_poly: &mut [E4],
    ood_samples: &[(E4, E4)],
    in_domain_samples: &[(BF, E4)],
) {
    for (point, challenge) in ood_samples.iter() {
        let pows = make_pows_for_test(*point, eq_poly.len().trailing_zeros() as usize);
        let eqs = make_eq_poly_in_full::<E4>(&pows, &Worker::new());
        for (dst, src) in eq_poly.iter_mut().zip(eqs.last().unwrap().iter()) {
            let mut t = *challenge;
            t.mul_assign(src);
            dst.add_assign(&t);
        }
    }
    for (point, challenge) in in_domain_samples.iter() {
        let pows = make_pows_for_test(
            E4::from_base(*point),
            eq_poly.len().trailing_zeros() as usize,
        );
        let eqs = make_eq_poly_in_full::<E4>(&pows, &Worker::new());
        for (dst, src) in eq_poly.iter_mut().zip(eqs.last().unwrap().iter()) {
            let mut t = *challenge;
            t.mul_assign(src);
            dst.add_assign(&t);
        }
    }
}

fn evaluate_monomial_form_for_test(coeffs: &[E4], point: E4) -> E4 {
    let mut result = E4::ZERO;
    let mut current = E4::ONE;
    for coeff in coeffs.iter() {
        let mut term = *coeff;
        term.mul_assign(&current);
        result.add_assign(&term);
        current.mul_assign(&point);
    }
    result
}

fn fold_coset_for_test(
    mut flattened_evals: Vec<E4>,
    num_folding_rounds: usize,
    folding_challenges: &[E4],
    base_root_inv: &BF,
    high_powers_offsets: &[BF],
    two_inv: &BF,
) -> E4 {
    let mut root_inv = *base_root_inv;
    let mut buffer = Vec::with_capacity(flattened_evals.len());
    for folding_step in 0..num_folding_rounds {
        let (src, dst) = if folding_step % 2 == 0 {
            (&flattened_evals[..], &mut buffer)
        } else {
            (&buffer[..], &mut flattened_evals)
        };
        dst.clear();
        for (set_idx, [a, b]) in src.as_chunks::<2>().0.iter().enumerate() {
            let mut t = *a;
            t.sub_assign(b);
            t.mul_assign(&folding_challenges[folding_step]);
            let mut root = root_inv;
            root.mul_assign(&high_powers_offsets[set_idx]);
            t.mul_assign_by_base(&root);
            t.add_assign(a);
            t.add_assign(b);
            t.mul_assign_by_base(two_inv);
            dst.push(t);
        }
        root_inv.square();
    }
    if num_folding_rounds % 2 == 1 {
        buffer[0]
    } else {
        flattened_evals[0]
    }
}

fn assert_recursive_whir_oracle_parity_for_supported_path(
    mem_oracle: &ColumnMajorBaseOracleForLDE<BF, DefaultTreeConstructor>,
    mem_polys_claims: &[E4],
    gpu_mem_trace_holder: &mut TraceHolder<BF>,
    wit_oracle: &ColumnMajorBaseOracleForLDE<BF, DefaultTreeConstructor>,
    wit_polys_claims: &[E4],
    gpu_wit_trace_holder: &mut TraceHolder<BF>,
    setup_oracle: &ColumnMajorBaseOracleForLDE<BF, DefaultTreeConstructor>,
    setup_polys_claims: &[E4],
    gpu_setup_trace_holder: &mut TraceHolder<BF>,
    original_evaluation_point: &[E4],
    original_lde_factor: usize,
    batching_challenge: E4,
    whir_schedule: &WhirSchedule,
    twiddles: &Twiddles<BF, Global>,
    mut transcript_seed: Seed,
    trace_len_log2: usize,
    worker: &Worker,
    context: &ProverContext,
) -> WhirPolyCommitProof<BF, E4, DefaultTreeConstructor> {
    let two_inv = BF::from_u32_unchecked(2).inverse().unwrap();
    let scheduled_transcript_seed = transcript_seed;
    let oracle_refs = [mem_oracle, wit_oracle, setup_oracle];
    let evals_refs = [mem_polys_claims, wit_polys_claims, setup_polys_claims];
    let total_base_oracles = oracle_refs.iter().map(|oracle| oracle.num_columns()).sum();
    let mut challenge_powers = materialize_powers_serial_starting_with_one::<E4, Global>(
        batching_challenge,
        total_base_oracles,
    );
    challenge_powers[1..].fill(E4::ZERO);
    let (base_mem_powers, rest) = challenge_powers.split_at(evals_refs[0].len());
    let (base_wit_powers, base_setup_powers) = rest.split_at(evals_refs[1].len());

    let mut batched_poly_on_main_domain = vec![E4::ZERO; 1 << trace_len_log2];
    for (challenges_set, values_set) in [
        (
            base_mem_powers,
            &oracle_refs[0].cosets[0].original_values_normal_order,
        ),
        (
            base_wit_powers,
            &oracle_refs[1].cosets[0].original_values_normal_order,
        ),
        (
            base_setup_powers,
            &oracle_refs[2].cosets[0].original_values_normal_order,
        ),
    ] {
        for (batch_challenge, base_value) in challenges_set.iter().zip(values_set.iter()) {
            for (dst, src) in batched_poly_on_main_domain
                .iter_mut()
                .zip(base_value.column.iter())
            {
                let mut term = *batch_challenge;
                term.mul_assign_by_base(src);
                dst.add_assign(&term);
            }
        }
    }

    let gpu_batched_poly_on_main_domain = debug_build_initial_batched_main_domain_poly_for_test(
        gpu_mem_trace_holder,
        mem_polys_claims,
        gpu_wit_trace_holder,
        wit_polys_claims,
        gpu_setup_trace_holder,
        setup_polys_claims,
        batching_challenge,
        context,
    )
    .unwrap();
    assert_eq!(gpu_batched_poly_on_main_domain, batched_poly_on_main_domain);
    let mut sumchecked_poly_monomial_form =
        compute_column_major_monomial_form_from_main_domain_owned_for_test(
            batched_poly_on_main_domain,
            twiddles,
        );
    let mut sumchecked_poly_evaluation_form = sumchecked_poly_monomial_form.clone();
    let eval_log2 = sumchecked_poly_evaluation_form.len().trailing_zeros();
    prover::gkr::whir::hypercube_to_monomial::multivariate_coeffs_into_hypercube_evals(
        &mut sumchecked_poly_evaluation_form,
        eval_log2,
    );
    bitreverse_enumeration_inplace(&mut sumchecked_poly_evaluation_form);

    let mut claim = E4::ZERO;
    for (challenges_set, values_set) in [base_mem_powers, base_wit_powers, base_setup_powers]
        .into_iter()
        .zip(evals_refs.into_iter())
    {
        for (challenge, value) in challenges_set.iter().zip(values_set.iter()) {
            let mut term = *value;
            term.mul_assign(challenge);
            claim.add_assign(&term);
        }
    }

    let mut eq_poly = make_eq_poly_in_full::<E4>(original_evaluation_point, worker)
        .pop()
        .unwrap()
        .into_vec();
    let (gpu_pre_eq_evaluation_form, gpu_post_eq_evaluation_form) =
        debug_build_initial_state_snapshots_for_test(
            gpu_mem_trace_holder,
            mem_polys_claims,
            gpu_wit_trace_holder,
            wit_polys_claims,
            gpu_setup_trace_holder,
            setup_polys_claims,
            original_evaluation_point,
            batching_challenge,
            context,
        )
        .unwrap();
    assert_eq!(gpu_pre_eq_evaluation_form, sumchecked_poly_evaluation_form);
    assert_eq!(gpu_post_eq_evaluation_form, sumchecked_poly_evaluation_form);
    let (gpu_batch_challenges, gpu_claim, gpu_monomial_form, gpu_evaluation_form, gpu_eq_poly) =
        debug_build_initial_state_for_test(
            gpu_mem_trace_holder,
            mem_polys_claims,
            gpu_wit_trace_holder,
            wit_polys_claims,
            gpu_setup_trace_holder,
            setup_polys_claims,
            original_evaluation_point,
            batching_challenge,
            context,
        )
        .unwrap();
    assert_eq!(
        gpu_batch_challenges,
        [
            base_mem_powers.to_vec(),
            base_wit_powers.to_vec(),
            base_setup_powers.to_vec(),
        ]
    );
    assert_eq!(gpu_claim, claim);
    assert_eq!(gpu_monomial_form, sumchecked_poly_monomial_form);
    assert_eq!(gpu_evaluation_form, sumchecked_poly_evaluation_form);
    assert_eq!(gpu_eq_poly, eq_poly);
    let mut poly_size_log2 = trace_len_log2;

    let mut whir_steps_schedule = whir_schedule.whir_steps_schedule.iter().copied().peekable();
    let mut whir_queries_schedule = whir_schedule.whir_queries_schedule.iter().copied();
    let mut whir_steps_lde_factors = whir_schedule.whir_steps_lde_factors.iter().copied();
    let mut whir_pow_schedule = whir_schedule.whir_pow_schedule.iter().copied();
    let mut cpu_pre_pow_seeds = Vec::with_capacity(whir_schedule.whir_pow_schedule.len());
    let mut cpu_pow_nonces = Vec::with_capacity(whir_schedule.whir_pow_schedule.len());
    let mut cpu_sumcheck_polys =
        Vec::with_capacity(whir_schedule.whir_steps_schedule.iter().sum::<usize>());
    let mut cpu_recursive_caps = Vec::with_capacity(whir_schedule.whir_steps_lde_factors.len());
    let mut cpu_ood_samples = Vec::with_capacity(whir_schedule.whir_steps_lde_factors.len());
    let mut cpu_recursive_query_indexes =
        Vec::with_capacity(whir_schedule.whir_steps_lde_factors.len());
    let transcript_seed_before_initial_rounds = transcript_seed.clone();

    let num_initial_folding_rounds = whir_steps_schedule.next().unwrap();
    let initial_queries = whir_queries_schedule.next().unwrap();
    let initial_pow_bits = whir_pow_schedule.next().unwrap();
    let mut gpu_initial_fold_state = debug_build_initial_fold_state_for_test(
        gpu_mem_trace_holder,
        mem_polys_claims,
        gpu_wit_trace_holder,
        wit_polys_claims,
        gpu_setup_trace_holder,
        setup_polys_claims,
        original_evaluation_point,
        batching_challenge,
        context,
    )
    .unwrap();
    let mut gpu_monomial_after_initial_rounds = Vec::new();
    let mut folding_challenges_in_round = Vec::with_capacity(num_initial_folding_rounds);
    let mut initial_round_sumcheck_polys = Vec::with_capacity(num_initial_folding_rounds);
    for folding_round in 0..num_initial_folding_rounds {
        let (f0, f1, f_half) =
            special_three_point_eval_for_test(&sumchecked_poly_evaluation_form, &eq_poly);
        let coeffs = special_lagrange_interpolate_for_test(f0, f1, f_half, E4::from_base(two_inv));
        initial_round_sumcheck_polys.push(coeffs);
        cpu_sumcheck_polys.push(coeffs);
        commit_field_els::<BF, E4>(&mut transcript_seed, &coeffs);
        let folding_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        folding_challenges_in_round.push(folding_challenge);
        claim = evaluate_small_univariate_poly::<BF, E4, 3>(&coeffs, &folding_challenge);
        fold_monomial_form_for_test(&mut sumchecked_poly_monomial_form, folding_challenge);
        fold_evaluation_form_for_test(&mut sumchecked_poly_evaluation_form, folding_challenge);
        fold_eq_poly_for_test(&mut eq_poly, folding_challenge);
        let gpu_monomial_after_round = debug_apply_initial_fold_challenge_for_test(
            &mut gpu_initial_fold_state,
            folding_challenge,
            context,
        )
        .unwrap();
        gpu_monomial_after_initial_rounds = gpu_monomial_after_round.clone();
        if gpu_monomial_after_round != sumchecked_poly_monomial_form {
            let first_mismatch = gpu_monomial_after_round
                .iter()
                .zip(sumchecked_poly_monomial_form.iter())
                .enumerate()
                .find(|(_, (gpu, cpu))| gpu != cpu)
                .map(|(idx, (gpu, cpu))| (idx, *gpu, *cpu));
            panic!(
                "initial WHIR monomial fold diverged at round {folding_round}; first_mismatch={first_mismatch:?}"
            );
        }
    }
    poly_size_log2 -= num_initial_folding_rounds;

    let first_lde_factor = whir_steps_lde_factors.next().unwrap();
    let next_folding_steps = *whir_steps_schedule.peek().unwrap();
    let mut cpu_rs_oracle = build_cpu_recursive_whir_oracle_for_test(
        &sumchecked_poly_monomial_form,
        twiddles,
        first_lde_factor,
        1 << next_folding_steps,
        whir_schedule.cap_size,
        worker,
    );
    let mut gpu_rs_oracle = GpuWhirExtensionOracle::from_monomial_coeffs(
        &sumchecked_poly_monomial_form,
        first_lde_factor,
        1 << next_folding_steps,
        whir_schedule.cap_size,
        context,
    )
    .unwrap();
    assert_eq!(
        gpu_rs_oracle.get_tree_cap(),
        <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
            &cpu_rs_oracle.tree,
        )
    );
    cpu_recursive_caps.push(
        <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
            &cpu_rs_oracle.tree,
        ),
    );
    let gpu_initial_round_checkpoint = debug_initial_round_checkpoint_for_test(
        gpu_mem_trace_holder,
        mem_polys_claims,
        gpu_wit_trace_holder,
        wit_polys_claims,
        gpu_setup_trace_holder,
        setup_polys_claims,
        original_evaluation_point,
        original_lde_factor,
        batching_challenge,
        num_initial_folding_rounds,
        first_lde_factor,
        next_folding_steps,
        whir_schedule.cap_size,
        transcript_seed_before_initial_rounds,
        context,
    )
    .unwrap();
    add_whir_commitment_to_transcript(
        &mut transcript_seed,
        &WhirCommitment::<BF, DefaultTreeConstructor> {
            cap: <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &cpu_rs_oracle.tree,
            ),
            _marker: core::marker::PhantomData,
        },
    );

    let ood_point = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
    let ood_value = evaluate_monomial_form_for_test(&sumchecked_poly_monomial_form, ood_point);
    cpu_ood_samples.push(ood_value);
    commit_field_els::<BF, E4>(&mut transcript_seed, &[ood_value]);
    assert_eq!(
        gpu_initial_round_checkpoint.sumcheck_polys, initial_round_sumcheck_polys,
        "initial WHIR sumcheck polys diverged before PoW",
    );
    assert_eq!(
        gpu_initial_round_checkpoint.folding_challenges, folding_challenges_in_round,
        "initial WHIR folding challenges diverged before recursive commitment",
    );
    assert_eq!(
        gpu_initial_round_checkpoint.folded_monomial_form, gpu_monomial_after_initial_rounds,
        "all-in-one initial WHIR checkpoint diverged from the stepwise GPU fold path",
    );
    let gpu_materialized_initial_rs_oracle = GpuWhirExtensionOracle::from_monomial_coeffs(
        &gpu_initial_round_checkpoint.folded_monomial_form,
        first_lde_factor,
        1 << next_folding_steps,
        whir_schedule.cap_size,
        context,
    )
    .unwrap();
    assert_eq!(
        gpu_initial_round_checkpoint.recursive_cap,
        gpu_materialized_initial_rs_oracle.get_tree_cap(),
        "initial recursive WHIR commitment does not match the cap rebuilt from the materialized folded monomial form",
    );
    if gpu_initial_round_checkpoint.folded_monomial_form != sumchecked_poly_monomial_form {
        let first_mismatch = gpu_initial_round_checkpoint
            .folded_monomial_form
            .iter()
            .zip(sumchecked_poly_monomial_form.iter())
            .enumerate()
            .find(|(_, (gpu, cpu))| gpu != cpu)
            .map(|(idx, (gpu, cpu))| (idx, *gpu, *cpu));
        panic!(
            "initial folded WHIR monomial form diverged before recursive commitment; first_mismatch={first_mismatch:?}"
        );
    }
    assert_eq!(
        gpu_initial_round_checkpoint.recursive_cap,
        <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
            &cpu_rs_oracle.tree,
        ),
        "initial recursive WHIR commitment diverged before PoW",
    );
    assert_eq!(
        gpu_initial_round_checkpoint.ood_point, ood_point,
        "initial WHIR OOD point diverged before PoW",
    );
    assert_eq!(
        gpu_initial_round_checkpoint.ood_value, ood_value,
        "initial WHIR OOD value diverged before PoW",
    );
    assert_eq!(
        gpu_initial_round_checkpoint.transcript_seed, transcript_seed,
        "initial WHIR transcript seed diverged before PoW",
    );
    let rs_domain_log2 = trace_len_log2 + original_lde_factor.trailing_zeros() as usize;
    let query_domain_log2 = rs_domain_log2 - num_initial_folding_rounds;
    let query_domain_size = 1u64 << query_domain_log2;
    let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
    let extended_generator = domain_generator_for_size::<BF>(1u64 << rs_domain_log2);
    let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<BF, Global>(
        domain_generator_for_size::<BF>(1u64 << num_initial_folding_rounds)
            .inverse()
            .unwrap(),
        1 << (num_initial_folding_rounds - 1),
    );
    bitreverse_enumeration_inplace(&mut high_powers_offsets);
    let query_index_bits = query_domain_size.trailing_zeros() as usize;
    cpu_pre_pow_seeds.push(transcript_seed);
    let (initial_nonce, mut bit_source) = draw_query_bits(
        &mut transcript_seed,
        initial_queries * query_index_bits,
        initial_pow_bits,
        worker,
    );
    cpu_pow_nonces.push(initial_nonce);
    let delinearization_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
    let mut claim_correction = {
        let mut t = ood_value;
        t.mul_assign(&delinearization_challenge);
        t
    };
    let mut in_domain_samples = Vec::with_capacity(initial_queries);
    for _ in 0..initial_queries {
        let query_index = assemble_query_index(query_index_bits, &mut bit_source);
        let query_point = query_domain_generator.pow(query_index as u32);
        let base_root = extended_generator.pow(query_index as u32);
        let base_root_inv = base_root.inverse().unwrap();
        let mut batched_evals = vec![E4::ZERO; mem_oracle.values_per_leaf];
        for (oracle, batching_challenges) in oracle_refs
            .iter()
            .zip([base_mem_powers, base_wit_powers, base_setup_powers].iter())
        {
            let (_, leaf, _) = oracle.query_for_folded_index(query_index);
            for (dst, src) in batched_evals.iter_mut().zip(leaf.iter()) {
                for (a, b) in src.iter().zip(batching_challenges.iter()) {
                    let mut t = *b;
                    t.mul_assign_by_base(a);
                    dst.add_assign(&t);
                }
            }
        }
        let folded = fold_coset_for_test(
            batched_evals,
            num_initial_folding_rounds,
            &folding_challenges_in_round,
            &base_root_inv,
            &high_powers_offsets,
            &two_inv,
        );
        let mut t = folded;
        t.mul_assign(&delinearization_challenge);
        claim_correction.add_assign(&t);
        in_domain_samples.push((query_point, delinearization_challenge));
    }
    update_eq_poly_for_test(
        &mut eq_poly,
        &[(ood_point, delinearization_challenge)],
        &in_domain_samples,
    );
    claim.add_assign(&claim_correction);

    let num_internal_rounds = whir_schedule.whir_steps_lde_factors.len() - 1;
    for _internal_round in 0..num_internal_rounds {
        let num_folding_steps = whir_steps_schedule.next().unwrap();
        let num_queries = whir_queries_schedule.next().unwrap();
        let pow_bits = whir_pow_schedule.next().unwrap();
        let rs_domain_log2 = poly_size_log2 + cpu_rs_oracle.cosets.len().trailing_zeros() as usize;
        let query_domain_log2 = rs_domain_log2 - num_folding_steps;
        let mut folding_challenges_in_round = Vec::with_capacity(num_folding_steps);
        for _ in 0..num_folding_steps {
            let (f0, f1, f_half) =
                special_three_point_eval_for_test(&sumchecked_poly_evaluation_form, &eq_poly);
            let coeffs =
                special_lagrange_interpolate_for_test(f0, f1, f_half, E4::from_base(two_inv));
            cpu_sumcheck_polys.push(coeffs);
            commit_field_els::<BF, E4>(&mut transcript_seed, &coeffs);
            let folding_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
            folding_challenges_in_round.push(folding_challenge);
            claim = evaluate_small_univariate_poly::<BF, E4, 3>(&coeffs, &folding_challenge);
            fold_monomial_form_for_test(&mut sumchecked_poly_monomial_form, folding_challenge);
            fold_evaluation_form_for_test(&mut sumchecked_poly_evaluation_form, folding_challenge);
            fold_eq_poly_for_test(&mut eq_poly, folding_challenge);
        }
        poly_size_log2 -= num_folding_steps;

        let lde_factor = whir_steps_lde_factors.next().unwrap();
        let next_folding_steps = *whir_steps_schedule.peek().unwrap();
        let next_cpu_oracle = build_cpu_recursive_whir_oracle_for_test(
            &sumchecked_poly_monomial_form,
            twiddles,
            lde_factor,
            1 << next_folding_steps,
            whir_schedule.cap_size,
            worker,
        );
        let next_gpu_oracle = GpuWhirExtensionOracle::from_monomial_coeffs(
            &sumchecked_poly_monomial_form,
            lde_factor,
            1 << next_folding_steps,
            whir_schedule.cap_size,
            context,
        )
        .unwrap();
        assert_eq!(
            next_gpu_oracle.get_tree_cap(),
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &next_cpu_oracle.tree,
            )
        );
        cpu_recursive_caps.push(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &next_cpu_oracle.tree,
            ),
        );

        let ood_point = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        let ood_value = evaluate_monomial_form_for_test(&sumchecked_poly_monomial_form, ood_point);
        cpu_ood_samples.push(ood_value);
        let query_domain_size = 1u64 << query_domain_log2;
        let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
        let extended_generator = domain_generator_for_size::<BF>(1u64 << rs_domain_log2);
        let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<BF, Global>(
            domain_generator_for_size::<BF>(1u64 << num_folding_steps)
                .inverse()
                .unwrap(),
            1 << (num_folding_steps - 1),
        );
        bitreverse_enumeration_inplace(&mut high_powers_offsets);
        let query_index_bits = query_domain_size.trailing_zeros() as usize;
        cpu_pre_pow_seeds.push(transcript_seed);
        let (nonce, mut bit_source) = draw_query_bits(
            &mut transcript_seed,
            num_queries * query_index_bits,
            pow_bits,
            worker,
        );
        cpu_pow_nonces.push(nonce);
        let delinearization_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        let mut claim_correction = {
            let mut t = ood_value;
            t.mul_assign(&delinearization_challenge);
            t
        };
        let mut in_domain_samples = Vec::with_capacity(num_queries);
        let mut recursive_round_query_indexes = Vec::with_capacity(num_queries);
        for _ in 0..num_queries {
            let query_index = assemble_query_index(query_index_bits, &mut bit_source);
            recursive_round_query_indexes.push(query_index);
            let (_, cpu_values, cpu_query) = cpu_rs_oracle.query_for_folded_index(query_index);
            let (_, gpu_values, gpu_query) = gpu_rs_oracle
                .query_for_folded_index(query_index, context)
                .unwrap();
            assert_eq!(gpu_values, cpu_values, "recursive query values diverged");
            assert_eq!(gpu_query.index, cpu_query.index);
            assert_eq!(
                gpu_query.leaf_values_concatenated,
                cpu_query.leaf_values_concatenated
            );
            assert_eq!(gpu_query.path, cpu_query.path);

            let query_point = query_domain_generator.pow(query_index as u32);
            let base_root = extended_generator.pow(query_index as u32);
            let base_root_inv = base_root.inverse().unwrap();
            let folded = fold_coset_for_test(
                cpu_values,
                num_folding_steps,
                &folding_challenges_in_round,
                &base_root_inv,
                &high_powers_offsets,
                &two_inv,
            );
            let mut t = folded;
            t.mul_assign(&delinearization_challenge);
            claim_correction.add_assign(&t);
            in_domain_samples.push((query_point, delinearization_challenge));
        }
        update_eq_poly_for_test(
            &mut eq_poly,
            &[(ood_point, delinearization_challenge)],
            &in_domain_samples,
        );
        cpu_recursive_query_indexes.push(recursive_round_query_indexes);
        claim.add_assign(&claim_correction);

        cpu_rs_oracle = next_cpu_oracle;
        gpu_rs_oracle = next_gpu_oracle;
    }

    let final_folding_steps = whir_steps_schedule.next().unwrap();
    let final_queries = whir_queries_schedule.next().unwrap();
    let final_pow_bits = whir_pow_schedule.next().unwrap();
    let rs_domain_log2 = poly_size_log2 + cpu_rs_oracle.cosets.len().trailing_zeros() as usize;
    let query_domain_log2 = rs_domain_log2 - final_folding_steps;
    let mut folding_challenges_in_round = Vec::with_capacity(final_folding_steps);
    for _ in 0..final_folding_steps {
        let (f0, f1, f_half) =
            special_three_point_eval_for_test(&sumchecked_poly_evaluation_form, &eq_poly);
        let coeffs = special_lagrange_interpolate_for_test(f0, f1, f_half, E4::from_base(two_inv));
        cpu_sumcheck_polys.push(coeffs);
        commit_field_els::<BF, E4>(&mut transcript_seed, &coeffs);
        let folding_challenge = draw_random_field_els::<BF, E4>(&mut transcript_seed, 1)[0];
        folding_challenges_in_round.push(folding_challenge);
        claim = evaluate_small_univariate_poly::<BF, E4, 3>(&coeffs, &folding_challenge);
        fold_monomial_form_for_test(&mut sumchecked_poly_monomial_form, folding_challenge);
        fold_evaluation_form_for_test(&mut sumchecked_poly_evaluation_form, folding_challenge);
        fold_eq_poly_for_test(&mut eq_poly, folding_challenge);
    }
    poly_size_log2 -= final_folding_steps;
    let query_domain_size = 1u64 << query_domain_log2;
    let query_domain_generator = domain_generator_for_size::<BF>(query_domain_size);
    let extended_generator = domain_generator_for_size::<BF>(1u64 << rs_domain_log2);
    let mut high_powers_offsets = materialize_powers_serial_starting_with_one::<BF, Global>(
        domain_generator_for_size::<BF>(1u64 << final_folding_steps)
            .inverse()
            .unwrap(),
        1 << (final_folding_steps - 1),
    );
    bitreverse_enumeration_inplace(&mut high_powers_offsets);
    let query_index_bits = query_domain_size.trailing_zeros() as usize;
    cpu_pre_pow_seeds.push(transcript_seed);
    let (final_nonce, mut bit_source) = draw_query_bits(
        &mut transcript_seed,
        final_queries * query_index_bits,
        final_pow_bits,
        worker,
    );
    cpu_pow_nonces.push(final_nonce);
    let mut final_round_query_indexes = Vec::with_capacity(final_queries);
    for _ in 0..final_queries {
        let query_index = assemble_query_index(query_index_bits, &mut bit_source);
        final_round_query_indexes.push(query_index);
        let (_, cpu_values, cpu_query) = cpu_rs_oracle.query_for_folded_index(query_index);
        let (_, gpu_values, gpu_query) = gpu_rs_oracle
            .query_for_folded_index(query_index, context)
            .unwrap();
        assert_eq!(
            gpu_values, cpu_values,
            "final recursive query values diverged"
        );
        assert_eq!(gpu_query.index, cpu_query.index);
        assert_eq!(
            gpu_query.leaf_values_concatenated,
            cpu_query.leaf_values_concatenated
        );
        assert_eq!(gpu_query.path, cpu_query.path);

        let query_point = query_domain_generator.pow(query_index as u32);
        let base_root = extended_generator.pow(query_index as u32);
        let base_root_inv = base_root.inverse().unwrap();
        let folded = fold_coset_for_test(
            cpu_values,
            final_folding_steps,
            &folding_challenges_in_round,
            &base_root_inv,
            &high_powers_offsets,
            &two_inv,
        );
        assert_eq!(
            folded,
            evaluate_monomial_form_for_test(
                &sumchecked_poly_monomial_form,
                E4::from_base(query_point)
            )
        );
    }
    cpu_recursive_query_indexes.push(final_round_query_indexes);
    let mem_polys_claims_for_schedule = mem_polys_claims.to_vec();
    let wit_polys_claims_for_schedule = wit_polys_claims.to_vec();
    let setup_polys_claims_for_schedule = setup_polys_claims.to_vec();
    let original_evaluation_point_for_schedule = original_evaluation_point.to_vec();
    let memory_base_caps_keepalive = gpu_mem_trace_holder.take_tree_caps_host();
    let witness_base_caps_keepalive = gpu_wit_trace_holder.take_tree_caps_host();
    let setup_base_caps_keepalive = gpu_setup_trace_holder.take_tree_caps_host();
    let scheduled_gpu_whir = schedule_gpu_whir_fold_with_sources(
        gpu_mem_trace_holder,
        memory_base_caps_keepalive,
        move |dst| dst.copy_from_slice(&mem_polys_claims_for_schedule),
        gpu_wit_trace_holder,
        witness_base_caps_keepalive,
        move |dst| dst.copy_from_slice(&wit_polys_claims_for_schedule),
        gpu_setup_trace_holder,
        setup_base_caps_keepalive,
        move |dst| dst.copy_from_slice(&setup_polys_claims_for_schedule),
        original_evaluation_point_for_schedule.len(),
        move |dst| dst.copy_from_slice(&original_evaluation_point_for_schedule),
        original_lde_factor,
        move || batching_challenge,
        whir_schedule.whir_steps_schedule.clone(),
        whir_schedule.whir_queries_schedule.clone(),
        whir_schedule.whir_steps_lde_factors.clone(),
        whir_schedule.whir_pow_schedule.clone(),
        move || scheduled_transcript_seed,
        whir_schedule.cap_size,
        trace_len_log2,
        Some(cpu_pow_nonces.clone()),
        context,
    )
    .unwrap();
    let scheduled_shared_state = scheduled_gpu_whir.shared_state_handle();
    let scheduled_gpu_whir_proof = scheduled_gpu_whir.wait(context).unwrap();
    let gpu_pre_pow_seeds = clone_scheduled_whir_pre_pow_seeds(&scheduled_shared_state);
    let scheduled_recursive_caps = scheduled_gpu_whir_proof
        .intermediate_whir_oracles
        .iter()
        .map(|oracle| oracle.commitment.cap.clone())
        .collect::<Vec<_>>();
    let scheduled_recursive_query_indexes = scheduled_gpu_whir_proof
        .intermediate_whir_oracles
        .iter()
        .map(|oracle| {
            oracle
                .queries
                .iter()
                .map(|query| query.index)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    // Per-round assertions in workflow order to find first divergence.
    // Sumcheck polys: one per folding step. whir_steps_schedule = [1, 4, 4, 4, 4, 4]
    // OOD samples: one per recursive round (rounds 1..N)
    // Recursive caps: one per recursive round
    // Pre-PoW seeds: one per round
    {
        let mut step_offset = 0;
        for (round_idx, &num_steps) in whir_schedule.whir_steps_schedule.iter().enumerate() {
            for step in 0..num_steps {
                let idx = step_offset + step;
                assert_eq!(
                    scheduled_gpu_whir_proof.sumcheck_polys[idx], cpu_sumcheck_polys[idx],
                    "sumcheck poly diverged at round {round_idx} step {step} (global idx {idx})"
                );
            }
            step_offset += num_steps;
            // After each round's sumcheck: check OOD (except base round)
            if round_idx > 0 {
                let ood_idx = round_idx - 1;
                if ood_idx < cpu_ood_samples.len() {
                    assert_eq!(
                        scheduled_gpu_whir_proof.ood_samples[ood_idx], cpu_ood_samples[ood_idx],
                        "OOD sample diverged at round {round_idx} (ood_idx {ood_idx})"
                    );
                }
            }
            // Check recursive cap
            if round_idx > 0 {
                let cap_idx = round_idx - 1;
                if cap_idx < cpu_recursive_caps.len() {
                    assert_eq!(
                        scheduled_recursive_caps[cap_idx], cpu_recursive_caps[cap_idx],
                        "recursive cap diverged at round {round_idx} (cap_idx {cap_idx})"
                    );
                }
            }
            // Check pre-PoW seed
            if round_idx < gpu_pre_pow_seeds.len() {
                assert_eq!(
                    gpu_pre_pow_seeds[round_idx], cpu_pre_pow_seeds[round_idx],
                    "pre-PoW seed diverged at round {round_idx}"
                );
            }
            // Check PoW nonce
            if round_idx < scheduled_gpu_whir_proof.pow_nonces.len() {
                assert_eq!(
                    scheduled_gpu_whir_proof.pow_nonces[round_idx], cpu_pow_nonces[round_idx],
                    "PoW nonce diverged at round {round_idx}"
                );
            }
        }
    }
    let _ = claim;
    scheduled_gpu_whir_proof
}

pub(crate) struct BasicUnrolledAsyncBackwardFixture {
    pub(crate) context: ProverContext,
    pub(crate) compiled_circuit: GKRCircuitArtifact<BF>,
    pub(crate) gpu_backward_state: GpuGKRDimensionReducingBackwardState<BF, E4>,
    pub(crate) initial_output_layer_idx: usize,
    pub(crate) top_layer_claims: BTreeMap<GKRAddress, E4>,
    pub(crate) evaluation_point: Vec<E4>,
    pub(crate) seed: Seed,
    pub(crate) batching_challenge: E4,
    pub(crate) lookup_additive_part: E4,
    pub(crate) constraints_batch_challenge: E4,
    pub(crate) expected_proof_layers: usize,
}

fn build_basic_unrolled_async_backward_fixture_from_base(
    base: &BasicUnrolledFixture,
) -> BasicUnrolledAsyncBackwardFixture {
    let worker = Worker::new_with_num_threads(8);
    let context = make_test_context(64 * 1024, 1024);
    let mut transfers = base.create_transfers_for_context(&context).unwrap();
    transfers.schedule(&context).unwrap();
    context.get_h2d_stream().synchronize().unwrap();
    eprintln!("async-backward-from-base: transfers ready");

    let mut stage1_output = GpuGKRStage1Output::generate(
        base.circuit_type,
        &base.compiled_circuit,
        &transfers.setup_transfer,
        transfers
            .decoder_transfer
            .as_ref()
            .map(|transfer| &transfer.data_device[..]),
        &transfers.tracing_data_transfer.data_device,
        &context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    eprintln!("async-backward-from-base: stage1 ready");

    let mut lookup_challenges_host = unsafe { context.alloc_host_uninit_slice(3) };
    let mut transcript_input = vec![];
    base.external_challenges
        .flatten_into_buffer(&mut transcript_input);
    flatten_merkle_caps_iter_into(
        transfers
            .setup_transfer
            .trace_holder
            .get_tree_caps()
            .into_iter(),
        &mut transcript_input,
    );
    flatten_merkle_caps_iter_into(
        stage1_output
            .memory_trace_holder
            .get_tree_caps()
            .into_iter(),
        &mut transcript_input,
    );
    flatten_merkle_caps_iter_into(
        stage1_output
            .witness_trace_holder
            .get_tree_caps()
            .into_iter(),
        &mut transcript_input,
    );
    let mut seed = Transcript::commit_initial(&transcript_input);
    let challenges: Vec<E4> = draw_random_field_els::<BF, E4>(&mut seed, 3);
    let [lookup_alpha, lookup_additive_part, constraints_batch_challenge] =
        challenges.try_into().unwrap();
    unsafe {
        lookup_challenges_host
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(&[
                lookup_alpha,
                lookup_additive_part,
                constraints_batch_challenge,
            ]);
    }
    let mut gpu_forward_setup = transfers
        .setup_transfer
        .schedule_forward_setup(&base.compiled_circuit, lookup_challenges_host, &context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    eprintln!("async-backward-from-base: forward setup ready");

    let gpu_forward_output = schedule_forward_pass(
        &transfers.setup_transfer,
        &mut stage1_output,
        &mut gpu_forward_setup,
        &base.compiled_circuit,
        &base.external_challenges,
        base.final_trace_size_log_2,
        &context,
    )
    .unwrap();
    eprintln!("async-backward-from-base: forward pass scheduled");
    let gpu_transcript_handoff = gpu_forward_output
        .schedule_transcript_handoff(&context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    eprintln!("async-backward-from-base: transcript handoff ready");
    let gpu_final_explicit_evaluations = gpu_transcript_handoff.final_explicit_evaluations();
    let gpu_evals_flattened = gpu_transcript_handoff.flattened_transcript_evaluations();

    commit_field_els::<BF, E4>(&mut seed, &gpu_evals_flattened);
    let mut challenges =
        draw_random_field_els::<BF, E4>(&mut seed, base.final_trace_size_log_2 + 1);
    let batching_challenge = challenges.pop().unwrap();
    let evaluation_point = challenges;

    let [claim_readset, claim_writeset, claim_rangechecknum, claim_rangecheckden, claim_timechecknum, claim_timecheckden, claim_lookupnum, claim_lookupden] =
        compute_initial_sumcheck_claims_from_explicit_evaluations_for_test(
            &gpu_final_explicit_evaluations,
            &evaluation_point,
            &worker,
        );

    let output_layer_for_sumcheck = gpu_forward_output
        .dimension_reducing_inputs
        .get(&gpu_forward_output.initial_layer_for_sumcheck)
        .unwrap();
    let mut top_layer_claims = BTreeMap::new();
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::PermutationProduct].output[0],
        claim_readset,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::PermutationProduct].output[1],
        claim_writeset,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::Lookup16Bits].output[0],
        claim_rangechecknum,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::Lookup16Bits].output[1],
        claim_rangecheckden,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::LookupTimestamps].output[0],
        claim_timechecknum,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::LookupTimestamps].output[1],
        claim_timecheckden,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::GenericLookup].output[0],
        claim_lookupnum,
    );
    top_layer_claims.insert(
        output_layer_for_sumcheck[&OutputType::GenericLookup].output[1],
        claim_lookupden,
    );

    let expected_proof_layers =
        gpu_forward_output.dimension_reducing_inputs.len() + base.compiled_circuit.layers.len();
    let initial_output_layer_idx = gpu_forward_output.initial_layer_for_sumcheck + 1;

    drop(gpu_transcript_handoff);
    drop(gpu_forward_setup);
    drop(transfers);
    drop(stage1_output);

    BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit: base.compiled_circuit.clone(),
        gpu_backward_state: gpu_forward_output.into_dimension_reducing_backward_state(),
        initial_output_layer_idx,
        top_layer_claims,
        evaluation_point,
        seed,
        batching_challenge,
        lookup_additive_part,
        constraints_batch_challenge,
        expected_proof_layers,
    }
}

pub(crate) fn prepare_basic_unrolled_async_backward_fixture(
    _final_trace_size_log_2: usize,
) -> BasicUnrolledAsyncBackwardFixture {
    let (base, expected_cpu_proof) =
        prepare_basic_unrolled_fixture(BasicUnrolledFixtureBuildConfig {
            binary_path: "examples/hashed_fibonacci/app.bin",
            text_path: "examples/hashed_fibonacci/app.text",
            non_determinism_reads: &[15, 1],
            compute_cpu_reference: false,
        });
    assert!(
        expected_cpu_proof.is_none(),
        "async backward fixture must not compute the CPU reference proof",
    );
    build_basic_unrolled_async_backward_fixture_from_base(&base)
}

fn expected_dimension_reducing_kernel_specs_for_test<E: Field>(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    batch_challenge_base: E,
) -> Vec<(GKRInputs, Vec<E>)> {
    let mut current_batch_challenge = E::ONE;
    let mut get_challenge = || {
        let challenge = current_batch_challenge;
        current_batch_challenge.mul_assign(&batch_challenge_base);
        challenge
    };

    let mut specs = Vec::new();
    for (output_type, reduced_io) in layer.iter() {
        match *output_type {
            OutputType::PermutationProduct => {
                for (input, output) in reduced_io.inputs.iter().zip(reduced_io.output.iter()) {
                    specs.push((
                        GKRInputs {
                            inputs_in_base: Vec::new(),
                            inputs_in_extension: vec![*input],
                            outputs_in_base: Vec::new(),
                            outputs_in_extension: vec![*output],
                        },
                        vec![get_challenge()],
                    ));
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                specs.push((
                    GKRInputs {
                        inputs_in_base: Vec::new(),
                        inputs_in_extension: reduced_io.inputs.clone(),
                        outputs_in_base: Vec::new(),
                        outputs_in_extension: reduced_io.output.clone(),
                    },
                    vec![get_challenge(), get_challenge()],
                ));
            }
        }
    }

    specs
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExpectedMainLayerConstraintMetadata<E> {
    pub(crate) quadratic_terms:
        Vec<crate::prover::gkr::backward::GpuGKRMainLayerConstraintQuadraticTerm<E>>,
    pub(crate) linear_terms:
        Vec<crate::prover::gkr::backward::GpuGKRMainLayerConstraintLinearTerm<E>>,
    pub(crate) constant_offset: E,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExpectedMainLayerKernelSpec<E> {
    pub(crate) kind: GpuGKRMainLayerKernelKind,
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenges: Vec<E>,
    pub(crate) auxiliary_challenge: E,
    pub(crate) constraint_metadata: Option<ExpectedMainLayerConstraintMetadata<E>>,
}

pub(crate) fn expected_main_layer_kernel_specs_for_test<E: Field + FieldExtension<BF>>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    storage: &GpuGKRStorage<BF, E>,
    batch_challenge_base: E,
    lookup_additive_challenge: E,
    constraint_batch_challenge: E,
    num_base_layer_memory_polys: usize,
    num_base_layer_witness_polys: usize,
) -> Vec<ExpectedMainLayerKernelSpec<E>> {
    let mut current_batch_challenge = E::ONE;
    let mut get_challenge = || {
        let challenge = current_batch_challenge;
        current_batch_challenge.mul_assign(&batch_challenge_base);
        challenge
    };

    let mut specs = Vec::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        match &gate.enforced_relation {
            NoFieldGKRRelation::Copy { input, output } => {
                let batch_challenges = vec![get_challenge()];
                if storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(input)
                {
                    let relation = BaseFieldCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    specs.push(ExpectedMainLayerKernelSpec {
                        kind: GpuGKRMainLayerKernelKind::BaseCopy,
                        inputs: <BaseFieldCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenges,
                        auxiliary_challenge: E::ZERO,
                        constraint_metadata: None,
                    });
                } else {
                    let relation = ExtensionCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    specs.push(ExpectedMainLayerKernelSpec {
                        kind: GpuGKRMainLayerKernelKind::ExtCopy,
                        inputs: <ExtensionCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenges,
                        auxiliary_challenge: E::ZERO,
                        constraint_metadata: None,
                    });
                }
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let relation = SameSizeProductGKRRelation {
                    inputs: *input,
                    output: *output,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::Product,
                    inputs: <SameSizeProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenges: vec![get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let relation = MaskIntoIdentityProductGKRRelation {
                    input: *input,
                    mask: *mask,
                    output: *output,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::MaskIdentity,
                    inputs:
                        <MaskIntoIdentityProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenges: vec![get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let relation = LookupPairGKRRelation {
                    inputs: *input,
                    outputs: *output,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupPair,
                    inputs: <LookupPairGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: E::ZERO,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let relation = LookupBasePairGKRRelation::<BF, E> {
                    inputs: *input,
                    outputs: *output,
                    lookup_additive_challenge,
                    _marker: core::marker::PhantomData,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupBasePair,
                    inputs:
                        <LookupBasePairGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: lookup_additive_challenge,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseMinusMultiplicityByBaseGKRRelation::<BF, E> {
                    input: *input,
                    setup: *setup,
                    outputs: *output,
                    lookup_additive_challenge,
                    _marker: core::marker::PhantomData,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
                    inputs:
                        <LookupBaseMinusMultiplicityByBaseGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: lookup_additive_challenge,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedBaseGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge,
                    _marker: core::marker::PhantomData,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
                    inputs: <LookupRationalPairWithUnbalancedBaseGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: lookup_additive_challenge,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseExtMinusBaseExtGKRRelation::<BF, E> {
                    nums: [input[0], setup[0]],
                    dens: [input[1], setup[1]],
                    outputs: *output,
                    lookup_additive_challenge,
                    _marker: core::marker::PhantomData,
                };
                specs.push(ExpectedMainLayerKernelSpec {
                    kind: GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
                    inputs: <LookupBaseExtMinusBaseExtGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenges: vec![get_challenge(), get_challenge()],
                    auxiliary_challenge: lookup_additive_challenge,
                    constraint_metadata: None,
                });
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input } => {
                let relation = BatchConstraintEvalGKRRelation::<BF, E>::new(
                    input,
                    num_base_layer_memory_polys,
                    num_base_layer_witness_polys,
                    constraint_batch_challenge,
                );
                specs.push(
                    ExpectedMainLayerKernelSpec {
                        kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
                        inputs: <BatchConstraintEvalGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                        batch_challenges: vec![get_challenge()],
                        auxiliary_challenge: E::ZERO,
                        constraint_metadata: Some(ExpectedMainLayerConstraintMetadata {
                            quadratic_terms: relation
                                .kernel
                                .quadratic_parts
                                .iter()
                                .map(
                                    |((lhs, rhs), challenge)| crate::prover::gkr::backward::GpuGKRMainLayerConstraintQuadraticTerm {
                                        lhs: *lhs as u32,
                                        rhs: *rhs as u32,
                                        challenge: *challenge,
                                    },
                                )
                                .collect(),
                            linear_terms: relation
                                .kernel
                                .linear_parts
                                .iter()
                                .map(
                                    |(input, challenge)| crate::prover::gkr::backward::GpuGKRMainLayerConstraintLinearTerm {
                                        input: *input as u32,
                                        challenge: *challenge,
                                    },
                                )
                                .collect(),
                            constant_offset: relation.kernel.constant_offset,
                        }),
                    },
                );
            }
            NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. }
            | NoFieldGKRRelation::MaterializeSingleLookupInput { .. }
            | NoFieldGKRRelation::MaterializedVectorLookupInput { .. }
            | NoFieldGKRRelation::LookupPairFromBaseInputs { .. }
            | NoFieldGKRRelation::LookupPairFromVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { .. }
            | NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { .. }
            | NoFieldGKRRelation::LinearBaseFieldRelation { .. }
            | NoFieldGKRRelation::MaxQuadratic { .. } => {
                panic!(
                    "unsupported main-layer relation in test: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    specs
}

fn assert_dimension_reducing_layer_plan_for_test<E: Field + std::fmt::Debug>(
    layer_plan: &GpuGKRDimensionReducingSumcheckLayerPlan<BF, E>,
    storage: &GpuGKRStorage<BF, E>,
    expected_specs: &[(GKRInputs, Vec<E>)],
) {
    assert_eq!(layer_plan.kernel_plans().len(), expected_specs.len());
    assert_eq!(layer_plan.round0_descriptors().len(), expected_specs.len());

    for (idx, (expected_inputs, expected_batch_challenges)) in expected_specs.iter().enumerate() {
        let kernel_plan = &layer_plan.kernel_plans()[idx];
        assert_eq!(&kernel_plan.inputs, expected_inputs);
        assert_eq!(&kernel_plan.batch_challenges, expected_batch_challenges);

        let round0 = &layer_plan.round0_descriptors()[idx];
        let ext_inputs_accessor = round0.host.extension_field_inputs.get_accessor();
        let ext_inputs = unsafe { ext_inputs_accessor.get() };
        let ext_outputs_accessor = round0.host.extension_field_outputs.get_accessor();
        let ext_outputs = unsafe { ext_outputs_accessor.get() };
        let base_inputs_accessor = round0.host.base_field_inputs.get_accessor();
        let base_inputs = unsafe { base_inputs_accessor.get() };
        let base_outputs_accessor = round0.host.base_field_outputs.get_accessor();
        let base_outputs = unsafe { base_outputs_accessor.get() };

        assert!(base_inputs.is_empty());
        assert!(base_outputs.is_empty());
        assert_eq!(ext_inputs.len(), expected_inputs.inputs_in_extension.len());
        assert_eq!(
            ext_outputs.len(),
            expected_inputs.outputs_in_extension.len()
        );

        for (descriptor, address) in ext_inputs
            .iter()
            .zip(expected_inputs.inputs_in_extension.iter())
        {
            let poly = storage.get_ext_poly(*address);
            assert_eq!(descriptor.start, poly.as_ptr());
            assert_eq!(descriptor.next_layer_size, poly.len() / 2);
        }
        for (descriptor, address) in ext_outputs
            .iter()
            .zip(expected_inputs.outputs_in_extension.iter())
        {
            let poly = storage.get_ext_poly(*address);
            assert_eq!(descriptor.start, poly.as_ptr());
            assert_eq!(descriptor.next_layer_size, poly.len() / 2);
        }
    }
}

fn assert_main_layer_plan_for_test<E: Field + std::fmt::Debug>(
    layer_plan: &GpuGKRMainLayerSumcheckLayerPlan<E>,
    storage: &GpuGKRStorage<BF, E>,
    expected_specs: &[ExpectedMainLayerKernelSpec<E>],
) {
    assert_eq!(layer_plan.kernel_plans().len(), expected_specs.len());
    assert_eq!(layer_plan.round0_descriptors().len(), expected_specs.len());

    for (idx, expected) in expected_specs.iter().enumerate() {
        let kernel_plan = &layer_plan.kernel_plans()[idx];
        assert_eq!(kernel_plan.kind, expected.kind);
        assert_eq!(kernel_plan.inputs, expected.inputs);
        assert_eq!(kernel_plan.batch_challenges, expected.batch_challenges);
        assert_eq!(
            kernel_plan.auxiliary_challenge_summary(),
            Some(expected.auxiliary_challenge)
        );
        assert_eq!(
            kernel_plan.constraint_metadata_summary(),
            expected.constraint_metadata.as_ref().map(|metadata| {
                (
                    metadata.quadratic_terms.len(),
                    metadata.linear_terms.len(),
                    metadata.constant_offset,
                )
            })
        );

        let round0 = &layer_plan.round0_descriptors()[idx];
        let base_inputs_accessor = round0.host.base_field_inputs.get_accessor();
        let base_inputs = unsafe { base_inputs_accessor.get() };
        let ext_inputs_accessor = round0.host.extension_field_inputs.get_accessor();
        let ext_inputs = unsafe { ext_inputs_accessor.get() };
        let base_outputs_accessor = round0.host.base_field_outputs.get_accessor();
        let base_outputs = unsafe { base_outputs_accessor.get() };
        let ext_outputs_accessor = round0.host.extension_field_outputs.get_accessor();
        let ext_outputs = unsafe { ext_outputs_accessor.get() };

        assert_eq!(base_inputs.len(), expected.inputs.inputs_in_base.len());
        assert_eq!(ext_inputs.len(), expected.inputs.inputs_in_extension.len());
        assert_eq!(base_outputs.len(), expected.inputs.outputs_in_base.len());
        assert_eq!(
            ext_outputs.len(),
            expected.inputs.outputs_in_extension.len()
        );

        for (descriptor, address) in base_inputs
            .iter()
            .zip(expected.inputs.inputs_in_base.iter())
        {
            if *address == GKRAddress::placeholder() {
                assert!(descriptor.start.is_null());
                assert_eq!(descriptor.next_layer_size, 0);
                continue;
            }
            let poly = storage.get_base_layer(*address);
            assert_eq!(
                descriptor.start,
                poly.as_ptr(),
                "kernel {idx} base input {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 2,
                "kernel {idx} base input {:?} size mismatch",
                address
            );
        }
        for (descriptor, address) in ext_inputs
            .iter()
            .zip(expected.inputs.inputs_in_extension.iter())
        {
            if *address == GKRAddress::placeholder() {
                assert!(descriptor.start.is_null());
                assert_eq!(descriptor.next_layer_size, 0);
                continue;
            }
            let poly = storage.get_ext_poly(*address);
            assert_eq!(
                descriptor.start,
                poly.as_ptr(),
                "kernel {idx} ext input {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 2,
                "kernel {idx} ext input {:?} size mismatch",
                address
            );
        }
        for (descriptor, address) in base_outputs
            .iter()
            .zip(expected.inputs.outputs_in_base.iter())
        {
            let poly = storage.get_base_layer(*address);
            assert_eq!(
                descriptor.start,
                poly.as_ptr(),
                "kernel {idx} base output {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 2,
                "kernel {idx} base output {:?} size mismatch",
                address
            );
        }
        for (descriptor, address) in ext_outputs
            .iter()
            .zip(expected.inputs.outputs_in_extension.iter())
        {
            let poly = storage.get_ext_poly(*address);
            assert_eq!(
                descriptor.start,
                poly.as_ptr(),
                "kernel {idx} ext output {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 2,
                "kernel {idx} ext output {:?} size mismatch",
                address
            );
        }
    }
}

fn assert_sumcheck_intermediate_values_eq_for_test<F: PrimeField, E: FieldExtension<F> + Field>(
    actual: &prover::gkr::prover::SumcheckIntermediateProofValues<F, E>,
    expected: &prover::gkr::prover::SumcheckIntermediateProofValues<F, E>,
) {
    assert_sumcheck_intermediate_values_eq_for_test_with_layer(actual, expected, usize::MAX);
}

fn assert_sumcheck_intermediate_values_eq_for_test_with_layer<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    actual: &prover::gkr::prover::SumcheckIntermediateProofValues<F, E>,
    expected: &prover::gkr::prover::SumcheckIntermediateProofValues<F, E>,
    layer_idx: usize,
) {
    assert_eq!(
        actual.sumcheck_num_rounds, expected.sumcheck_num_rounds,
        "layer {layer_idx}: sumcheck_num_rounds mismatch"
    );
    assert_eq!(
        actual.internal_round_coefficients.len(),
        expected.internal_round_coefficients.len(),
        "layer {layer_idx}: internal_round_coefficients length mismatch"
    );
    for (round_idx, (actual_coeffs, expected_coeffs)) in actual
        .internal_round_coefficients
        .iter()
        .zip(expected.internal_round_coefficients.iter())
        .enumerate()
    {
        for (coeff_idx, (&actual_coeff, &expected_coeff)) in
            actual_coeffs.iter().zip(expected_coeffs.iter()).enumerate()
        {
            assert_eq!(
                actual_coeff, expected_coeff,
                "layer {layer_idx}: internal_round_coefficients mismatch at round {round_idx}, coeff {coeff_idx}"
            );
        }
    }
    assert_eq!(
        actual.final_step_evaluations, expected.final_step_evaluations,
        "layer {layer_idx}: final_step_evaluations mismatch"
    );
}

fn assert_layer_points_eq_for_test<E: Field + std::fmt::Debug>(
    actual: &BTreeMap<usize, Vec<E>>,
    expected: &BTreeMap<usize, Vec<E>>,
) {
    assert_eq!(
        actual.len(),
        expected.len(),
        "layer-point map sizes differ: actual keys {:?}, expected keys {:?}",
        actual.keys().collect::<Vec<_>>(),
        expected.keys().collect::<Vec<_>>(),
    );
    for (layer_idx, expected_point) in expected.iter() {
        let actual_point = actual
            .get(layer_idx)
            .unwrap_or_else(|| panic!("missing actual point for layer {layer_idx}"));
        assert_eq!(
            actual_point, expected_point,
            "layer point mismatch at layer {layer_idx}: actual={actual_point:?} expected={expected_point:?}"
        );
    }
}

fn assert_backward_claims_eq_before_base_layer_expansion<E: Field + std::fmt::Debug>(
    actual: &BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    expected: &BTreeMap<usize, BTreeMap<GKRAddress, E>>,
) {
    assert_eq!(
        actual.len(),
        expected.len(),
        "layer-claim map sizes differ: actual keys {:?}, expected keys {:?}",
        actual.keys().collect::<Vec<_>>(),
        expected.keys().collect::<Vec<_>>(),
    );

    for (layer_idx, expected_claims) in expected.iter() {
        let actual_claims = actual
            .get(layer_idx)
            .unwrap_or_else(|| panic!("missing actual claims for layer {layer_idx}"));
        if *layer_idx == 0 {
            let filtered_expected = expected_claims
                .iter()
                .filter_map(|(address, claim)| {
                    actual_claims
                        .contains_key(address)
                        .then_some((*address, *claim))
                })
                .collect::<BTreeMap<_, _>>();
            assert_eq!(
                actual_claims, &filtered_expected,
                "layer 0 claims diverged before base-layer dependency expansion"
            );
        } else {
            assert_eq!(
                actual_claims, expected_claims,
                "layer {layer_idx} claims diverged before base-layer dependency expansion"
            );
        }
    }
}

fn assert_base_field_query_eq_for_test(
    actual: &prover::gkr::whir::BaseFieldQuery<BF, DefaultTreeConstructor>,
    expected: &prover::gkr::whir::BaseFieldQuery<BF, DefaultTreeConstructor>,
) {
    assert_eq!(actual.index, expected.index);
    assert_eq!(
        actual.leaf_values_concatenated,
        expected.leaf_values_concatenated
    );
    assert_eq!(actual.path, expected.path);
}

fn assert_extension_field_query_eq_for_test(
    actual: &prover::gkr::whir::ExtensionFieldQuery<BF, E4, DefaultTreeConstructor>,
    expected: &prover::gkr::whir::ExtensionFieldQuery<BF, E4, DefaultTreeConstructor>,
) {
    assert_eq!(actual.index, expected.index);
    assert_eq!(
        actual.leaf_values_concatenated,
        expected.leaf_values_concatenated
    );
    assert_eq!(actual.path, expected.path);
}

fn assert_whir_proof_eq_for_test(
    actual: &prover::gkr::whir::WhirPolyCommitProof<BF, E4, DefaultTreeConstructor>,
    expected: &prover::gkr::whir::WhirPolyCommitProof<BF, E4, DefaultTreeConstructor>,
) {
    assert_eq!(
        actual.sumcheck_polys.len(),
        expected.sumcheck_polys.len(),
        "WHIR sumcheck round count diverged",
    );
    for (round_idx, (actual_poly, expected_poly)) in actual
        .sumcheck_polys
        .iter()
        .zip(expected.sumcheck_polys.iter())
        .enumerate()
    {
        assert_eq!(
            actual_poly.len(),
            expected_poly.len(),
            "WHIR sumcheck polynomial degree diverged at round {round_idx}",
        );
        for (coeff_idx, (&actual_coeff, &expected_coeff)) in
            actual_poly.iter().zip(expected_poly.iter()).enumerate()
        {
            assert_eq!(
                actual_coeff, expected_coeff,
                "WHIR sumcheck coefficient diverged at round {round_idx}, coeff {coeff_idx}",
            );
        }
    }
    assert_eq!(
        actual.ood_samples, expected.ood_samples,
        "WHIR OOD samples diverged"
    );
    assert_eq!(
        actual.pow_nonces, expected.pow_nonces,
        "WHIR PoW nonces diverged"
    );
    assert_eq!(
        actual.final_monomials, expected.final_monomials,
        "WHIR final monomials diverged",
    );

    for (actual_commitment, expected_commitment) in [
        (&actual.memory_commitment, &expected.memory_commitment),
        (&actual.witness_commitment, &expected.witness_commitment),
        (&actual.setup_commitment, &expected.setup_commitment),
    ] {
        assert_eq!(
            actual_commitment.commitment.cap,
            expected_commitment.commitment.cap
        );
        assert_eq!(
            actual_commitment.num_columns,
            expected_commitment.num_columns
        );
        assert_eq!(actual_commitment.evals, expected_commitment.evals);
        assert_eq!(
            actual_commitment.queries.len(),
            expected_commitment.queries.len()
        );
        for (actual_query, expected_query) in actual_commitment
            .queries
            .iter()
            .zip(expected_commitment.queries.iter())
        {
            assert_base_field_query_eq_for_test(actual_query, expected_query);
        }
    }

    assert_eq!(
        actual.intermediate_whir_oracles.len(),
        expected.intermediate_whir_oracles.len()
    );
    for (actual_oracle, expected_oracle) in actual
        .intermediate_whir_oracles
        .iter()
        .zip(expected.intermediate_whir_oracles.iter())
    {
        assert_eq!(actual_oracle.commitment.cap, expected_oracle.commitment.cap);
        assert_eq!(actual_oracle.queries.len(), expected_oracle.queries.len());
        for (actual_query, expected_query) in actual_oracle
            .queries
            .iter()
            .zip(expected_oracle.queries.iter())
        {
            assert_extension_field_query_eq_for_test(actual_query, expected_query);
        }
    }
}

fn assert_gkr_proof_eq_for_test(
    actual: &GKRProof<BF, E4, DefaultTreeConstructor>,
    expected: &GKRProof<BF, E4, DefaultTreeConstructor>,
) {
    assert_eq!(actual.external_challenges, expected.external_challenges);
    assert_eq!(
        actual.final_explicit_evaluations,
        expected.final_explicit_evaluations
    );
    assert_eq!(
        actual.grand_product_accumulator_computed,
        expected.grand_product_accumulator_computed
    );
    assert_eq!(
        actual.sumcheck_intermediate_values.len(),
        expected.sumcheck_intermediate_values.len()
    );
    for (layer_idx, expected_values) in expected.sumcheck_intermediate_values.iter() {
        let actual_values = actual
            .sumcheck_intermediate_values
            .get(layer_idx)
            .unwrap_or_else(|| panic!("missing proof layer {layer_idx}"));
        assert_sumcheck_intermediate_values_eq_for_test_with_layer(
            actual_values,
            expected_values,
            *layer_idx,
        );
    }
    assert_whir_proof_eq_for_test(&actual.whir_proof, &expected.whir_proof);
}

fn assert_gkr_proof_structure_for_test(
    proof: &GKRProof<BF, E4, DefaultTreeConstructor>,
    whir_schedule: &WhirSchedule,
) {
    assert!(
        !proof.sumcheck_intermediate_values.is_empty(),
        "proof must contain sumcheck intermediate values",
    );
    for key in [
        OutputType::PermutationProduct,
        OutputType::Lookup16Bits,
        OutputType::LookupTimestamps,
        OutputType::GenericLookup,
    ] {
        assert!(
            proof.final_explicit_evaluations.contains_key(&key),
            "proof must contain explicit evaluations for {key:?}",
        );
    }
    assert_eq!(
        proof.whir_proof.pow_nonces.len(),
        whir_schedule.whir_pow_schedule.len(),
        "proof must contain one PoW nonce per WHIR round",
    );
}

fn stage1_caps_from_tree<T: ColumnMajorMerkleTreeConstructor<BF>>(
    tree: &T,
    subcap_size: usize,
) -> Vec<MerkleTreeCapVarLength> {
    tree.get_cap()
        .cap
        .chunks_exact(subcap_size)
        .map(|chunk| MerkleTreeCapVarLength {
            cap: chunk.to_vec(),
        })
        .collect_vec()
}

fn copy_bf_device_slice_to_host(values: &DeviceSlice<BF>, context: &ProverContext) -> Vec<BF> {
    let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
    memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    unsafe { host.get_accessor().get().to_vec() }
}

fn copy_u32_device_slice_to_host(values: &DeviceSlice<u32>, context: &ProverContext) -> Vec<u32> {
    let mut host = unsafe { context.alloc_host_uninit_slice(values.len()) };
    memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    unsafe { host.get_accessor().get().to_vec() }
}

fn copy_base_poly_from_gpu_storage<E: Field>(
    storage: &GpuGKRStorage<BF, E>,
    address: GKRAddress,
    context: &ProverContext,
) -> Vec<BF> {
    let poly = storage.get_base_layer(address);
    let mut tmp = context
        .alloc(poly.len(), AllocationPlacement::BestFit)
        .unwrap();
    set_by_ref(
        &poly.as_device_chunk(),
        tmp.deref_mut(),
        context.get_exec_stream(),
    )
    .unwrap();

    let mut host = unsafe { context.alloc_host_uninit_slice(poly.len()) };
    memory_copy_async(&mut host, &tmp, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    unsafe { host.get_accessor().get().to_vec() }
}

fn copy_ext_poly_from_gpu_storage<E: Field + SetByRef>(
    storage: &GpuGKRStorage<BF, E>,
    address: GKRAddress,
    context: &ProverContext,
) -> Vec<E> {
    let poly = storage
        .try_get_ext_poly(address)
        .unwrap_or_else(|| panic!("missing GPU extension poly for {:?}", address));
    let mut tmp = context
        .alloc(poly.len(), AllocationPlacement::BestFit)
        .unwrap();
    set_by_ref(
        &poly.as_device_chunk(),
        tmp.deref_mut(),
        context.get_exec_stream(),
    )
    .unwrap();

    let mut host = vec![E::ZERO; poly.len()];
    memory_copy_async(&mut host, &tmp, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn describe_first_flat_column_mismatch<Column: AsRef<[BF]>>(
    gpu_flat_columns: &[BF],
    cpu_columns: &[Column],
    trace_len: usize,
) -> std::option::Option<String> {
    if gpu_flat_columns.len() != cpu_columns.len() * trace_len {
        return Some(format!(
            "gpu flat len {} != cpu flat len {}",
            gpu_flat_columns.len(),
            cpu_columns.len() * trace_len
        ));
    }

    for (column_idx, cpu_column) in cpu_columns.iter().enumerate() {
        let cpu_column = cpu_column.as_ref();
        let gpu_column = &gpu_flat_columns[column_idx * trace_len..(column_idx + 1) * trace_len];
        if let Some((row_idx, (gpu_value, cpu_value))) = gpu_column
            .iter()
            .zip(cpu_column.iter())
            .enumerate()
            .find(|(_, (gpu_value, cpu_value))| gpu_value != cpu_value)
        {
            return Some(format!(
                "column {column_idx}, row {row_idx}: gpu={gpu_value:?}, cpu={cpu_value:?}"
            ));
        }
    }

    None
}

fn describe_first_trace_holder_column_mismatch<Column: AsRef<[BF]>>(
    trace_holder: &TraceHolder<BF>,
    cpu_columns: &[Column],
    trace_len: usize,
    context: &ProverContext,
) -> std::option::Option<String> {
    if trace_holder.columns_count != cpu_columns.len() {
        return Some(format!(
            "gpu columns {} != cpu columns {}",
            trace_holder.columns_count,
            cpu_columns.len()
        ));
    }
    if (1usize << trace_holder.log_domain_size) != trace_len {
        return Some(format!(
            "gpu trace len {} != cpu trace len {}",
            1usize << trace_holder.log_domain_size,
            trace_len
        ));
    }

    let raw = trace_holder.get_hypercube_evals();
    for (column_idx, cpu_column) in cpu_columns.iter().enumerate() {
        let gpu_column = copy_bf_device_slice_to_host(
            &raw[column_idx * trace_len..(column_idx + 1) * trace_len],
            context,
        );
        let cpu_column = cpu_column.as_ref();
        if let Some((row_idx, (gpu_value, cpu_value))) = gpu_column
            .iter()
            .zip(cpu_column.iter())
            .enumerate()
            .find(|(_, (gpu_value, cpu_value))| gpu_value != cpu_value)
        {
            return Some(format!(
                "column {column_idx}, row {row_idx}: gpu={gpu_value:?}, cpu={cpu_value:?}"
            ));
        }
    }

    None
}

fn describe_first_trace_holder_subrange_mismatch<Column: AsRef<[BF]>>(
    trace_holder: &TraceHolder<BF>,
    cpu_columns: &[Column],
    column_range: std::ops::Range<usize>,
    trace_len: usize,
    context: &ProverContext,
) -> std::option::Option<String> {
    if column_range.end > trace_holder.columns_count {
        return Some(format!(
            "gpu column range {:?} exceeds total columns {}",
            column_range, trace_holder.columns_count
        ));
    }
    if column_range.end > cpu_columns.len() {
        return Some(format!(
            "cpu column range {:?} exceeds total columns {}",
            column_range,
            cpu_columns.len()
        ));
    }
    if (1usize << trace_holder.log_domain_size) != trace_len {
        return Some(format!(
            "gpu trace len {} != cpu trace len {}",
            1usize << trace_holder.log_domain_size,
            trace_len
        ));
    }

    let raw = trace_holder.get_hypercube_evals();
    for column_idx in column_range {
        let gpu_column = copy_bf_device_slice_to_host(
            &raw[column_idx * trace_len..(column_idx + 1) * trace_len],
            context,
        );
        let cpu_column = cpu_columns[column_idx].as_ref();
        if let Some((row_idx, (gpu_value, cpu_value))) = gpu_column
            .iter()
            .zip(cpu_column.iter())
            .enumerate()
            .find(|(_, (gpu_value, cpu_value))| gpu_value != cpu_value)
        {
            return Some(format!(
                "column {column_idx}, row {row_idx}: gpu={gpu_value:?}, cpu={cpu_value:?}"
            ));
        }
    }

    None
}

fn describe_first_vec_mismatch<T: PartialEq + core::fmt::Debug>(
    gpu_values: &[T],
    cpu_values: &[T],
) -> std::option::Option<String> {
    if gpu_values.len() != cpu_values.len() {
        return Some(format!(
            "gpu len {} != cpu len {}",
            gpu_values.len(),
            cpu_values.len()
        ));
    }

    gpu_values
        .iter()
        .zip(cpu_values.iter())
        .enumerate()
        .find(|(_, (gpu_value, cpu_value))| gpu_value != cpu_value)
        .map(|(idx, (gpu_value, cpu_value))| {
            format!("index {idx}: gpu={gpu_value:?}, cpu={cpu_value:?}")
        })
}

fn assert_generic_family_mapping_contract(
    lookup_mappings: &crate::prover::gkr::stage1::GpuGKRLookupMappings,
    cpu_trace: &GKRFullWitnessTrace<
        BF,
        impl std::alloc::Allocator + Clone,
        impl std::alloc::Allocator + Clone,
    >,
    _populated_rows: usize,
    context: &ProverContext,
) {
    let gpu_generic_family =
        copy_u32_device_slice_to_host(lookup_mappings.generic_family(), context);
    let trace_len = lookup_mappings.trace_len;
    let expected_num_cols = cpu_trace.generic_lookup_mapping.len();
    assert_eq!(gpu_generic_family.len(), expected_num_cols * trace_len);

    for generic_set_idx in 0..lookup_mappings.num_generic_sets {
        let gpu_column = copy_u32_device_slice_to_host(
            lookup_mappings.generic_mapping(generic_set_idx),
            context,
        );
        let cpu_column = &cpu_trace.generic_lookup_mapping[generic_set_idx];
        assert_eq!(
            gpu_column, *cpu_column,
            "generic mapping column {generic_set_idx} diverged",
        );
    }

    if lookup_mappings.has_decoder {
        let gpu_decoder = copy_u32_device_slice_to_host(
            lookup_mappings
                .decoder_mapping()
                .expect("decoder mapping must be present"),
            context,
        );
        let cpu_decoder = cpu_trace
            .generic_lookup_mapping
            .last()
            .expect("decoder lookup mapping must be present");
        assert_eq!(gpu_decoder, *cpu_decoder);
        assert_eq!(
            &gpu_generic_family[lookup_mappings.num_generic_sets * trace_len..],
            &gpu_decoder,
        );
    }
}

fn assert_gpu_and_cpu_gkr_storage_match<
    E: FieldExtension<BF> + Field + SetByRef + core::fmt::Debug,
>(
    gpu_storage: &GpuGKRStorage<BF, E>,
    cpu_storage: &GKRStorage<BF, E>,
    context: &ProverContext,
) {
    assert_eq!(gpu_storage.layers.len(), cpu_storage.layers.len());
    for (layer_idx, (gpu_layer, cpu_layer)) in gpu_storage
        .layers
        .iter()
        .zip(cpu_storage.layers.iter())
        .enumerate()
    {
        let gpu_base_keys = gpu_layer.base_field_inputs.keys().copied().collect_vec();
        let cpu_base_keys = cpu_layer.base_field_inputs.keys().copied().collect_vec();
        assert_eq!(
            gpu_base_keys, cpu_base_keys,
            "base keys differ in layer {layer_idx}"
        );
        for address in cpu_base_keys {
            let gpu_values = copy_base_poly_from_gpu_storage(gpu_storage, address, context);
            let cpu_values = cpu_storage
                .try_get_base_poly(address)
                .unwrap_or_else(|| panic!("missing CPU base poly for {:?}", address));
            assert_eq!(gpu_values, cpu_values, "base poly {:?} diverged", address);
        }

        let gpu_ext_keys = gpu_layer
            .extension_field_inputs
            .keys()
            .copied()
            .collect_vec();
        let cpu_ext_keys = cpu_layer
            .extension_field_inputs
            .keys()
            .copied()
            .collect_vec();
        assert_eq!(
            gpu_ext_keys, cpu_ext_keys,
            "extension keys differ in layer {layer_idx}"
        );
        for address in cpu_ext_keys {
            let gpu_values = copy_ext_poly_from_gpu_storage(gpu_storage, address, context);
            let cpu_values = cpu_storage
                .try_get_ext_poly(address)
                .unwrap_or_else(|| panic!("missing CPU extension poly for {:?}", address));
            assert_eq!(
                gpu_values, cpu_values,
                "extension poly {:?} diverged",
                address
            );
        }
    }
}

#[test]
#[serial]
fn run_basic_unrolled_async_scheduler_smoke_test() {
    let BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit,
        gpu_backward_state,
        initial_output_layer_idx,
        top_layer_claims,
        evaluation_point,
        seed,
        batching_challenge,
        lookup_additive_part,
        constraints_batch_challenge,
        expected_proof_layers,
    } = prepare_basic_unrolled_async_backward_fixture(8);

    let scheduled = gpu_backward_state
        .schedule_execute_backward_workflow(
            compiled_circuit,
            initial_output_layer_idx,
            top_layer_claims,
            evaluation_point,
            seed,
            batching_challenge,
            lookup_additive_part,
            constraints_batch_challenge,
            &context,
        )
        .unwrap();

    let completion_event =
        CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING).unwrap();
    completion_event.record(context.get_exec_stream()).unwrap();
    assert!(
        !completion_event.query().unwrap(),
        "workflow scheduling should enqueue work without waiting for completion"
    );

    let execution = scheduled.wait(&context).unwrap();
    assert_eq!(execution.proofs.len(), expected_proof_layers);
    assert!(execution.proofs.contains_key(&0));
    assert!(execution.claims_for_layers.contains_key(&0));
    assert!(execution.points_for_claims_at_layer.contains_key(&0));
    assert!(!execution.points_for_claims_at_layer[&0].is_empty());
}

#[test]
#[serial]
fn run_basic_unrolled_main_layer0_plan_matches_cpu_test() {
    fn copy_device_values<T: Copy>(
        context: &ProverContext,
        values: &crate::primitives::context::DeviceAllocation<T>,
    ) -> Vec<T> {
        let mut allocation = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { allocation.get_accessor().get().to_vec() }
    }

    let BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit,
        mut gpu_backward_state,
        initial_output_layer_idx: _,
        top_layer_claims: _,
        evaluation_point: _,
        seed: _,
        batching_challenge,
        lookup_additive_part,
        constraints_batch_challenge,
        expected_proof_layers: _,
    } = prepare_basic_unrolled_async_backward_fixture(8);

    while let Some(layer_plan) = gpu_backward_state
        .prepare_next_layer_static(&context)
        .unwrap()
    {
        drop(layer_plan);
    }

    let mut main_layer_state = gpu_backward_state.into_main_layer_backward_state(
        compiled_circuit.clone(),
        lookup_additive_part,
        constraints_batch_challenge,
    );

    let layer0_plan = loop {
        let Some(layer_plan) = main_layer_state
            .prepare_next_layer(batching_challenge, &context)
            .unwrap()
        else {
            panic!("expected to reach main layer 0 plan");
        };
        if layer_plan.layer_idx == 0 {
            break layer_plan;
        }
        drop(layer_plan);
    };

    let expected = expected_main_layer_kernel_specs_for_test(
        &compiled_circuit.layers[0],
        0,
        main_layer_state.storage(),
        batching_challenge,
        lookup_additive_part,
        constraints_batch_challenge,
        compiled_circuit.memory_layout.total_width,
        compiled_circuit.witness_layout.total_width,
    );

    context.get_exec_stream().synchronize().unwrap();
    assert_main_layer_plan_for_test(&layer0_plan, main_layer_state.storage(), &expected);

    let mut callbacks = crate::primitives::callbacks::Callbacks::new();
    let round1 = layer0_plan
        .schedule_round_1(&mut callbacks, &context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    for (idx, (scheduled, kernel)) in round1
        .iter()
        .zip(layer0_plan.kernel_plans().iter())
        .enumerate()
    {
        let base_inputs: Vec<
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<BF, E4>,
        > = copy_device_values(&context, &scheduled.device.base_field_inputs);
        let ext_inputs: Vec<
            crate::prover::gkr::GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>,
        > = copy_device_values(&context, &scheduled.device.extension_field_inputs);

        for (descriptor, address) in base_inputs.iter().zip(kernel.inputs.inputs_in_base.iter()) {
            if *address == GKRAddress::placeholder() {
                assert!(descriptor.base_input_start.is_null());
                continue;
            }
            let poly = main_layer_state.storage().get_base_layer(*address);
            assert_eq!(
                descriptor.base_input_start,
                poly.as_ptr(),
                "kernel {idx} round1 base input {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.base_layer_half_size,
                poly.len() / 2,
                "kernel {idx} round1 base input {:?} half-size mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 4,
                "kernel {idx} round1 base input {:?} next-layer mismatch",
                address
            );
        }
        for (descriptor, address) in ext_inputs
            .iter()
            .zip(kernel.inputs.inputs_in_extension.iter())
        {
            if *address == GKRAddress::placeholder() {
                assert!(descriptor.previous_layer_start.is_null());
                continue;
            }
            let poly = main_layer_state.storage().get_ext_poly(*address);
            assert_eq!(
                descriptor.previous_layer_start,
                poly.as_ptr(),
                "kernel {idx} round1 ext input {:?} start mismatch",
                address
            );
            assert_eq!(
                descriptor.this_layer_size,
                poly.len() / 2,
                "kernel {idx} round1 ext input {:?} this-layer mismatch",
                address
            );
            assert_eq!(
                descriptor.next_layer_size,
                poly.len() / 4,
                "kernel {idx} round1 ext input {:?} next-layer mismatch",
                address
            );
            assert!(
                descriptor.first_access,
                "kernel {idx} round1 ext input {:?} should be first access",
                address
            );
        }
    }
}

#[test]
#[serial]
fn run_basic_unrolled_main_layer0_static_plan_matches_cpu_test() {
    let BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit,
        mut gpu_backward_state,
        initial_output_layer_idx: _,
        top_layer_claims: _,
        evaluation_point: _,
        seed: _,
        batching_challenge,
        lookup_additive_part,
        constraints_batch_challenge,
        expected_proof_layers: _,
    } = prepare_basic_unrolled_async_backward_fixture(8);

    while let Some(layer_plan) = gpu_backward_state
        .prepare_next_layer_static(&context)
        .unwrap()
    {
        drop(layer_plan);
    }

    let mut main_layer_state = gpu_backward_state.into_main_layer_backward_state(
        compiled_circuit.clone(),
        lookup_additive_part,
        constraints_batch_challenge,
    );

    let layer0_plan = loop {
        let Some(layer_plan) = main_layer_state
            .prepare_next_layer_static(&context)
            .unwrap()
        else {
            panic!("expected to reach main layer 0 static plan");
        };
        if layer_plan.layer_idx == 0 {
            break layer_plan;
        }
        drop(layer_plan);
    };

    let expected = expected_main_layer_kernel_specs_for_test(
        &compiled_circuit.layers[0],
        0,
        main_layer_state.storage(),
        batching_challenge,
        lookup_additive_part,
        constraints_batch_challenge,
        compiled_circuit.memory_layout.total_width,
        compiled_circuit.witness_layout.total_width,
    );

    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(layer0_plan.kernel_plans().len(), expected.len());

    let mut expected_offset = 0usize;
    for (idx, (kernel_plan, expected_spec)) in layer0_plan
        .kernel_plans()
        .iter()
        .zip(expected.iter())
        .enumerate()
    {
        assert_eq!(
            kernel_plan.kind, expected_spec.kind,
            "kernel {idx} kind mismatch"
        );
        assert_eq!(
            kernel_plan.inputs, expected_spec.inputs,
            "kernel {idx} inputs mismatch"
        );
        assert!(
            kernel_plan.batch_challenges.is_empty(),
            "kernel {idx} static plan should not embed immediate batch challenges"
        );
        assert_eq!(
            kernel_plan.batch_challenge_offset, expected_offset,
            "kernel {idx} batch challenge offset mismatch"
        );
        assert_eq!(
            kernel_plan.batch_challenge_count,
            expected_spec.batch_challenges.len(),
            "kernel {idx} batch challenge count mismatch"
        );
        expected_offset += expected_spec.batch_challenges.len();

        match expected_spec.kind {
            GpuGKRMainLayerKernelKind::LookupBasePair
            | GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase
            | GpuGKRMainLayerKernelKind::LookupUnbalanced
            | GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup => {
                assert_eq!(
                    kernel_plan.auxiliary_challenge_summary(),
                    None,
                    "kernel {idx} should defer lookup additive challenge"
                );
            }
            _ => {
                assert_eq!(
                    kernel_plan.auxiliary_challenge_summary(),
                    Some(E4::ZERO),
                    "kernel {idx} should not depend on deferred auxiliary challenge"
                );
            }
        }

        match expected_spec.constraint_metadata.as_ref() {
            Some(metadata) => {
                assert_eq!(
                    kernel_plan.constraint_metadata_summary(),
                    Some((
                        metadata.quadratic_terms.len(),
                        metadata.linear_terms.len(),
                        E4::ZERO,
                    )),
                    "kernel {idx} constraint metadata summary mismatch"
                );
            }
            None => {
                assert_eq!(
                    kernel_plan.constraint_metadata_summary(),
                    None,
                    "kernel {idx} unexpected constraint metadata"
                );
            }
        }
    }
}

#[test]
#[serial]
fn run_basic_unrolled_main_layer0_kernel_kind_trace_test() {
    let BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit,
        mut gpu_backward_state,
        batching_challenge,
        lookup_additive_part,
        constraints_batch_challenge,
        ..
    } = prepare_basic_unrolled_async_backward_fixture(8);

    while let Some(layer_plan) = gpu_backward_state
        .prepare_next_layer_static(&context)
        .unwrap()
    {
        drop(layer_plan);
    }

    let mut main_layer_state = gpu_backward_state.into_main_layer_backward_state(
        compiled_circuit,
        lookup_additive_part,
        constraints_batch_challenge,
    );

    let layer0_plan = loop {
        let Some(layer_plan) = main_layer_state
            .prepare_next_layer(batching_challenge, &context)
            .unwrap()
        else {
            panic!("expected to reach main layer 0 plan");
        };
        if layer_plan.layer_idx == 0 {
            break layer_plan;
        }
        drop(layer_plan);
    };

    let kernel_kinds = layer0_plan
        .kernel_plans()
        .iter()
        .map(|kernel| kernel.kind)
        .collect_vec();
    eprintln!("layer0 kernel kinds: {kernel_kinds:?}");
}

#[test]
#[serial]
fn run_basic_unrolled_first_main_layer_static_vs_dynamic_execution_test() {
    fn advance_dimension_reduction(
        mut state: GpuGKRDimensionReducingBackwardState<BF, E4>,
        compiled_circuit: &GKRCircuitArtifact<BF>,
        mut current_claims: BTreeMap<GKRAddress, E4>,
        mut current_point: Vec<E4>,
        mut seed: Seed,
        mut batching_challenge: E4,
        lookup_additive_part: E4,
        constraints_batch_challenge: E4,
        context: &ProverContext,
    ) -> (
        crate::prover::gkr::backward::GpuGKRMainLayerBackwardState<E4>,
        BTreeMap<GKRAddress, E4>,
        Vec<E4>,
        Seed,
        E4,
    ) {
        while let Some(mut plan) = state
            .prepare_next_layer(batching_challenge, context)
            .unwrap()
        {
            let scheduled = plan
                .schedule_execute_dimension_reducing_layer(
                    &current_claims,
                    &current_point,
                    seed,
                    batching_challenge,
                    context,
                )
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let execution = scheduled.into_execution();
            current_claims = execution.new_claims;
            current_point = execution.new_claim_point;
            seed = execution.updated_seed;
            batching_challenge = execution.next_batching_challenge;
        }

        (
            state.into_main_layer_backward_state(
                compiled_circuit.clone(),
                lookup_additive_part,
                constraints_batch_challenge,
            ),
            current_claims,
            current_point,
            seed,
            batching_challenge,
        )
    }

    let (base_fixture, expected_cpu_proof) =
        prepare_basic_unrolled_fixture(BasicUnrolledFixtureBuildConfig {
            binary_path: "examples/hashed_fibonacci/app.bin",
            text_path: "examples/hashed_fibonacci/app.text",
            non_determinism_reads: &[15, 1],
            compute_cpu_reference: false,
        });
    assert!(expected_cpu_proof.is_none());
    let fixture_dynamic = build_basic_unrolled_async_backward_fixture_from_base(&base_fixture);
    eprintln!("first-main-layer: dynamic fixture ready");
    let fixture_static = build_basic_unrolled_async_backward_fixture_from_base(&base_fixture);
    eprintln!("first-main-layer: static fixture ready");

    let (
        mut dynamic_state,
        dynamic_claims,
        dynamic_point,
        dynamic_seed,
        dynamic_batching_challenge,
    ) = advance_dimension_reduction(
        fixture_dynamic.gpu_backward_state,
        &fixture_dynamic.compiled_circuit,
        fixture_dynamic.top_layer_claims,
        fixture_dynamic.evaluation_point,
        fixture_dynamic.seed,
        fixture_dynamic.batching_challenge,
        fixture_dynamic.lookup_additive_part,
        fixture_dynamic.constraints_batch_challenge,
        &fixture_dynamic.context,
    );
    eprintln!("first-main-layer: dynamic dimension reduction ready");

    let (mut static_state, static_claims, static_point, static_seed, static_batching_challenge) =
        advance_dimension_reduction(
            fixture_static.gpu_backward_state,
            &fixture_static.compiled_circuit,
            fixture_static.top_layer_claims,
            fixture_static.evaluation_point,
            fixture_static.seed,
            fixture_static.batching_challenge,
            fixture_static.lookup_additive_part,
            fixture_static.constraints_batch_challenge,
            &fixture_static.context,
        );
    eprintln!("first-main-layer: static dimension reduction ready");

    let mut dynamic_plan = dynamic_state
        .prepare_next_layer(dynamic_batching_challenge, &fixture_dynamic.context)
        .unwrap()
        .expect("expected first main-layer plan");
    let first_layer_idx = dynamic_plan.layer_idx;
    let mut static_plan = static_state
        .prepare_next_layer_static(&fixture_static.context)
        .unwrap()
        .expect("expected first static main-layer plan");
    assert_eq!(static_plan.layer_idx, first_layer_idx);

    let dynamic_scheduled = dynamic_plan
        .schedule_execute_main_layer(
            &dynamic_claims,
            &dynamic_point,
            dynamic_seed,
            &fixture_dynamic.context,
        )
        .unwrap();
    eprintln!("first-main-layer: dynamic main-layer scheduled");
    fixture_dynamic
        .context
        .get_exec_stream()
        .synchronize()
        .unwrap();
    eprintln!("first-main-layer: dynamic main-layer synchronized");
    let dynamic_execution = dynamic_scheduled.into_execution();

    let shared_state = crate::prover::gkr::backward::make_deferred_backward_workflow_state();
    crate::prover::gkr::backward::populate_backward_workflow_state(
        &shared_state,
        first_layer_idx + 1,
        static_claims,
        static_point,
        static_seed,
        static_batching_challenge,
        fixture_static.lookup_additive_part,
        fixture_static.constraints_batch_challenge,
    );
    let static_scheduled = static_plan
        .schedule_execute_main_layer_from_workflow_state(
            std::sync::Arc::clone(&shared_state),
            &fixture_static.context,
        )
        .unwrap();
    eprintln!("first-main-layer: static main-layer scheduled");
    fixture_static
        .context
        .get_exec_stream()
        .synchronize()
        .unwrap();
    eprintln!("first-main-layer: static main-layer synchronized");
    let static_execution = static_scheduled.into_execution();

    assert_sumcheck_intermediate_values_eq_for_test_with_layer(
        &dynamic_execution.proof,
        &static_execution.proof,
        first_layer_idx,
    );
    assert_eq!(dynamic_execution.new_claims, static_execution.new_claims);
    assert_eq!(
        dynamic_execution.new_claim_point,
        static_execution.new_claim_point
    );
    assert_eq!(
        dynamic_execution.next_batching_challenge,
        static_execution.next_batching_challenge
    );
    assert_eq!(
        dynamic_execution.updated_seed,
        static_execution.updated_seed
    );
}

#[test]
#[serial]
fn run_basic_unrolled_main_layers_static_vs_dynamic_execution_test() {
    fn advance_dimension_reduction(
        mut state: GpuGKRDimensionReducingBackwardState<BF, E4>,
        compiled_circuit: &GKRCircuitArtifact<BF>,
        mut current_claims: BTreeMap<GKRAddress, E4>,
        mut current_point: Vec<E4>,
        mut seed: Seed,
        mut batching_challenge: E4,
        lookup_additive_part: E4,
        constraints_batch_challenge: E4,
        context: &ProverContext,
    ) -> (
        crate::prover::gkr::backward::GpuGKRMainLayerBackwardState<E4>,
        BTreeMap<GKRAddress, E4>,
        Vec<E4>,
        Seed,
        E4,
    ) {
        while let Some(mut plan) = state
            .prepare_next_layer(batching_challenge, context)
            .unwrap()
        {
            let scheduled = plan
                .schedule_execute_dimension_reducing_layer(
                    &current_claims,
                    &current_point,
                    seed,
                    batching_challenge,
                    context,
                )
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let execution = scheduled.into_execution();
            current_claims = execution.new_claims;
            current_point = execution.new_claim_point;
            seed = execution.updated_seed;
            batching_challenge = execution.next_batching_challenge;
        }

        (
            state.into_main_layer_backward_state(
                compiled_circuit.clone(),
                lookup_additive_part,
                constraints_batch_challenge,
            ),
            current_claims,
            current_point,
            seed,
            batching_challenge,
        )
    }

    let fixture_dynamic = prepare_basic_unrolled_async_backward_fixture(8);
    let fixture_static = prepare_basic_unrolled_async_backward_fixture(8);

    let (
        mut dynamic_state,
        mut dynamic_claims,
        mut dynamic_point,
        mut dynamic_seed,
        mut dynamic_batching_challenge,
    ) = advance_dimension_reduction(
        fixture_dynamic.gpu_backward_state,
        &fixture_dynamic.compiled_circuit,
        fixture_dynamic.top_layer_claims,
        fixture_dynamic.evaluation_point,
        fixture_dynamic.seed,
        fixture_dynamic.batching_challenge,
        fixture_dynamic.lookup_additive_part,
        fixture_dynamic.constraints_batch_challenge,
        &fixture_dynamic.context,
    );

    let (
        mut static_state,
        mut static_claims,
        mut static_point,
        mut static_seed,
        mut static_batching_challenge,
    ) = advance_dimension_reduction(
        fixture_static.gpu_backward_state,
        &fixture_static.compiled_circuit,
        fixture_static.top_layer_claims,
        fixture_static.evaluation_point,
        fixture_static.seed,
        fixture_static.batching_challenge,
        fixture_static.lookup_additive_part,
        fixture_static.constraints_batch_challenge,
        &fixture_static.context,
    );

    let mut current_output_layer_idx = fixture_dynamic.initial_output_layer_idx;
    while let Some(mut dynamic_plan) = dynamic_state
        .prepare_next_layer(dynamic_batching_challenge, &fixture_dynamic.context)
        .unwrap()
    {
        let layer_idx = dynamic_plan.layer_idx;
        let mut static_plan = static_state
            .prepare_next_layer_static(&fixture_static.context)
            .unwrap()
            .unwrap_or_else(|| panic!("missing static plan for layer {layer_idx}"));
        assert_eq!(static_plan.layer_idx, layer_idx);

        let dynamic_scheduled = dynamic_plan
            .schedule_execute_main_layer(
                &dynamic_claims,
                &dynamic_point,
                dynamic_seed,
                &fixture_dynamic.context,
            )
            .unwrap();
        fixture_dynamic
            .context
            .get_exec_stream()
            .synchronize()
            .unwrap();
        let dynamic_execution = dynamic_scheduled.into_execution();

        let shared_state = crate::prover::gkr::backward::make_deferred_backward_workflow_state();
        crate::prover::gkr::backward::populate_backward_workflow_state(
            &shared_state,
            current_output_layer_idx,
            static_claims.clone(),
            static_point.clone(),
            static_seed,
            static_batching_challenge,
            fixture_static.lookup_additive_part,
            fixture_static.constraints_batch_challenge,
        );
        let static_scheduled = static_plan
            .schedule_execute_main_layer_from_workflow_state(
                std::sync::Arc::clone(&shared_state),
                &fixture_static.context,
            )
            .unwrap();
        fixture_static
            .context
            .get_exec_stream()
            .synchronize()
            .unwrap();
        let static_execution = static_scheduled.into_execution();

        assert_sumcheck_intermediate_values_eq_for_test_with_layer(
            &dynamic_execution.proof,
            &static_execution.proof,
            layer_idx,
        );
        assert_eq!(
            dynamic_execution.new_claims, static_execution.new_claims,
            "layer {layer_idx}: new_claims mismatch"
        );
        assert_eq!(
            dynamic_execution.new_claim_point, static_execution.new_claim_point,
            "layer {layer_idx}: new_claim_point mismatch"
        );
        assert_eq!(
            dynamic_execution.next_batching_challenge, static_execution.next_batching_challenge,
            "layer {layer_idx}: next batching challenge mismatch"
        );
        assert_eq!(
            dynamic_execution.updated_seed, static_execution.updated_seed,
            "layer {layer_idx}: updated seed mismatch"
        );

        dynamic_claims = dynamic_execution.new_claims;
        dynamic_point = dynamic_execution.new_claim_point;
        dynamic_seed = dynamic_execution.updated_seed;
        dynamic_batching_challenge = dynamic_execution.next_batching_challenge;

        static_claims = static_execution.new_claims;
        static_point = static_execution.new_claim_point;
        static_seed = static_execution.updated_seed;
        static_batching_challenge = static_execution.next_batching_challenge;

        current_output_layer_idx = layer_idx;
        dynamic_state.purge_up_to_layer(layer_idx);
        static_state.purge_up_to_layer(layer_idx);
    }
}

#[test]
#[serial]
fn run_basic_unrolled_async_allocator_regression_test() {
    let BasicUnrolledAsyncBackwardFixture {
        context,
        compiled_circuit,
        gpu_backward_state,
        initial_output_layer_idx,
        top_layer_claims,
        evaluation_point,
        seed,
        batching_challenge,
        lookup_additive_part,
        constraints_batch_challenge,
        expected_proof_layers: _,
    } = prepare_basic_unrolled_async_backward_fixture(8);

    let host_before = context.get_host_used_mem_current();
    context.reset_host_used_mem_peak();

    let scheduled = gpu_backward_state
        .schedule_execute_backward_workflow(
            compiled_circuit,
            initial_output_layer_idx,
            top_layer_claims,
            evaluation_point,
            seed,
            batching_challenge,
            lookup_additive_part,
            constraints_batch_challenge,
            &context,
        )
        .unwrap();

    assert!(
        context.get_host_used_mem_peak() > host_before,
        "backward scheduling should allocate from the host allocator"
    );

    let execution = scheduled.wait(&context).unwrap();
    drop(execution);

    assert_eq!(
        context.get_host_used_mem_current(),
        host_before,
        "host allocator usage should return to baseline after drop"
    );
}

#[test]
#[serial]
fn run_basic_unrolled_test() {
    let fixture = prepare_basic_unrolled_proof_fixture();
    let proof_job = fixture
        .schedule_prove(fixture.parity_pow_challenges())
        .unwrap();

    assert!(
        !proof_job.is_finished().unwrap(),
        "prove() should return before the scheduled proof completes"
    );

    let (gpu_proof, _proof_time_ms) = proof_job.finish().unwrap();
    assert_gkr_proof_eq_for_test(&gpu_proof, &fixture.expected_cpu_proof);
}

#[test]
#[serial]
fn run_basic_unrolled_proof_job_default_pow_smoke_test() {
    let fixture = prepare_basic_unrolled_proof_fixture();
    let proof_job = fixture.schedule_prove(None).unwrap();

    assert!(
        !proof_job.is_finished().unwrap(),
        "prove() should remain non-blocking without external PoW overrides"
    );

    let (gpu_proof, _proof_time_ms) = proof_job.finish().unwrap();
    assert_eq!(
        gpu_proof.external_challenges,
        fixture.expected_cpu_proof.external_challenges
    );
    assert_eq!(
        gpu_proof.final_explicit_evaluations,
        fixture.expected_cpu_proof.final_explicit_evaluations
    );
    // With default (non-external) PoW nonces, the GPU may find different valid
    // nonces than the CPU.  Different nonces → different WHIR transcript state →
    // different evaluation point → different backward sumcheck values.  So we can
    // only check structural properties here, not exact values.
    assert_eq!(
        gpu_proof.sumcheck_intermediate_values.len(),
        fixture
            .expected_cpu_proof
            .sumcheck_intermediate_values
            .len(),
        "number of proof layers must match"
    );
    for (layer_idx, expected_values) in fixture
        .expected_cpu_proof
        .sumcheck_intermediate_values
        .iter()
    {
        let actual_values = gpu_proof
            .sumcheck_intermediate_values
            .get(layer_idx)
            .unwrap_or_else(|| panic!("missing proof layer {layer_idx}"));
        assert_eq!(
            actual_values.sumcheck_num_rounds, expected_values.sumcheck_num_rounds,
            "layer {layer_idx}: sumcheck_num_rounds must match"
        );
        assert_eq!(
            actual_values.internal_round_coefficients.len(),
            expected_values.internal_round_coefficients.len(),
            "layer {layer_idx}: number of internal round coefficients must match"
        );
        assert_eq!(
            actual_values.final_step_evaluations.len(),
            expected_values.final_step_evaluations.len(),
            "layer {layer_idx}: number of final step evaluations must match"
        );
    }
    assert_eq!(
        gpu_proof.whir_proof.pow_nonces.len(),
        fixture.base.whir_schedule.whir_pow_schedule.len()
    );
    // final_monomials is not yet populated by the proof pipeline; just check
    // it matches whatever the CPU reference has.
    assert_eq!(
        gpu_proof.whir_proof.final_monomials.len(),
        fixture.expected_cpu_proof.whir_proof.final_monomials.len()
    );
}

#[test]
#[serial]
fn run_basic_unrolled_proof_job_multi_schedule_test() {
    let fixture = prepare_basic_unrolled_proof_fixture();
    let baseline_device_usage = fixture.base.context.get_used_mem_current();
    let t0 = std::time::Instant::now();
    let proof_job_0 = fixture
        .schedule_prove(fixture.parity_pow_challenges())
        .unwrap();
    eprintln!("schedule_prove #0 took {:?}", t0.elapsed());
    let t1 = std::time::Instant::now();
    let proof_job_1 = fixture
        .schedule_prove(fixture.parity_pow_challenges())
        .unwrap();
    eprintln!("schedule_prove #1 took {:?}", t1.elapsed());

    let (gpu_proof_0, proof_time_ms_0) = proof_job_0.finish().unwrap();
    eprintln!("proof_job_0 proof time: {proof_time_ms_0} ms");
    assert_gkr_proof_eq_for_test(&gpu_proof_0, &fixture.expected_cpu_proof);
    drop(gpu_proof_0);

    let (gpu_proof_1, proof_time_ms_1) = proof_job_1.finish().unwrap();
    eprintln!("proof_job_1 proof time: {proof_time_ms_1} ms");
    assert_gkr_proof_eq_for_test(&gpu_proof_1, &fixture.expected_cpu_proof);
    drop(gpu_proof_1);

    assert_eq!(
        fixture.base.context.get_used_mem_current(),
        baseline_device_usage,
        "device memory must return to baseline after both proofs complete"
    );
}

#[test]
#[serial]
#[ignore]
fn run_basic_unrolled_proof_job_profile_test() {
    let nsys_capture_domain = std::ffi::CStr::from_bytes_with_nul(b"gpu_prover.tests\0").unwrap();
    let nsys_capture_message =
        std::ffi::CStr::from_bytes_with_nul(b"test.gpu.prove.profiled_call\0").unwrap();

    let fixture = prepare_basic_unrolled_profiling_fixture();
    let baseline_device_usage = fixture.context.get_used_mem_current();

    let warmup_transfers = fixture.schedule_transfers().unwrap();
    fixture.context.get_h2d_stream().synchronize().unwrap();
    let warmup_job = fixture.prove(warmup_transfers, None).unwrap();
    assert!(
        !warmup_job.is_finished().unwrap(),
        "prove() should remain non-blocking after transfers are ready",
    );
    let (warmup_proof, warmup_time_ms) = warmup_job.finish().unwrap();
    eprintln!("warmup proof time: {warmup_time_ms} ms");
    assert_gkr_proof_structure_for_test(&warmup_proof, &fixture.whir_schedule);
    drop(warmup_proof);

    let profiled_transfers = fixture.schedule_transfers().unwrap();
    fixture.context.get_h2d_stream().synchronize().unwrap();
    let (profiled_proof, profiled_time_ms) = {
        let _range = start_registered_range(nsys_capture_domain, nsys_capture_message);
        let profiled_job = fixture.prove(profiled_transfers, None).unwrap();
        assert!(
            !profiled_job.is_finished().unwrap(),
            "prove() should remain non-blocking for the profiled call",
        );
        profiled_job.finish().unwrap()
    };
    eprintln!("profiled proof time: {profiled_time_ms} ms");
    assert_gkr_proof_structure_for_test(&profiled_proof, &fixture.whir_schedule);
    drop(profiled_proof);

    assert_eq!(
        fixture.context.get_used_mem_current(),
        baseline_device_usage,
        "device memory must return to baseline after warmup and profiled proofs complete",
    );
}

#[test]
#[serial]
fn run_basic_unrolled_workflow_input_parity_test() {
    type CountersT = DelegationsAndFamiliesCounters;

    const TRACE_LEN_LOG2: usize = 24;
    const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    let binary = std::fs::read(test_artifact_path("examples/hashed_fibonacci/app.bin")).unwrap();
    assert_eq!(binary.len() % 4, 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let text_section =
        std::fs::read(test_artifact_path("examples/hashed_fibonacci/app.text")).unwrap();
    assert_eq!(text_section.len() % 4, 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);
    let cycles_bound = 1 << 20;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter =
        SimpleSnapshotter::<CountersT, { ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(
            cycles_bound,
            state,
        );
    let mut non_determinism = QuasiUARTSource::new_with_reads(vec![15, 1]);

    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<_, _, _, BF>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_program_finished);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;
    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

    let memory_argument_alpha =
        E4::from_array_of_base([BF::new(2), BF::new(5), BF::new(42), BF::new(123)]);
    let permutation_argument_additive_part =
        E4::from_array_of_base([BF::new(7), BF::new(11), BF::new(1024), BF::new(8000)]);
    let permutation_argument_linearization_challenges: [E4; NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();
    let external_challenges: GKRExternalChallenges<BF, E4> = GKRExternalChallenges {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    };

    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BF,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
        ],
    );

    let add_sub_circuit = compile_unrolled_circuit_state_transition_into_gkr::<BF>(
        &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
        &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        1 << 20,
        TRACE_LEN_LOG2,
    );
    let num_calls =
        counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();

    let mut replay_state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
        buffers: &mut buffers[..],
    };

    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _, BF>(
        &mut replay_state,
        &mut replay_ram,
        &tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state, replay_state);

    let decoder_table_data = &preprocessing_data[&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX];
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();

    let oracle = NonMemoryCircuitOracle {
        inner: &buffer[..],
        decoder_table: &witness_gen_data,
        default_pc_value_in_padding: 4,
    };
    let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BF, _, _, _>(
        &add_sub_circuit,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &worker,
        Global,
        Global,
    );
    let full_trace = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
        &add_sub_circuit,
        add_sub_lui_auipc_mod::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &TableDriver::new(),
        &worker,
        Global,
        Global,
    );
    ensure_memory_trace_consistency(&memory_trace, &full_trace);

    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    let whir_schedule = WhirSchedule::default_for_tests_80_bits();
    let setup = GKRSetup::construct(
        &TableDriver::new(),
        &decoder_table_data,
        trace_len,
        &add_sub_circuit,
    );
    let setup_commitment = setup.commit::<DefaultTreeConstructor>(
        &twiddles,
        whir_schedule.base_lde_factor,
        whir_schedule.whir_steps_schedule[0],
        whir_schedule.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );
    let subcap_size = whir_schedule.cap_size / whir_schedule.base_lde_factor;
    let context = make_test_context(64 * 1024, 1024);
    let gpu_setup_host = Arc::new(
        GpuGKRSetupHost::precompute_from_cpu_setup(
            &setup,
            whir_schedule.base_lde_factor.trailing_zeros(),
            whir_schedule.whir_steps_schedule[0] as u32,
            whir_schedule.cap_size.trailing_zeros(),
            &context,
        )
        .unwrap(),
    );
    let mut gpu_setup_transfer =
        GpuGKRSetupTransfer::new(Arc::clone(&gpu_setup_host), &context).unwrap();
    gpu_setup_transfer.schedule_transfer(&context).unwrap();
    context.get_h2d_stream().synchronize().unwrap();

    let cpu_setup_caps = stage1_caps_from_tree(&setup_commitment.tree, subcap_size);
    let gpu_setup_caps = gpu_setup_transfer.trace_holder.get_tree_caps();
    assert_eq!(gpu_setup_caps, cpu_setup_caps, "setup caps diverged");

    let h_decoder_table = witness_gen_data
        .iter()
        .copied()
        .map(ExecutorFamilyDecoderData::from)
        .collect_vec();
    let mut d_decoder_table = context
        .alloc(h_decoder_table.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(
        &mut d_decoder_table,
        &h_decoder_table,
        context.get_exec_stream(),
    )
    .unwrap();
    let mut trace_data = context
        .alloc(buffer.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut trace_data, &buffer[..], context.get_exec_stream()).unwrap();
    let gpu_trace = TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(
        UnrolledNonMemoryTraceDevice {
            tracing_data: trace_data,
        },
    ));
    let mut stage1_output = GpuGKRStage1Output::generate(
        CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
            UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
        )),
        &add_sub_circuit,
        &gpu_setup_transfer,
        if add_sub_circuit.has_decoder_lookup {
            Some(&d_decoder_table)
        } else {
            None
        },
        &gpu_trace,
        &context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let (mem_oracle, wit_oracle) = stage1::stage1::<BF, DefaultTreeConstructor>(
        &full_trace,
        &twiddles,
        whir_schedule.base_lde_factor,
        whir_schedule.whir_steps_schedule[0],
        whir_schedule.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );
    let cpu_memory_caps = stage1_caps_from_tree(&mem_oracle.tree, subcap_size);
    let gpu_memory_caps = stage1_output.memory_trace_holder.get_tree_caps();
    if gpu_memory_caps != cpu_memory_caps {
        let first_mismatch = describe_first_trace_holder_column_mismatch(
            &stage1_output.memory_trace_holder,
            &full_trace.column_major_memory_trace,
            NUM_CYCLES_PER_CHUNK,
            &context,
        )
        .unwrap_or_else(|| "no flat-column mismatch found despite cap divergence".to_string());
        panic!("memory caps diverged; first flat mismatch: {first_mismatch}");
    }

    let cpu_witness_caps = stage1_caps_from_tree(&wit_oracle.tree, subcap_size);
    let gpu_witness_caps = stage1_output.witness_trace_holder.get_tree_caps();
    assert_eq!(gpu_witness_caps, cpu_witness_caps, "witness caps diverged");

    assert_generic_family_mapping_contract(
        &stage1_output.lookup_mappings,
        &full_trace,
        num_calls,
        &context,
    );
    let expected_range_check = full_trace
        .range_check_16_lookup_mapping
        .iter()
        .flat_map(|column| column.iter().map(|value| u32::from(*value)))
        .collect_vec();
    let gpu_range_check =
        copy_u32_device_slice_to_host(stage1_output.lookup_mappings.range_check_16(), &context);
    assert_eq!(gpu_range_check, expected_range_check);
    let expected_timestamp = full_trace
        .timestamp_range_check_lookup_mapping
        .iter()
        .flat_map(|column| column.iter().copied())
        .collect_vec();
    let gpu_timestamp =
        copy_u32_device_slice_to_host(stage1_output.lookup_mappings.timestamp(), &context);
    assert_eq!(gpu_timestamp, expected_timestamp);

    let generic_lookup_multiplicities_range = add_sub_circuit
        .witness_layout
        .multiplicities_columns_for_generic_lookup
        .clone();
    if !generic_lookup_multiplicities_range.is_empty() {
        let first_mismatch = describe_first_trace_holder_subrange_mismatch(
            &stage1_output.witness_trace_holder,
            &full_trace.column_major_witness_trace,
            generic_lookup_multiplicities_range.clone(),
            NUM_CYCLES_PER_CHUNK,
            &context,
        );
        assert!(
            first_mismatch.is_none(),
            "generic lookup multiplicity columns diverged: {}",
            first_mismatch.unwrap()
        );
    }

    let mut cpu_transcript_input = Vec::new();
    external_challenges.flatten_into_buffer(&mut cpu_transcript_input);
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &setup_commitment.tree,
            ),
        )
        .into_iter(),
        &mut cpu_transcript_input,
    );
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &mem_oracle.tree,
            ),
        )
        .into_iter(),
        &mut cpu_transcript_input,
    );
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &wit_oracle.tree,
            ),
        )
        .into_iter(),
        &mut cpu_transcript_input,
    );

    let mut gpu_transcript_input = Vec::new();
    external_challenges.flatten_into_buffer(&mut gpu_transcript_input);
    flatten_merkle_caps_iter_into(gpu_setup_caps.into_iter(), &mut gpu_transcript_input);
    flatten_merkle_caps_iter_into(gpu_memory_caps.into_iter(), &mut gpu_transcript_input);
    flatten_merkle_caps_iter_into(gpu_witness_caps.into_iter(), &mut gpu_transcript_input);

    assert_eq!(
        gpu_transcript_input, cpu_transcript_input,
        "initial transcript input diverged",
    );

    let mut cpu_seed = Transcript::commit_initial(&cpu_transcript_input);
    let mut gpu_seed = Transcript::commit_initial(&gpu_transcript_input);
    assert_eq!(gpu_seed, cpu_seed, "initial transcript seed diverged");

    let cpu_lookup_challenges = draw_random_field_els::<BF, E4>(&mut cpu_seed, 3);
    let gpu_lookup_challenges = draw_random_field_els::<BF, E4>(&mut gpu_seed, 3);
    assert_eq!(
        gpu_lookup_challenges, cpu_lookup_challenges,
        "lookup challenges diverged after matching transcript inputs",
    );

    let [lookup_alpha, lookup_additive_part, constraints_batch_challenge]: [E4; 3] =
        cpu_lookup_challenges.try_into().unwrap();
    let mut lookup_challenges_host = unsafe { context.alloc_host_uninit_slice(3) };
    unsafe {
        lookup_challenges_host
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(&[
                lookup_alpha,
                lookup_additive_part,
                constraints_batch_challenge,
            ]);
    }

    let mut gpu_forward_setup = gpu_setup_transfer
        .schedule_forward_setup(&add_sub_circuit, lookup_challenges_host, &context)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let mut gkr_storage = GKRStorage::<BF, E4>::default();
    let preprocessed_generic_lookup = setup.preprocess_generic_lookups(
        &add_sub_circuit,
        lookup_alpha,
        trace_len,
        &mut gkr_storage,
        &worker,
    );

    let mut gpu_generic = vec![E4::ZERO; gpu_forward_setup.generic_lookup_len()];
    memory_copy_async(
        &mut gpu_generic,
        gpu_forward_setup.generic_lookup(),
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    let first_mismatch =
        describe_first_vec_mismatch(&gpu_generic, preprocessed_generic_lookup.as_ref());
    assert!(
        first_mismatch.is_none(),
        "preprocessed generic lookup diverged: {}",
        first_mismatch.unwrap()
    );

    let mut witness_eval_data = full_trace;
    for (layer_idx, layer) in add_sub_circuit.layers.iter().enumerate() {
        forward_loop::evaluate_layer(
            layer_idx,
            layer,
            &mut gkr_storage,
            &add_sub_circuit,
            &external_challenges,
            &mut witness_eval_data,
            trace_len,
            &preprocessed_generic_lookup,
            lookup_additive_part,
            constraints_batch_challenge,
            &worker,
        );
    }

    let final_trace_size_log_2 = 4;
    let (initial_layer_for_sumcheck, dimension_reducing_inputs) =
        dimension_reduction::forward::evaluate_dimension_reduction_forward(
            &mut gkr_storage,
            &add_sub_circuit,
            trace_len.trailing_zeros() as usize,
            final_trace_size_log_2,
            &worker,
        );
    let output_layer_for_sumcheck = &dimension_reducing_inputs[&initial_layer_for_sumcheck];
    let (final_explicit_evaluations, evals_flattened) = collect_final_explicit_evaluations_for_test(
        &gkr_storage,
        output_layer_for_sumcheck,
        1 << final_trace_size_log_2,
    );

    let (gpu_forward_output, gpu_transcript_handoff) = {
        let gpu_forward_output = schedule_forward_pass(
            &gpu_setup_transfer,
            &mut stage1_output,
            &mut gpu_forward_setup,
            &add_sub_circuit,
            &external_challenges,
            final_trace_size_log_2,
            &context,
        )
        .unwrap();
        let gpu_transcript_handoff = gpu_forward_output
            .schedule_transcript_handoff(&context)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        (gpu_forward_output, gpu_transcript_handoff)
    };
    let gpu_final_explicit_evaluations = gpu_transcript_handoff.final_explicit_evaluations();
    let gpu_evals_flattened = gpu_transcript_handoff.flattened_transcript_evaluations();
    drop(gpu_transcript_handoff);

    assert!(!stage1_output.lookup_mappings.has_generic_family());
    assert!(!stage1_output.lookup_mappings.has_range_check_16());
    assert!(!stage1_output.lookup_mappings.has_timestamp());
    assert!(!gpu_forward_setup.has_generic_lookup());
    assert_eq!(
        gpu_forward_output.initial_layer_for_sumcheck,
        initial_layer_for_sumcheck
    );
    assert_eq!(
        gpu_forward_output.dimension_reducing_inputs,
        dimension_reducing_inputs
    );
    assert_gpu_and_cpu_gkr_storage_match(&gpu_forward_output.storage, &gkr_storage, &context);
    assert_eq!(gpu_final_explicit_evaluations, final_explicit_evaluations);
    assert_eq!(gpu_evals_flattened, evals_flattened);
}

#[test]
#[serial]
fn run_basic_unrolled_stagewise_parity_test() {
    type CountersT = DelegationsAndFamiliesCounters;

    // NOTE: these constants must match with ones used in CS crate to produce
    // layout and SSA forms, otherwise derived witness-gen functions may write into
    // invalid locations
    const TRACE_LEN_LOG2: usize = 24;
    const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);
    // load binary

    // let binary = std::fs::read(test_artifact_path("examples/basic_fibonacci/app.bin")).unwrap();
    let binary = std::fs::read(test_artifact_path("examples/hashed_fibonacci/app.bin")).unwrap();
    // let binary = std::fs::read(test_artifact_path("riscv_transpiler/examples/keccak_f1600/app.bin")).unwrap();
    assert_eq!(binary.len() % 4, 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    // let text_section =
    //     std::fs::read(test_artifact_path("examples/basic_fibonacci/app.text")).unwrap();
    let text_section =
        std::fs::read(test_artifact_path("examples/hashed_fibonacci/app.text")).unwrap();
    // let text_section =
    //     std::fs::read(test_artifact_path("riscv_transpiler/examples/keccak_f1600/app.text"))
    //         .unwrap();
    assert_eq!(text_section.len() % 4, 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    // first run to capture minimal information
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text_section);

    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);
    let cycles_bound = 1 << 20;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter =
        SimpleSnapshotter::<CountersT, { ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(
            cycles_bound,
            state,
        );
    let mut non_determinism = QuasiUARTSource::new_with_reads(vec![15, 1]);

    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<_, _, _, BF>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_program_finished); // check that we reached looping state (ie. end state for our vm)

    let counters = snapshotter.snapshots.last().unwrap().state.counters;

    let shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(&worker, Global);
    let total_shuffle_entries: usize = shuffle_ram_touched_addresses.iter().map(Vec::len).sum();
    assert_ne!(
        total_shuffle_entries, 0,
        "expected RAM touches for stagewise parity test"
    );

    // let flattened_inits_and_teardowns: Vec<_> = shuffle_ram_touched_addresses
    //     .into_iter()
    //     .flatten()
    //     .collect();

    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

    let memory_argument_alpha =
        E4::from_array_of_base([BF::new(2), BF::new(5), BF::new(42), BF::new(123)]);
    let permutation_argument_additive_part =
        E4::from_array_of_base([BF::new(7), BF::new(11), BF::new(1024), BF::new(8000)]);

    let permutation_argument_linearization_challenges: [E4; NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let external_challenges: GKRExternalChallenges<BF, E4> = GKRExternalChallenges {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    };

    // evaluate memory witness
    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BF,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
        ],
    );

    assert!(
        counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<MUL_DIV_CIRCUIT_FAMILY_IDX>() < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );

    let add_sub_circuit = compile_unrolled_circuit_state_transition_into_gkr::<BF>(
        &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
        &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        1 << 20,
        TRACE_LEN_LOG2,
    );

    let num_calls =
        counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();

    let mut state = snapshotter.initial_snapshot.state;

    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());

    let mut ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
        buffers: &mut buffers[..],
    };

    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _, BF>(
        &mut state,
        &mut ram,
        &tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state, state);

    let decoder_table_data = &preprocessing_data[&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX];
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();

    let oracle = NonMemoryCircuitOracle {
        inner: &buffer[..],
        decoder_table: &witness_gen_data,
        default_pc_value_in_padding: 4,
    };

    let memory_trace = evaluate_gkr_memory_witness_for_executor_family::<BF, _, _, _>(
        &add_sub_circuit,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &worker,
        Global,
        Global,
    );

    let full_trace = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
        &add_sub_circuit,
        add_sub_lui_auipc_mod::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &TableDriver::new(),
        &worker,
        Global,
        Global,
    );
    ensure_memory_trace_consistency(&memory_trace, &full_trace);

    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    let whir_schedule = WhirSchedule::default_for_tests_80_bits();
    let base_lde_factor = whir_schedule.base_lde_factor;
    let tree_cap_size = whir_schedule.cap_size;
    let setup = GKRSetup::construct(
        &TableDriver::new(),
        &decoder_table_data,
        trace_len,
        &add_sub_circuit,
    );
    let whir_first_fold_step_log2 = 1usize;

    let setup_commitment = setup.commit(
        &twiddles,
        base_lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );
    let log_lde_factor = base_lde_factor.trailing_zeros();
    let log_rows_per_leaf = whir_first_fold_step_log2 as u32;
    let log_tree_cap_size = tree_cap_size.trailing_zeros();
    let subcap_size = tree_cap_size / base_lde_factor;
    let context = make_test_context(64 * 1024, 1024);
    let gpu_setup_host = Arc::new(
        GpuGKRSetupHost::precompute_from_cpu_setup(
            &setup,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
            &context,
        )
        .unwrap(),
    );
    let mut gpu_setup_transfer =
        GpuGKRSetupTransfer::new(Arc::clone(&gpu_setup_host), &context).unwrap();
    {
        let _range = range!("test.gpu.setup_transfer");
        gpu_setup_transfer.schedule_transfer(&context).unwrap();
        context.get_h2d_stream().synchronize().unwrap();
    }

    let now = std::time::Instant::now();
    assert_eq!(add_sub_circuit.trace_len, trace_len);
    assert_eq!(full_trace.column_major_memory_trace[0].len(), trace_len);

    let (mem_oracle, wit_oracle) = stage1::stage1::<BF, DefaultTreeConstructor>(
        &full_trace,
        &twiddles,
        whir_schedule.base_lde_factor,
        whir_schedule.whir_steps_schedule[0],
        whir_schedule.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );

    let trace_holder_caps = gpu_setup_transfer.trace_holder.get_tree_caps();
    let setup_caps = stage1_caps_from_tree(&setup_commitment.tree, subcap_size);
    assert_eq!(trace_holder_caps, setup_caps);
    let h_decoder_table = witness_gen_data
        .iter()
        .copied()
        .map(|d| d.into())
        .collect_vec();
    let mut d_decoder_table = context
        .alloc(h_decoder_table.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(
        &mut d_decoder_table,
        &h_decoder_table,
        context.get_exec_stream(),
    )
    .unwrap();
    let mut trace_data = context
        .alloc(buffer.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut trace_data, &buffer[..], context.get_exec_stream()).unwrap();
    let gpu_trace = TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(
        UnrolledNonMemoryTraceDevice {
            tracing_data: trace_data,
        },
    ));
    let mut stage1_output = {
        let _range = range!("test.gpu.stage1.generate");
        let stage1_output = GpuGKRStage1Output::generate(
            CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
                UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
            )),
            &add_sub_circuit,
            &gpu_setup_transfer,
            if add_sub_circuit.has_decoder_lookup {
                Some(&d_decoder_table)
            } else {
                None
            },
            &gpu_trace,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        stage1_output
    };

    let memory_caps = stage1_caps_from_tree(&mem_oracle.tree, subcap_size);
    assert_eq!(
        stage1_output.memory_trace_holder.get_tree_caps(),
        memory_caps
    );
    let witness_caps = stage1_caps_from_tree(&wit_oracle.tree, subcap_size);
    assert_eq!(
        stage1_output.witness_trace_holder.get_tree_caps(),
        witness_caps
    );

    let mut transcript_input = vec![];
    external_challenges.flatten_into_buffer(&mut transcript_input);
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &setup_commitment.tree,
            ),
        )
        .into_iter(),
        &mut transcript_input,
    );
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &mem_oracle.tree,
            ),
        )
        .into_iter(),
        &mut transcript_input,
    );
    flatten_merkle_caps_iter_into(
        Some(
            <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<BF>>::get_cap(
                &wit_oracle.tree,
            ),
        )
        .into_iter(),
        &mut transcript_input,
    );

    let mut seed = Transcript::commit_initial(&transcript_input);
    let challenges: Vec<E4> = draw_random_field_els::<BF, E4>(&mut seed, 3);
    let [lookup_alpha, lookup_additive_part, constraints_batch_challenge] =
        challenges.try_into().unwrap();

    let mut lookup_challenges_host = unsafe { context.alloc_host_uninit_slice(3) };
    let lookup_challenges = [
        lookup_alpha,
        lookup_additive_part,
        constraints_batch_challenge,
    ];
    unsafe {
        lookup_challenges_host
            .get_mut_accessor()
            .get_mut()
            .copy_from_slice(&lookup_challenges);
    }
    let mut gpu_forward_setup = {
        let _range = range!("test.gpu.forward_setup.schedule");
        let gpu_forward_setup = gpu_setup_transfer
            .schedule_forward_setup(&add_sub_circuit, lookup_challenges_host, &context)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        gpu_forward_setup
    };

    let mut gkr_storage = GKRStorage::<BF, E4>::default();
    let preprocessed_generic_lookup = setup.preprocess_generic_lookups(
        &add_sub_circuit,
        lookup_alpha,
        trace_len,
        &mut gkr_storage,
        &worker,
    );

    let mut witness_eval_data = full_trace;
    for (layer_idx, layer) in add_sub_circuit.layers.iter().enumerate() {
        forward_loop::evaluate_layer(
            layer_idx,
            layer,
            &mut gkr_storage,
            &add_sub_circuit,
            &external_challenges,
            &mut witness_eval_data,
            trace_len,
            &preprocessed_generic_lookup,
            lookup_additive_part,
            constraints_batch_challenge,
            &worker,
        );
    }

    let final_trace_size_log_2 = 4;
    let (initial_layer_for_sumcheck, dimension_reducing_inputs) =
        dimension_reduction::forward::evaluate_dimension_reduction_forward(
            &mut gkr_storage,
            &add_sub_circuit,
            trace_len.trailing_zeros() as usize,
            final_trace_size_log_2,
            &worker,
        );
    let output_layer_for_sumcheck = &dimension_reducing_inputs[&initial_layer_for_sumcheck];
    let (final_explicit_evaluations, evals_flattened) = collect_final_explicit_evaluations_for_test(
        &gkr_storage,
        output_layer_for_sumcheck,
        1 << final_trace_size_log_2,
    );

    let (gpu_forward_output, gpu_transcript_handoff) = {
        let _range = range!("test.gpu.forward.schedule");
        let gpu_forward_output = schedule_forward_pass(
            &gpu_setup_transfer,
            &mut stage1_output,
            &mut gpu_forward_setup,
            &add_sub_circuit,
            &external_challenges,
            final_trace_size_log_2,
            &context,
        )
        .unwrap();
        let gpu_transcript_handoff = gpu_forward_output
            .schedule_transcript_handoff(&context)
            .unwrap();
        context.get_exec_stream().synchronize().unwrap();
        (gpu_forward_output, gpu_transcript_handoff)
    };
    let gpu_final_explicit_evaluations = gpu_transcript_handoff.final_explicit_evaluations();
    let gpu_evals_flattened = gpu_transcript_handoff.flattened_transcript_evaluations();
    drop(gpu_transcript_handoff);
    {
        let _range = range!("test.gpu.forward.readback_asserts");
        assert!(!stage1_output.lookup_mappings.has_generic_family());
        assert!(!stage1_output.lookup_mappings.has_range_check_16());
        assert!(!stage1_output.lookup_mappings.has_timestamp());
        assert!(!gpu_forward_setup.has_generic_lookup());
        assert_eq!(
            gpu_forward_output.initial_layer_for_sumcheck,
            initial_layer_for_sumcheck
        );
        assert_eq!(
            gpu_forward_output.dimension_reducing_inputs,
            dimension_reducing_inputs
        );
        assert_eq!(gpu_final_explicit_evaluations, final_explicit_evaluations);
        assert_eq!(gpu_evals_flattened, evals_flattened);
    }
    drop(gpu_forward_setup);

    let (copy_input, copy_output) = add_sub_circuit
        .layers
        .iter()
        .flat_map(|layer| {
            layer
                .gates
                .iter()
                .chain(layer.gates_with_external_connections.iter())
        })
        .find_map(|gate| match &gate.enforced_relation {
            NoFieldGKRRelation::Copy { input, output } => Some((*input, *output)),
            _ => None,
        })
        .expect("test circuit must contain a Copy relation");
    if let Some(input_poly) = gpu_forward_output.storage.try_get_base_poly(copy_input) {
        let output_poly = gpu_forward_output
            .storage
            .try_get_base_poly(copy_output)
            .expect("copy output must preserve base-field representation");
        assert!(input_poly.shares_backing_with(output_poly));
    } else {
        let input_poly = gpu_forward_output
            .storage
            .try_get_ext_poly(copy_input)
            .expect("copy input must exist");
        let output_poly = gpu_forward_output
            .storage
            .try_get_ext_poly(copy_output)
            .expect("copy output must preserve extension-field representation");
        assert!(input_poly.shares_backing_with(output_poly));
    }

    let seed_before_explicit_commit = seed;
    commit_field_els::<BF, E4>(&mut seed, &evals_flattened);
    let seed_after_cpu_explicit_commit = seed;

    let mut gpu_seed = seed_before_explicit_commit;
    commit_field_els::<BF, E4>(&mut gpu_seed, &gpu_evals_flattened);
    assert_eq!(gpu_seed, seed_after_cpu_explicit_commit);

    let num_challenges = final_trace_size_log_2 + 1;
    let mut challenges = draw_random_field_els::<BF, E4>(&mut seed, num_challenges);
    let expected_challenges = challenges.clone();
    let mut gpu_challenges = draw_random_field_els::<BF, E4>(&mut gpu_seed, num_challenges);
    assert_eq!(gpu_challenges, expected_challenges);
    let batching_challenge = challenges.pop().unwrap();
    let gpu_batching_challenge = gpu_challenges.pop().unwrap();
    assert_eq!(gpu_batching_challenge, batching_challenge);

    let evaluation_point = challenges;
    let gpu_evaluation_point = gpu_challenges;
    assert_eq!(gpu_evaluation_point, evaluation_point);
    assert_eq!(gpu_seed, seed);
    let backward_initial_seed = seed;
    let cpu_initial_claims = compute_initial_sumcheck_claims_for_test(
        &gkr_storage,
        &evaluation_point,
        output_layer_for_sumcheck,
        &worker,
    );
    let gpu_initial_claims = compute_initial_sumcheck_claims_from_explicit_evaluations_for_test(
        &gpu_final_explicit_evaluations,
        &evaluation_point,
        &worker,
    );
    assert_eq!(gpu_initial_claims, cpu_initial_claims);
    let [claim_readset, claim_writeset, claim_rangechecknum, claim_rangecheckden, claim_timechecknum, claim_timecheckden, claim_lookupnum, claim_lookupden] =
        cpu_initial_claims;
    let gpu_backward_state = gpu_forward_output.into_dimension_reducing_backward_state();

    let output_map = output_layer_for_sumcheck;
    let mut top_layer_claims: BTreeMap<GKRAddress, E4> = BTreeMap::new();
    top_layer_claims.insert(
        output_map[&OutputType::PermutationProduct].output[0],
        claim_readset,
    );
    top_layer_claims.insert(
        output_map[&OutputType::PermutationProduct].output[1],
        claim_writeset,
    );
    top_layer_claims.insert(
        output_map[&OutputType::Lookup16Bits].output[0],
        claim_rangechecknum,
    );
    top_layer_claims.insert(
        output_map[&OutputType::Lookup16Bits].output[1],
        claim_rangecheckden,
    );
    top_layer_claims.insert(
        output_map[&OutputType::LookupTimestamps].output[0],
        claim_timechecknum,
    );
    top_layer_claims.insert(
        output_map[&OutputType::LookupTimestamps].output[1],
        claim_timecheckden,
    );
    top_layer_claims.insert(
        output_map[&OutputType::GenericLookup].output[0],
        claim_lookupnum,
    );
    top_layer_claims.insert(
        output_map[&OutputType::GenericLookup].output[1],
        claim_lookupden,
    );

    let mut claims_for_layers: BTreeMap<usize, BTreeMap<GKRAddress, E4>> = BTreeMap::new();
    let mut points_for_claims_at_layer = BTreeMap::new();
    claims_for_layers.insert(initial_layer_for_sumcheck + 1, top_layer_claims.clone());
    points_for_claims_at_layer.insert(initial_layer_for_sumcheck + 1, evaluation_point.clone());

    let mut sumcheck_intermediate_values = BTreeMap::new();
    let mut sumcheck_batching_challenge = batching_challenge;
    let mut reduced_trace_size_log_2 = final_trace_size_log_2;
    {
        let _range = range!("test.cpu.sumcheck.dimension_reduction");
        for (layer_idx, layer) in dimension_reducing_inputs.into_iter().rev() {
            let _layer_range = range!("test.cpu.sumcheck.dimension_reduction.layer.{}", layer_idx);
            let proof = sumcheck_loop::evaluate_dimension_reducing_sumcheck_for_layer(
                layer_idx,
                &layer,
                &mut points_for_claims_at_layer,
                &mut claims_for_layers,
                &mut gkr_storage,
                &mut sumcheck_batching_challenge,
                &mut seed,
                1 << reduced_trace_size_log_2,
                &worker,
            );
            sumcheck_intermediate_values.insert(layer_idx, proof);
            reduced_trace_size_log_2 += 1;
        }
    }

    assert_eq!(1 << reduced_trace_size_log_2, trace_len);

    {
        let _range = range!("test.cpu.sumcheck.main_layers");
        for (layer_idx, layer) in add_sub_circuit.layers.iter().enumerate().rev() {
            let _layer_range = range!("test.cpu.sumcheck.main_layers.layer.{}", layer_idx);

            let proof = sumcheck_loop::evaluate_sumcheck_for_layer(
                layer_idx,
                layer,
                &mut points_for_claims_at_layer,
                &mut claims_for_layers,
                &mut gkr_storage,
                &mut sumcheck_batching_challenge,
                &add_sub_circuit,
                trace_len,
                lookup_additive_part,
                constraints_batch_challenge,
                &external_challenges,
                &mut seed,
                &worker,
            );
            sumcheck_intermediate_values.insert(layer_idx, proof);
        }
    }

    let mut gpu_backward_execution = {
        let _range = range!("test.gpu.sumcheck.backward_workflow");
        gpu_backward_state
            .schedule_execute_backward_workflow(
                add_sub_circuit.clone(),
                initial_layer_for_sumcheck + 1,
                top_layer_claims.clone(),
                evaluation_point.clone(),
                backward_initial_seed,
                batching_challenge,
                lookup_additive_part,
                constraints_batch_challenge,
                &context,
            )
            .unwrap()
            .wait(&context)
            .unwrap()
    };

    assert_layer_points_eq_for_test(
        &gpu_backward_execution.points_for_claims_at_layer,
        &points_for_claims_at_layer,
    );
    assert_backward_claims_eq_before_base_layer_expansion(
        &gpu_backward_execution.claims_for_layers,
        &claims_for_layers,
    );
    assert_eq!(
        gpu_backward_execution
            .points_for_claims_at_layer
            .get(&1)
            .cloned(),
        points_for_claims_at_layer.get(&1).cloned(),
        "layer 1 claim point diverged before layer-0 proof comparison"
    );
    assert_eq!(
        gpu_backward_execution.claims_for_layers.get(&1).cloned(),
        claims_for_layers.get(&1).cloned(),
        "layer 1 claims diverged before layer-0 proof comparison"
    );

    for (layer_idx, expected) in sumcheck_intermediate_values.iter() {
        let actual = gpu_backward_execution
            .proofs
            .get(layer_idx)
            .unwrap_or_else(|| panic!("missing GPU proof for layer {layer_idx}"));
        assert_sumcheck_intermediate_values_eq_for_test_with_layer(actual, expected, *layer_idx);
    }
    assert_eq!(
        gpu_backward_execution.next_batching_challenge,
        sumcheck_batching_challenge
    );

    let base_layer_z = gpu_backward_execution
        .points_for_claims_at_layer
        .get(&0)
        .expect("must have base layer point");
    let raw_gpu_base_layer_claims = gpu_backward_execution
        .claims_for_layers
        .get(&0)
        .cloned()
        .expect("must have raw layer-0 claims after backward");
    let eq_precomputed = make_eq_poly_in_full(base_layer_z, &worker);
    let eq_at_z = eq_precomputed.last().unwrap();
    let layer_desc = &add_sub_circuit.layers[0];

    let (
        cpu_base_layer_claims,
        cpu_extra_evaluations_from_caching_relations,
        cpu_extra_evaluations_transcript_batches,
        cpu_mem_polys_claims,
        cpu_wit_polys_claims,
        cpu_setup_polys_claims,
    ) = {
        let mut cpu_base_layer_claims = raw_gpu_base_layer_claims.clone();
        let mut cpu_extra_evaluations_from_caching_relations = BTreeMap::new();
        let mut cpu_extra_evaluations_transcript_batches = Vec::new();
        for (cached_addr, relation) in layer_desc.cached_relations.iter() {
            debug_assert!(
                cpu_base_layer_claims.contains_key(cached_addr),
                "Missing claim for cached address {:?}",
                cached_addr
            );

            for dep in relation.dependencies() {
                if cpu_base_layer_claims.contains_key(&dep) {
                    continue;
                }
                match dep {
                    GKRAddress::BaseLayerWitness(_)
                    | GKRAddress::BaseLayerMemory(_)
                    | GKRAddress::Setup(_) => {
                        let values = gkr_storage.get_base_layer(dep);
                        let evaluation = evaluate_base_poly_with_eq::<BF, E4>(values, &eq_at_z[..]);
                        cpu_base_layer_claims.insert(dep, evaluation);
                        cpu_extra_evaluations_from_caching_relations.insert(dep, evaluation);
                    }
                    _ => {
                        panic!(
                            "Unexpected dependency address {:?} for cached relation {:?}",
                            dep, cached_addr
                        );
                    }
                }
            }

            if !cpu_extra_evaluations_from_caching_relations.is_empty() {
                cpu_extra_evaluations_transcript_batches.push(
                    cpu_extra_evaluations_from_caching_relations
                        .values()
                        .copied()
                        .collect_vec(),
                );
            }
        }

        let mut mem_polys_claims = Vec::with_capacity(add_sub_circuit.memory_layout.total_width);
        for i in 0..add_sub_circuit.memory_layout.total_width {
            let key = GKRAddress::BaseLayerMemory(i);
            let evaluation =
                evaluate_base_poly_with_eq::<BF, E4>(gkr_storage.get_base_layer(key), &eq_at_z[..]);
            mem_polys_claims.push(evaluation);
        }

        let mut wit_polys_claims = Vec::with_capacity(add_sub_circuit.witness_layout.total_width);
        for i in 0..add_sub_circuit.witness_layout.total_width {
            let key = GKRAddress::BaseLayerWitness(i);
            let evaluation =
                evaluate_base_poly_with_eq::<BF, E4>(gkr_storage.get_base_layer(key), &eq_at_z[..]);
            wit_polys_claims.push(evaluation);
        }

        let mut setup_polys_claims = Vec::with_capacity(setup.hypercube_evals.len());
        for i in 0..setup.hypercube_evals.len() {
            let key = GKRAddress::Setup(i);
            let evaluation =
                evaluate_base_poly_with_eq::<BF, E4>(gkr_storage.get_base_layer(key), &eq_at_z[..]);
            setup_polys_claims.push(evaluation);
        }

        (
            cpu_base_layer_claims,
            cpu_extra_evaluations_from_caching_relations,
            cpu_extra_evaluations_transcript_batches,
            mem_polys_claims,
            wit_polys_claims,
            setup_polys_claims,
        )
    };

    let gpu_base_claims = {
        let _range = range!("test.gpu.base_layer_claims.prepare");
        prepare_base_layer_claims(
            layer_desc,
            base_layer_z,
            &raw_gpu_base_layer_claims,
            &gpu_setup_transfer.trace_holder,
            &stage1_output.memory_trace_holder,
            &stage1_output.witness_trace_holder,
            &context,
        )
        .unwrap()
    };

    assert_eq!(gpu_base_claims.completed_claims, cpu_base_layer_claims);
    assert_eq!(
        gpu_base_claims.extra_evaluations_from_caching_relations,
        cpu_extra_evaluations_from_caching_relations
    );
    assert_eq!(
        gpu_base_claims.extra_evaluations_transcript_batches,
        cpu_extra_evaluations_transcript_batches
    );
    assert_eq!(gpu_base_claims.mem_polys_claims, cpu_mem_polys_claims);
    assert_eq!(gpu_base_claims.wit_polys_claims, cpu_wit_polys_claims);
    assert_eq!(gpu_base_claims.setup_polys_claims, cpu_setup_polys_claims);

    for i in 0..add_sub_circuit.memory_layout.total_width {
        assert_eq!(
            gpu_base_claims.claim_for_address(GKRAddress::BaseLayerMemory(i)),
            Some(cpu_mem_polys_claims[i]),
        );
    }
    for i in 0..add_sub_circuit.witness_layout.total_width {
        assert_eq!(
            gpu_base_claims.claim_for_address(GKRAddress::BaseLayerWitness(i)),
            Some(cpu_wit_polys_claims[i]),
        );
    }
    for i in 0..setup.hypercube_evals.len() {
        assert_eq!(
            gpu_base_claims.claim_for_address(GKRAddress::Setup(i)),
            Some(cpu_setup_polys_claims[i]),
        );
    }

    let mut gpu_seed_after_base_layer_claims = gpu_backward_execution.updated_seed;
    for transcript_input in gpu_base_claims.extra_evaluations_transcript_batches.iter() {
        commit_field_els::<BF, E4>(&mut gpu_seed_after_base_layer_claims, &transcript_input);
    }
    assert_eq!(gpu_seed_after_base_layer_claims, seed);

    drop(preprocessed_generic_lookup);
    gpu_backward_execution
        .claims_for_layers
        .insert(0, gpu_base_claims.completed_claims.clone());

    drop(gkr_storage);

    let whir_batching_challenge = draw_random_field_els::<BF, E4>(&mut seed, 1)[0];
    let whir_schedule = whir_schedule.clone();
    stage1_output
        .memory_trace_holder
        .ensure_cosets_materialized(&context)
        .unwrap();
    stage1_output
        .witness_trace_holder
        .ensure_cosets_materialized(&context)
        .unwrap();
    gpu_setup_transfer
        .trace_holder
        .ensure_cosets_materialized(&context)
        .unwrap();
    // The per-round WHIR check takes tree caps from the trace holders, so we
    // capture the full GPU WHIR proof from this call rather than running a
    // second gpu_whir_fold_supported_path_with_external_pow (which would try to
    // take the already-consumed tree caps and panic).
    let gpu_whir_proof = {
        let _range = range!("test.gpu.whir.recursive_oracle_parity");
        assert_recursive_whir_oracle_parity_for_supported_path(
            &mem_oracle,
            &gpu_base_claims.mem_polys_claims,
            &mut stage1_output.memory_trace_holder,
            &wit_oracle,
            &gpu_base_claims.wit_polys_claims,
            &mut stage1_output.witness_trace_holder,
            &setup_commitment,
            &gpu_base_claims.setup_polys_claims,
            &mut gpu_setup_transfer.trace_holder,
            base_layer_z,
            whir_schedule.base_lde_factor,
            whir_batching_challenge,
            &whir_schedule,
            &twiddles,
            seed.clone(),
            trace_len.trailing_zeros() as usize,
            &worker,
            &context,
        )
    };
    let cpu_whir_proof = {
        let _range = range!("test.cpu.whir_fold");
        whir_fold(
            mem_oracle,
            gpu_base_claims.mem_polys_claims.clone(),
            wit_oracle,
            gpu_base_claims.wit_polys_claims.clone(),
            &setup_commitment,
            gpu_base_claims.setup_polys_claims.clone(),
            base_layer_z.clone(),
            whir_schedule.base_lde_factor,
            whir_batching_challenge,
            whir_schedule.whir_steps_schedule.clone(),
            whir_schedule.whir_queries_schedule.clone(),
            whir_schedule.whir_steps_lde_factors.clone(),
            whir_schedule.whir_pow_schedule.clone(),
            &twiddles,
            seed,
            whir_schedule.cap_size,
            trace_len.trailing_zeros() as usize,
            &worker,
        )
    };
    assert_whir_proof_eq_for_test(&gpu_whir_proof, &cpu_whir_proof);
    let whir_proof = gpu_whir_proof;

    let [read_set_computed, write_set_computed] = final_explicit_evaluations
        .get(&OutputType::PermutationProduct)
        .expect("must be present")
        .clone()
        .map(|els| {
            let mut result = E4::ONE;
            for el in els.iter() {
                result.mul_assign(el);
            }
            result
        });
    let mut grand_product_accumulator_computed = read_set_computed;
    grand_product_accumulator_computed
        .mul_assign(&write_set_computed.inverse().expect("must not be zero"));

    let _proof = GKRProof::<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
        external_challenges,
        final_explicit_evaluations,
        sumcheck_intermediate_values,
        whir_proof,
        grand_product_accumulator_computed,
    };
    let _elapsed = now.elapsed();
}

#[allow(unused_imports)]
mod add_sub_lui_auipc_mod {
    use crate::primitives::field::BF;
    use cs::oracle::Placeholder;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
    use cs::witness_placer::WitnessTypeSet;
    use cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use field::baby_bear::base::BabyBearField;
    use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use prover::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
    use prover::gkr::witness_gen::witness_proxy::WitnessProxy;

    include!(
        "../../../prover/compiled_circuits/add_sub_lui_auipc_mop_preprocessed_generated_gkr.rs"
    );

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BF>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BF, true>,
            ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BF>,
        >;
        fn_ptr(proxy);
    }
}
