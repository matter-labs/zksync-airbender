use super::gkr::{
    backward::{
        GpuGKRDimensionReducingBackwardState, GpuGKRMainLayerKernelKind,
        GpuGKRMainLayerSumcheckLayerPlan,
    },
    base_layer_claims::prepare_base_layer_claims,
    forward::schedule_forward_pass as schedule_forward_pass_impl,
    setup::{GpuGKRSetupHost, GpuGKRSetupTransfer},
    stage1::{GpuGKRStage1Output, GpuGKRTraceGeometry},
    GpuGKRStorage,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::{set_by_ref, SetByRef};
use crate::primitives::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::primitives::nvtx::scoped_range;
use crate::primitives::static_host::alloc_static_pinned_box_from_slice;
use crate::prover::proof::layout::{placeholder_inputs_for_prove, ProofLayout};
use crate::prover::proof::{
    grand_product_accumulator_from_explicit_evaluations, prove, GpuGKRProofJob,
};
use crate::prover::test_utils::{
    make_test_context, make_test_context_with_device_allocator_block_log_size,
};
use crate::prover::trace::decoder::DecoderTableTransfer;
use crate::prover::trace::holder::TraceHolder;
use crate::prover::trace::memory::commit_memory;
use crate::prover::trace::tracing_data::{
    DelegationTracingDataDevice, InitsAndTeardownsTransfer, TracingDataDevice, TracingDataHost,
    TracingDataTransfer, UnrolledTracingDataDevice, UnrolledTracingDataHost,
};
use crate::prover::whir::fold::{
    clone_scheduled_whir_pre_pow_seeds, debug_apply_initial_fold_challenge_for_test,
    debug_build_initial_batched_evals_for_test, debug_build_initial_fold_state_for_test,
    debug_build_initial_state_for_test, debug_build_initial_state_snapshots_for_test,
    debug_initial_round_checkpoint_for_test, schedule_gpu_whir_fold_with_sources,
    take_scheduled_whir_proof,
};
use crate::prover::whir::GpuWhirExtensionOracle;
use crate::witness::trace::ChunkedTraceHolder;
use crate::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, InitsAndTeardownsTraceDevice, InitsAndTeardownsTraceHost,
    UnrolledMemoryTraceDevice, UnrolledNonMemoryTraceDevice, PAGE_SIZE_LOG2,
};

use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::{
    batch_inverse_inplace, bitreverse_enumeration_inplace, domain_generator_for_size,
    materialize_powers_serial_starting_with_elem, materialize_powers_serial_starting_with_one,
    Twiddles,
};

use itertools::Itertools;

use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{
    Counters, DelegationsAndFamiliesCounters, RamWithRomRegion, ReplayBuffer, SimpleSnapshotter,
    SimpleTape, State, VM,
};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    BigintDelegationDestinationHolder, BlakeDelegationDestinationHolder,
    KeccakDelegationDestinationHolder, MemDestinationHolder, MemoryOpcodeTracingDataWithTimestamp,
    NonMemDestinationHolder, NonMemoryOpcodeTracingDataWithTimestamp,
};
use serial_test::serial;
use std::alloc::Global;
use std::collections::BTreeMap;
use std::ops::DerefMut;
use std::path::PathBuf;
use std::sync::Arc;
use worker::Worker;

const BASIC_UNROLLED_CPU_PARITY_BINARY_PATH: &str =
    "riscv_transpiler/examples/keccak_f1600/app.bin";
const BASIC_UNROLLED_CPU_PARITY_TEXT_PATH: &str = "riscv_transpiler/examples/keccak_f1600/app.text";
const BASIC_UNROLLED_ADD_SUB_LAYOUT_PATH: &str =
    "cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json";
const BASIC_UNROLLED_ADD_SUB_NO_CACHES_LAYOUT_PATH: &str =
    "cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json";

mod asserts;
mod basic_unrolled_parity;
mod commit_memory;
mod delegation_asserts;
mod expected_specs;
mod fixtures;
mod inits_and_teardowns;
mod memory_workflow;
mod poly_helpers;
mod smoke;
mod stagewise;
mod whir_oracle_parity;
mod workflow_parity;

use poly_helpers::*;

use asserts::*;
use delegation_asserts::*;

use expected_specs::*;
use memory_workflow::*;
use whir_oracle_parity::assert_recursive_whir_oracle_parity_for_supported_path;

use crate::upstream::*;
use fixtures::*;

fn test_artifact_path(relative_path: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(relative_path)
}

/// Upload the 3 host-computed lookup challenges (alpha, additive_part, batch) into a
/// `DeviceAllocation<E4>` the way `schedule_forward_setup` now consumes them. Test-only
/// bridge: production code derives these on device; the test fixtures still compute them
/// on host to keep their CPU-parity checks straightforward.
fn upload_lookup_challenges_for_test(
    lookup_challenges_host: &HostAllocation<[E4]>,
    context: &ProverContext,
) -> DeviceAllocation<E4> {
    let len = unsafe { lookup_challenges_host.get_accessor().get().len() };
    let mut d_lookup_challenges: DeviceAllocation<E4> =
        context.alloc(len, AllocationPlacement::BestFit).unwrap();
    memory_copy_async(
        &mut d_lookup_challenges,
        lookup_challenges_host,
        context.get_exec_stream(),
    )
    .unwrap();
    d_lookup_challenges
}

fn read_test_words(relative_path: &str) -> Vec<u32> {
    let bytes = std::fs::read(test_artifact_path(relative_path)).unwrap();
    assert_eq!(bytes.len() % 4, 0);
    bytes
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect()
}

fn deserialize_json_for_test<T: serde::de::DeserializeOwned>(relative_path: &str) -> T {
    let src = std::fs::File::open(test_artifact_path(relative_path)).unwrap();
    serde_json::from_reader(src).unwrap()
}

fn insert_virtual_setup_polys_for_test<F: PrimeField, E: FieldExtension<F> + Field>(
    trace_len: usize,
    gkr_storage: &mut GKRStorage<F, E>,
) {
    if gkr_storage.layers.is_empty() {
        gkr_storage.layers.push(GKRLayerSource::default());
    }
    let base_layer = &mut gkr_storage.layers[0].base_field_inputs;
    let previous = base_layer.insert(
        GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
        BaseFieldPoly::new(materialize_virtual_range_check_setup_poly::<F, Global, 16>(
            trace_len.trailing_zeros(),
        )),
    );
    assert!(previous.is_none());
    let previous = base_layer.insert(
        GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
        BaseFieldPoly::new(materialize_virtual_range_check_setup_poly::<
            F,
            Global,
            TIMESTAMP_COLUMNS_NUM_BITS,
        >(trace_len.trailing_zeros())),
    );
    assert!(previous.is_none());
    let worker = Worker::new();
    let (inits_low, inits_high) = materialize_virtual_inits_and_teardowns_base_address_setup_poly::<
        F,
        Global,
        2,
    >(trace_len.trailing_zeros(), &worker);
    let previous = base_layer.insert(
        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
        BaseFieldPoly::new(inits_low),
    );
    assert!(previous.is_none());
    let previous = base_layer.insert(
        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
        BaseFieldPoly::new(inits_high),
    );
    assert!(previous.is_none());
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

fn setup_geometry_for_test(setup_transfer: &GpuGKRSetupTransfer<'_>) -> GpuGKRTraceGeometry {
    GpuGKRTraceGeometry {
        log_domain_size: setup_transfer.trace_holder.log_domain_size,
        log_lde_factor: setup_transfer.trace_holder.log_lde_factor,
        log_rows_per_leaf: setup_transfer.trace_holder.log_rows_per_leaf,
        log_tree_cap_size: setup_transfer.trace_holder.log_tree_cap_size,
    }
}

fn generate_stage1_output_for_test(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    setup_transfer: &GpuGKRSetupTransfer<'_>,
    decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
    inits_and_teardowns: Option<&InitsAndTeardownsTraceDevice>,
    tracing_data: &TracingDataDevice,
    context: &ProverContext,
) -> CudaResult<GpuGKRStage1Output> {
    GpuGKRStage1Output::generate(
        circuit_type,
        compiled_circuit,
        setup_geometry_for_test(setup_transfer),
        Some(setup_transfer.trace_holder.get_hypercube_evals()),
        decoder_table,
        inits_and_teardowns,
        Some(tracing_data),
        context,
    )
}

fn schedule_forward_pass<E>(
    setup_transfer: &GpuGKRSetupTransfer<'_>,
    stage1: &mut GpuGKRStage1Output,
    forward_setup: &mut super::gkr::setup::GpuGKRForwardSetup<E>,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    final_trace_size_log_2: usize,
    context: &ProverContext,
) -> CudaResult<super::gkr::forward::GpuGKRForwardOutput<BF, E>>
where
    E: FieldExtension<BF>
        + Field
        + crate::ops::simple::SetByRef
        + crate::ops::simple::SetByVal
        + crate::prover::gkr::GpuKernels,
    crate::ops::simple::Add: crate::ops::simple::BinaryOp<E, E, E>,
    crate::ops::simple::Add: crate::ops::simple::BinaryOp<BF, E, E>,
    crate::ops::simple::Add: crate::ops::simple::BinaryOp<E, BF, E>,
    crate::ops::simple::Add: crate::ops::simple::BinaryOp<BF, BF, BF>,
    crate::ops::simple::Mul: crate::ops::simple::BinaryOp<E, E, E>,
    crate::ops::simple::Mul: crate::ops::simple::BinaryOp<BF, E, E>,
    crate::ops::simple::Mul: crate::ops::simple::BinaryOp<E, BF, E>,
    crate::ops::simple::Mul: crate::ops::simple::BinaryOp<BF, BF, BF>,
    crate::ops::simple::Sub: crate::ops::simple::BinaryOp<E, E, E>,
    crate::ops::simple::Sub: crate::ops::simple::BinaryOp<E, BF, E>,
    crate::ops::simple::Sub: crate::ops::simple::BinaryOp<BF, BF, BF>,
{
    schedule_forward_pass_impl(
        Some(&setup_transfer.trace_holder),
        None,
        stage1,
        forward_setup,
        compiled_circuit,
        external_challenges,
        final_trace_size_log_2,
        None,
        context,
    )
}

pub(crate) struct BasicUnrolledFixture {
    pub(crate) context: ProverContext,
    pub(crate) circuit_type: CircuitType,
    pub(crate) compiled_circuit: GKRCircuitArtifact<BF>,
    pub(crate) external_challenges: GKRExternalChallenges<BF, E4>,
    pub(crate) prover_config: ProverConfig,
    pub(crate) final_trace_size_log_2: usize,
    pub(crate) gpu_setup_host: Arc<GpuGKRSetupHost>,
    pub(crate) decoder_table_host:
        Arc<crate::primitives::static_host::StaticPinnedBox<ExecutorFamilyDecoderData>>,
    pub(crate) tracing_data_host: TracingDataHost<Global>,
    pub(crate) memory_tree_caps: Vec<MerkleTreeCapVarLength>,
}

struct BasicUnrolledTransfers<'a> {
    setup_transfer: GpuGKRSetupTransfer<'a>,
    decoder_transfer: Option<DecoderTableTransfer<'a>>,
    tracing_data_transfer: TracingDataTransfer<'a, Global>,
    memory_transfer: crate::prover::trace::memory_transfer::GpuGKRMemoryTransfer<'a>,
}

impl<'a> BasicUnrolledTransfers<'a> {
    fn schedule(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.setup_transfer.schedule_transfer(context)?;
        if let Some(decoder_transfer) = self.decoder_transfer.as_mut() {
            decoder_transfer.schedule_transfer(context)?;
        }
        self.tracing_data_transfer.schedule_transfer(context)?;
        self.memory_transfer.schedule_transfer(context)
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
        let memory_transfer_host = Arc::new(
            crate::prover::trace::memory_transfer::GpuGKRMemoryTransferHost::from_per_coset_caps(
                &self.memory_tree_caps,
                self.gpu_setup_host.log_lde_factor,
                self.gpu_setup_host.log_tree_cap_size,
            )?,
        );
        let memory_transfer = crate::prover::trace::memory_transfer::GpuGKRMemoryTransfer::new(
            memory_transfer_host,
            context,
        )?;

        Ok(BasicUnrolledTransfers {
            setup_transfer,
            decoder_transfer,
            tracing_data_transfer,
            memory_transfer,
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
    ) -> CudaResult<GpuGKRProofJob<'static>> {
        let BasicUnrolledTransfers {
            setup_transfer,
            decoder_transfer,
            tracing_data_transfer,
            memory_transfer,
        } = transfers;

        prove::<Global>(
            self.circuit_type,
            self.compiled_circuit.clone(),
            self.external_challenges,
            &self.prover_config,
            self.final_trace_size_log_2,
            Some(setup_transfer),
            decoder_transfer,
            None,
            Some(tracing_data_transfer),
            memory_transfer,
            &self.context,
        )
    }

    fn schedule_prove(&self) -> CudaResult<GpuGKRProofJob<'static>> {
        let BasicUnrolledTransfers {
            mut setup_transfer,
            mut decoder_transfer,
            mut tracing_data_transfer,
            mut memory_transfer,
        } = self.create_transfers()?;

        let h2d_stream = self.context.get_h2d_stream();
        let transfer_range = Range::new("gkr.proof.h2d_transfers")?;
        transfer_range.start(h2d_stream)?;
        setup_transfer.schedule_transfer(&self.context)?;
        if let Some(decoder_transfer) = decoder_transfer.as_mut() {
            decoder_transfer.schedule_transfer(&self.context)?;
        }
        tracing_data_transfer.schedule_transfer(&self.context)?;
        memory_transfer.schedule_transfer(&self.context)?;
        transfer_range.end(h2d_stream)?;

        let mut proof_job = prove::<Global>(
            self.circuit_type,
            self.compiled_circuit.clone(),
            self.external_challenges,
            &self.prover_config,
            self.final_trace_size_log_2,
            Some(setup_transfer),
            decoder_transfer,
            None,
            Some(tracing_data_transfer),
            memory_transfer,
            &self.context,
        )?;
        proof_job.ranges.insert(0, transfer_range);
        Ok(proof_job)
    }
}

impl BasicUnrolledProofFixture {
    fn schedule_prove(&self) -> CudaResult<GpuGKRProofJob<'static>> {
        self.base.schedule_prove()
    }
}

struct BasicUnrolledFixtureBuildConfig<'a> {
    binary_path: &'a str,
    text_path: &'a str,
    layout_path: &'a str,
    non_determinism_reads: &'a [u32],
    compute_cpu_reference: bool,
    device_allocator_block_log_size: u32,
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
        let first_mismatch = describe_first_vec_mismatch(&gpu_column, cpu_column);
        assert!(
            first_mismatch.is_none(),
            "generic mapping column {generic_set_idx} diverged: {}",
            first_mismatch.unwrap()
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
        let first_mismatch = describe_first_vec_mismatch(&gpu_decoder, cpu_decoder);
        assert!(
            first_mismatch.is_none(),
            "decoder mapping diverged: {}",
            first_mismatch.unwrap()
        );
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
    _compiled_circuit: &GKRCircuitArtifact<BF>,
    context: &ProverContext,
) {
    assert_eq!(gpu_storage.layers.len(), cpu_storage.layers.len());
    for (layer_idx, (gpu_layer, cpu_layer)) in gpu_storage
        .layers
        .iter()
        .zip(cpu_storage.layers.iter())
        .enumerate()
    {
        let gpu_base_keys = gpu_layer
            .base_field_inputs
            .keys()
            .copied()
            .filter(|address| !matches!(address, GKRAddress::VirtualSetup(..)))
            .collect_vec();
        let cpu_base_keys = cpu_layer
            .base_field_inputs
            .keys()
            .copied()
            .filter(|address| !matches!(address, GKRAddress::VirtualSetup(..)))
            .collect_vec();
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

fn cached_address_layer(address: &GKRAddress) -> Option<usize> {
    match address {
        GKRAddress::Cached { layer, .. } => Some(*layer),
        _ => None,
    }
}

fn assert_cached_storage_entries_are_layer_local<E>(gpu_storage: &GpuGKRStorage<BF, E>) -> usize {
    let mut cached_entries = 0;
    for (layer_idx, layer) in gpu_storage.layers.iter().enumerate() {
        for address in layer
            .base_field_inputs
            .keys()
            .chain(layer.extension_field_inputs.keys())
        {
            if let Some(address_layer) = cached_address_layer(address) {
                cached_entries += 1;
                assert_eq!(
                    address_layer, layer_idx,
                    "cached helper storage escaped layer locality in layer {layer_idx}: {address:?}"
                );
            }
        }
    }

    cached_entries
}

fn assert_cached_kernel_addresses_are_layer_local(
    layer_idx: usize,
    inputs: &GKRInputs,
    label: &str,
) -> usize {
    let mut cached_addresses = 0;
    for address in inputs
        .inputs_in_base
        .iter()
        .chain(inputs.inputs_in_extension.iter())
        .chain(inputs.outputs_in_base.iter())
        .chain(inputs.outputs_in_extension.iter())
    {
        if let Some(address_layer) = cached_address_layer(address) {
            cached_addresses += 1;
            assert_eq!(
                address_layer, layer_idx,
                "{label} referenced cross-layer cached helper address {address:?}",
            );
        }
    }

    cached_addresses
}

mod fixtures_helpers;
pub(super) use fixtures_helpers::*;
