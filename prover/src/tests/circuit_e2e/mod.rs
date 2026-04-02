//! End-to-end circuit constraint satisfaction tests for individual RISC-V opcodes.
//!
//! Each test encodes a single RISC-V instruction, provides register inputs/outputs
//! as oracle data, runs the full circuit (witness generation + constraint check),
//! and optionally runs the full prover + verifier pipeline.
//!
//! These tests require the `debug_evaluate_witness` feature (enabled by the prover's
//! `cs_debug` feature) so that `BasicAssembly::is_satisfied()` actually evaluates
//! constraints against the resolved witness.

use crate::cs::cs::cs_reference::BasicAssembly;
use crate::definitions::*;
use crate::merkle_trees::DefaultTreeConstructor;
use crate::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits;
use crate::prover_stages::SetupPrecomputations;
use crate::unrolled::{MemoryCircuitOracle, NonMemoryCircuitOracle};
use crate::unrolled::evaluate_witness_for_executor_family;
use crate::witness_evaluator::{check_satisfied, SimpleWitnessProxy};
use cs::cs::circuit::Circuit;
use cs::cs::oracle::ExecutorFamilyDecoderData;
use cs::definitions::TimestampData;
use cs::machine::ops::unrolled::decoder::{
    materialize_flattened_decoder_table, process_binary_into_separate_tables_ext,
};
use cs::one_row_compiler::CompiledCircuitArtifact;
use cs::tables::TableDriver;
use crate::DEFAULT_TRACE_PADDING_MULTIPLE;
use cs::one_row_compiler::NUM_MEM_ARGUMENT_KEY_PARTS;
use ::field::*;
use fft::*;
use riscv_transpiler::machine_mode_only_unrolled::*;
use std::alloc::Global;
use worker::Worker;

#[cfg(test)]
use test_utils::skip_if_ci;

pub struct NonMemTestCase {
    pub label: &'static str,
    pub rs1: u32,
    pub rs2: u32,
    pub rd: u32,
}

/// Run a single opcode through the circuit and check constraint satisfaction only.
pub fn run_non_mem_circuit_test(
    decoder_data: &[ExecutorFamilyDecoderData],
    table_fn: fn(&mut BasicAssembly<Mersenne31Field>),
    circuit_fn: fn(&mut BasicAssembly<Mersenne31Field>),
    case: &NonMemTestCase,
) {
    let trace_data = make_trace_data(case);

    let oracle = NonMemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: decoder_data,
        default_pc_value_in_padding: 4,
    };

    let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        decoder_data.to_vec(),
    );

    table_fn(&mut cs);
    circuit_fn(&mut cs);

    assert!(
        cs.is_satisfied(),
        "Constraints NOT satisfied for: {}",
        case.label
    );
}

/// Full prove pipeline: compile circuit, generate witness, check constraints,
/// run prover to generate a ZK proof.
pub fn run_non_mem_prove_test(
    encoding: u32,
    decoder: Box<dyn cs::machine::ops::unrolled::decoder::OpcodeFamilyDecoder>,
    family_idx: u8,
    table_fn: fn(&mut BasicAssembly<Mersenne31Field>),
    table_driver_fn: fn(&mut TableDriver<Mersenne31Field>),
    compile_circuit_fn: &dyn Fn(usize) -> CompiledCircuitArtifact<Mersenne31Field>,
    witness_eval_fn: fn(&mut SimpleWitnessProxy<'_, NonMemoryCircuitOracle<'_>>),
    case: &NonMemTestCase,
    supported_csrs: &[u16],
) {
    const TRACE_LEN_LOG2: usize = 24;
    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let num_cycles = trace_len - 1;
    let lde_factor = 2;
    let tree_cap_size = 32;

    let worker = Worker::new_with_num_threads(4);

    // 1. Compile circuit
    let compiled_circuit = compile_circuit_fn(TRACE_LEN_LOG2);

    // 2. Prepare decoder tables
    let bytecode = vec![encoding];
    let bytecode_size = 1 << 20;
    let mut t = process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        &bytecode,
        &[decoder],
        bytecode_size,
        supported_csrs,
    );
    let (decoder_table_entries, decoder_data) = t.remove(&family_idx).expect("decoder data");
    let flattened_decoder_table = materialize_flattened_decoder_table(&decoder_table_entries);

    // 3. Create oracle
    let trace_data = make_trace_data(case);
    let oracle = NonMemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: &decoder_data,
        default_pc_value_in_padding: 4,
    };

    // 4. Create table driver
    let mut table_driver = TableDriver::<Mersenne31Field>::new();
    table_driver_fn(&mut table_driver);

    // 5. Generate witness
    let full_trace = evaluate_witness_for_executor_family::<_, Global>(
        &compiled_circuit,
        witness_eval_fn,
        num_cycles,
        &oracle,
        &table_driver,
        &worker,
        Global,
    );

    // 6. Check constraints on witness
    let is_satisfied = check_satisfied(
        &compiled_circuit,
        &full_trace.exec_trace,
        full_trace.num_witness_columns,
    );
    assert!(
        is_satisfied,
        "Witness constraints NOT satisfied for: {}",
        case.label
    );

    // 7. Setup precomputations
    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    let lde_precomputations =
        LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
    let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
        &table_driver,
        &flattened_decoder_table,
        trace_len,
        &compiled_circuit.setup_layout,
        &twiddles,
        &lde_precomputations,
        lde_factor,
        tree_cap_size,
        &worker,
    );

    // 8. External challenges (deterministic for testing)
    let memory_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(2),
        Mersenne31Field(5),
        Mersenne31Field(42),
        Mersenne31Field(123),
    ]);
    let memory_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(11),
        Mersenne31Field(7),
        Mersenne31Field(1024),
        Mersenne31Field(8000),
    ]);
    let memory_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let state_permutation_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(41),
        Mersenne31Field(42),
        Mersenne31Field(43),
        Mersenne31Field(44),
    ]);
    let state_permutation_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(80),
        Mersenne31Field(90),
        Mersenne31Field(100),
        Mersenne31Field(110),
    ]);
    use cs::definitions::NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES;
    let state_linearization_challenges: [Mersenne31Quartic;
        NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            state_permutation_argument_alpha,
            NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES,
        )
        .try_into()
        .unwrap();

    let external_challenges = ExternalChallenges {
        memory_argument: ExternalMemoryArgumentChallenges {
            memory_argument_linearization_challenges,
            memory_argument_gamma,
        },
        delegation_argument: None,
        machine_state_permutation_argument: Some(ExternalMachineStateArgumentChallenges {
            linearization_challenges: state_linearization_challenges,
            additive_term: state_permutation_argument_gamma,
        }),
    };

    let security_config =
        crate::prover_stages::ProofSecurityConfig::for_queries_only(5, 28, 63);

    // 9. Generate proof
    println!("Proving: {}", case.label);
    let now = std::time::Instant::now();
    let (_prover_data, proof) = prove_configured_for_unrolled_circuits::<
        { DEFAULT_TRACE_PADDING_MULTIPLE },
        _,
        DefaultTreeConstructor,
    >(
        &compiled_circuit,
        &vec![],
        &external_challenges,
        full_trace,
        &[],
        &setup,
        &twiddles,
        &lde_precomputations,
        None,
        lde_factor,
        tree_cap_size,
        &security_config,
        &worker,
    );
    println!("Proof generated for '{}' in {:?}", case.label, now.elapsed());

    // Basic proof sanity checks
    assert!(
        proof.delegation_argument_accumulator.is_none(),
        "Unexpected delegation accumulator"
    );
}

fn make_trace_data(case: &NonMemTestCase) -> Vec<NonMemoryOpcodeTracingDataWithTimestamp> {
    vec![NonMemoryOpcodeTracingDataWithTimestamp {
        opcode_data: NonMemoryOpcodeTracingData {
            initial_pc: 0,
            rs1_value: case.rs1,
            rs2_value: case.rs2,
            rd_old_value: 0,
            rd_value: case.rd,
            new_pc: 4,
            delegation_type: 0,
        },
        rs1_read_timestamp: TimestampData::from_scalar(0),
        rs2_read_timestamp: TimestampData::from_scalar(0),
        rd_read_timestamp: TimestampData::from_scalar(0),
        cycle_timestamp: TimestampData::from_scalar(4),
    }]
}

/// Prepare decoder data for a single instruction encoding within a given family.
pub fn prepare_decoder_data(
    encoding: u32,
    decoder: Box<dyn cs::machine::ops::unrolled::decoder::OpcodeFamilyDecoder>,
    family_idx: u8,
    supported_csrs: &[u16],
) -> Vec<ExecutorFamilyDecoderData> {
    let bytecode = vec![encoding];
    let bytecode_size = 1 << 10;
    let mut t = process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        &bytecode,
        &[decoder],
        bytecode_size,
        supported_csrs,
    );
    let (_, decoder_data) = t.remove(&family_idx).expect("decoder data");
    decoder_data
}

/// Variant for circuits where padding rows need pc=0 (e.g. jump/branch/SLT).
pub fn run_non_mem_circuit_test_with_pc_padding(
    decoder_data: &[ExecutorFamilyDecoderData],
    table_fn: fn(&mut BasicAssembly<Mersenne31Field>),
    circuit_fn: fn(&mut BasicAssembly<Mersenne31Field>),
    case: &NonMemTestCase,
    default_pc_value_in_padding: u32,
) {
    let trace_data = make_trace_data(case);

    let oracle = NonMemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: decoder_data,
        default_pc_value_in_padding,
    };

    let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        decoder_data.to_vec(),
    );

    table_fn(&mut cs);
    circuit_fn(&mut cs);

    assert!(
        cs.is_satisfied(),
        "Constraints NOT satisfied for: {}",
        case.label
    );
}

/// Test case for memory (load/store) circuits.
pub struct MemTestCase {
    pub label: &'static str,
    pub data: MemoryOpcodeTracingDataWithTimestamp,
}

/// Run a memory circuit test (load/store families).
pub fn run_mem_circuit_test(
    decoder_data: &[ExecutorFamilyDecoderData],
    table_fn: fn(&mut BasicAssembly<Mersenne31Field>),
    circuit_fn: fn(&mut BasicAssembly<Mersenne31Field>),
    case: &MemTestCase,
) {
    let trace_data = vec![case.data];

    let oracle = MemoryCircuitOracle {
        inner: &trace_data,
        decoder_table: decoder_data,
    };

    let oracle: MemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
    let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
        oracle,
        decoder_data.to_vec(),
    );

    table_fn(&mut cs);
    circuit_fn(&mut cs);

    assert!(
        cs.is_satisfied(),
        "Constraints NOT satisfied for: {}",
        case.label
    );
}

#[cfg(test)]
mod mul_div;
#[cfg(test)]
mod add_sub;
#[cfg(test)]
mod shift_binop;

// mod jump_branch;
#[cfg(test)]
mod load_store;
#[cfg(test)]
mod e2e_prove_verify;
