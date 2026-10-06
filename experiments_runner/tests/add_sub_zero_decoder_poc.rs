#![feature(allocator_api)]
#![feature(generic_const_exprs)]

//! Reproduce the decoder-zero-row flaw on the unfixed add/sub circuit.
//! Run with `cargo test -p experiments_runner --test add_sub_zero_decoder_poc add_sub_zero_decoder_poc -- --ignored --nocapture`.

use ::field::baby_bear::base::BabyBearField;
use common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
use cs::definitions::{
    BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, BLAKE2S_DELEGATION_CSR_REGISTER,
    BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER, NON_DETERMINISM_CSR,
};
use cs::gkr_circuits::{
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    process_binary_into_separate_tables_ext,
};
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::tables::TableDriver;
use field::Field;
use prover::definitions::SecurityLevel;
use prover::gkr::witness_gen::family_circuits::evaluate_gkr_witness_for_executor_family;
use prover::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
use prover::tests::gkr::check_satisfied_row;
use prover::tests::gkr::orchestration::common::{
    hardcoded_external_challenges, run_vm_and_capture, ProgramConfig,
};
use prover::tests::gkr::orchestration::delegations::{deserialize_from_file, serialize_to_file};
use prover::tests::gkr::orchestration::per_family::{circuit_path, prove_built_family_trace};
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{Counters, DelegationsAndFamiliesCounters, ReplayBuffer};
use riscv_transpiler::witness::{NonMemDestinationHolder, NonMemoryOpcodeTracingDataWithTimestamp};
use std::alloc::Global;
use worker::Worker;

#[test]
#[ignore = "expensive 2^24-row security PoC"]
fn add_sub_zero_decoder_poc() {
    type CountersT = DelegationsAndFamiliesCounters;
    const FAMILY: u8 = ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
    const FORGED_X0: u32 = 8;

    let worker = Worker::new_with_num_threads(8);
    let vm = run_vm_and_capture::<CountersT, FullUnsignedMachineDecoderConfig>(
        &ProgramConfig {
            binary_path: "../examples/add_sub_zero_decoder_poc/app.bin".into(),
            text_section_path: "../examples/add_sub_zero_decoder_poc/app.text".into(),
            non_determinism_reads: vec![],
            cycles_bound: 1 << 16,
            ram_bound_bytes: 1 << 26,
        },
        &worker,
    );
    let preprocessing = process_binary_into_separate_tables_ext::<
        BabyBearField,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ],
    );
    let genuine_decoder = &preprocessing[&FAMILY];
    assert_eq!(
        genuine_decoder[0].unwrap().opcode_family_bits.count_ones(),
        1
    );
    let mut forged_decoder = genuine_decoder.clone();
    forged_decoder[0] = Some(Default::default());

    let circuit: GKRCircuitArtifact<BabyBearField> =
        deserialize_from_file(&circuit_path("add_sub_lui_auipc_mop"));
    assert!(!circuit.tables_ids_in_generic_lookups);
    assert_eq!(circuit.total_tables_size, 1 << 20);
    assert!(circuit.trace_len > circuit.total_tables_size);
    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::add_sub_family::add_sub_lui_auipc_mop_table_driver_fn(&mut table_driver);

    let num_calls = vm.counters.get_calls_to_circuit_family::<FAMILY>();
    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<FAMILY> {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        &vm.tape,
        &mut (),
        vm.cycles_bound,
        &mut tracer,
    );
    assert_eq!(state, vm.expected_final_state());
    assert_eq!(buffer[0].opcode_data.initial_pc, 0);
    assert_eq!(buffer[0].opcode_data.rd_old_value, 0);

    // The fake all-zero decoder tuple chooses x0 for every register port. The
    // active row still writes an arbitrary u32 into x0 at machine startup.
    buffer[0].opcode_data.rd_value = FORGED_X0;
    buffer[0].rd_read_timestamp =
        common_constants::TimestampData::from_scalar(buffer[0].cycle_timestamp.as_scalar() + 1);
    // The next authentic instruction is `addi ra, ra, 12`. It reads the
    // forged x0 value as rs2 and writes ra = V + 12. The following authentic
    // `jalr x0, ra, 0` would use that value as its branch target.
    assert_eq!(buffer[1].opcode_data.initial_pc, 4);
    assert_eq!(buffer[1].opcode_data.rd_value, 12);
    buffer[1].opcode_data.rs2_value = FORGED_X0;
    buffer[1].opcode_data.rd_value = FORGED_X0 + 12;
    buffer[1].rs1_read_timestamp = common_constants::TimestampData::from_scalar(0);
    buffer[1].rs2_read_timestamp =
        common_constants::TimestampData::from_scalar(buffer[0].cycle_timestamp.as_scalar() + 2);
    // The authentic JALR at PC 8 branches to PC 20 in the forged trace, so
    // the third add/sub row is the authenticated `addi a0, x0, 2` there.
    // Its timestamp and x0/a0 read history match the honest PC-12 ADDI row.
    assert_eq!(buffer[2].opcode_data.initial_pc, 12);
    assert_eq!(buffer[2].opcode_data.rd_value, 1);
    assert!(genuine_decoder[20 / 4].is_some());
    buffer[2].opcode_data.initial_pc = 20;
    buffer[2].opcode_data.new_pc = 24;
    buffer[2].opcode_data.rd_value = 2;
    let oracle = NonMemoryCircuitOracle {
        inner: &buffer,
        decoder_table: &forged_decoder,
        default_pc_value_in_padding: 4,
    };
    let mut trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
        &circuit,
        prover::tests::gkr::add_sub_lui_auipc_mop::witness_eval_fn,
        circuit.trace_len,
        &oracle,
        &table_driver,
        &worker,
        None,
        Global,
        Global,
    );
    assert_eq!(trace.generic_lookup_mapping[0][0], 0);
    trace.generic_lookup_mapping[0][0] = circuit.total_tables_size as u32;
    let multiplicity_col = circuit
        .witness_layout
        .multiplicities_columns_for_generic_lookup
        .start;
    let multiplicities = &mut trace.column_major_witness_trace[multiplicity_col];
    assert_ne!(multiplicities[0], BabyBearField::ZERO);
    multiplicities[0].sub_assign(&BabyBearField::ONE);
    multiplicities[circuit.total_tables_size].add_assign(&BabyBearField::ONE);
    assert!(check_satisfied_row(&circuit, &trace, 0));
    assert!(check_satisfied_row(&circuit, &trace, 1));
    assert!(check_satisfied_row(&circuit, &trace, 2));

    let proof = prove_built_family_trace(
        &circuit,
        &table_driver,
        genuine_decoder,
        trace,
        circuit.trace_len,
        &hardcoded_external_challenges(),
        SecurityLevel::Sec100,
        &worker,
    );
    std::fs::create_dir_all("../prover/test_proofs").unwrap();
    serialize_to_file(
        &proof,
        "../prover/test_proofs/add_sub_zero_decoder_poc_sec_100_gkr_proof.json",
    );
}
