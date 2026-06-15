use super::orchestration::common::{
    hardcoded_external_challenges, run_vm_and_capture, ProgramConfig,
};
use super::orchestration::per_family::{build_nonmem_family_full_trace, prove_built_family_trace};
use super::*;
use crate::definitions::SecurityLevel;
use crate::gkr::prover::GKRProof;
use crate::merkle_trees::DefaultTreeConstructor;
use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use cs::gkr_circuits::opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization;
use cs::gkr_circuits::process_binary_into_separate_tables_ext;
use cs::tables::TableDriver;
use field::Field;
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::vm::{Counters, DelegationsAndFamiliesCounters};
use std::alloc::Global;
use worker::Worker;

const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;

// jump_branch_slt multiplicity column indices (from compiled circuit witness_layout)
const MULTIPLICITY_COL_RANGE_CHECK_16: usize = 25;
const MULTIPLICITY_COL_TIMESTAMP: usize = 26;
const MULTIPLICITY_COL_GENERIC: usize = 27;

/// Generate a jump_branch_slt proof with a witness mutation applied before proving.
fn generate_proof(
    mutate: impl FnOnce(&mut GKRFullWitnessTrace<BabyBearField, Global, Global>),
) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
    type CountersT = DelegationsAndFamiliesCounters;
    const CIRCUIT_TYPE: u8 = JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    let config = ProgramConfig::keccak_f1600();
    let vm = run_vm_and_capture::<CountersT>(&config, &worker);

    let preprocessing_data = process_binary_into_separate_tables_ext::<
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
        ],
    );
    let decoder_table_data = &preprocessing_data[&CIRCUIT_TYPE];

    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        &super::orchestration::per_family::circuit_path("jump_branch_slt"),
    );

    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::jump_branch_slt_family::jump_branch_slt_table_driver_fn(&mut table_driver);

    let num_calls = vm.counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
    assert!(
        num_calls > 0,
        "no jump_branch_slt instructions found in trace"
    );

    let mut full_trace = build_nonmem_family_full_trace::<CIRCUIT_TYPE, _>(
        &vm.snapshotter,
        &vm.tape,
        &vm.expected_final_state(),
        vm.cycles_bound,
        num_calls,
        &circuit,
        &table_driver,
        decoder_table_data,
        jump_branch_slt::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        false,
        &worker,
    );

    println!("Applying witness mutation");
    mutate(&mut full_trace);

    println!("Proving with corrupted witness");
    prove_built_family_trace(
        &circuit,
        &table_driver,
        decoder_table_data,
        full_trace,
        trace_len,
        &hardcoded_external_challenges(),
        SecurityLevel::Sec80,
        &worker,
    )
}

#[test]
#[ignore]
fn generate_malicious_proofs() {
    let proof = generate_proof(|trace| {
        let col = MULTIPLICITY_COL_RANGE_CHECK_16;
        let before = trace.column_major_witness_trace[col][0];
        trace.column_major_witness_trace[col][0].add_assign(&BabyBearField::ONE);
        let after = trace.column_major_witness_trace[col][0];
        println!(
            "range_check_16 multiplicity col={} row=0: {:?} -> {:?}",
            col, before, after
        );
    });
    serialize_to_file(&proof, "test_proofs/malicious_lookup_16bits_gkr_proof.json");

    let proof = generate_proof(|trace| {
        let col = MULTIPLICITY_COL_TIMESTAMP;
        let before = trace.column_major_witness_trace[col][0];
        trace.column_major_witness_trace[col][0].add_assign(&BabyBearField::ONE);
        let after = trace.column_major_witness_trace[col][0];
        println!(
            "timestamp multiplicity col={} row=0: {:?} -> {:?}",
            col, before, after
        );
    });
    serialize_to_file(
        &proof,
        "test_proofs/malicious_lookup_timestamps_gkr_proof.json",
    );

    // Generic lookup via multiplicity corruption
    let proof = generate_proof(|trace| {
        let col = MULTIPLICITY_COL_GENERIC;
        let before = trace.column_major_witness_trace[col][0];
        trace.column_major_witness_trace[col][0].add_assign(&BabyBearField::ONE);
        let after = trace.column_major_witness_trace[col][0];
        println!(
            "generic multiplicity col={} row=0: {:?} -> {:?}",
            col, before, after
        );
    });
    serialize_to_file(
        &proof,
        "test_proofs/malicious_lookup_generic_gkr_proof.json",
    );

    // --- Constraint / permutation violations ---

    let proof = generate_proof(|trace| {
        trace.column_major_witness_trace[0][0].add_assign(&BabyBearField::ONE);
    });
    serialize_to_file(&proof, "test_proofs/malicious_witness_value_gkr_proof.json");

    let proof = generate_proof(|trace| {
        trace.column_major_memory_trace[0][0].add_assign(&BabyBearField::ONE);
    });
    serialize_to_file(&proof, "test_proofs/malicious_memory_value_gkr_proof.json");
}
