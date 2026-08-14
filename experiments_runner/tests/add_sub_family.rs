//! Analog of the `add_sub_lui_auipc_mop` section of
//! `prover::tests::gkr::family_circuits::gkr_run_basic_unrolled_test_impl`:
//! run the default keccak-f1600 program, preprocess the binary, and prove
//! ONLY the add/sub family circuit at Sec80. Kept byte-compatible with the
//! per-family test by reusing the exact same orchestration helpers
//! (`run_vm_and_capture` + `prove_non_mem_family`); the proof lands in
//! `experiments_runner/test_proofs/add_sub_lui_auipc_mop_sec_80_gkr_proof.json`.

// Same nightly features the prover crate builds with: its orchestration API
// surfaces `Global` and a const-generic snapshotter parameter.
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]

use common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
use cs::definitions::{
    BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, BLAKE2S_DELEGATION_CSR_REGISTER,
    BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER,
    NON_DETERMINISM_CSR,
};
use cs::gkr_circuits::opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization;
use cs::gkr_circuits::process_binary_into_separate_tables_ext;
use field::baby_bear::base::BabyBearField;
use prover::definitions::SecurityLevel;
use prover::tests::gkr::add_sub_lui_auipc_mop;
use prover::tests::gkr::orchestration::common::{
    hardcoded_external_challenges, run_vm_and_capture, ProgramConfig,
};
use prover::tests::gkr::orchestration::per_family::prove_non_mem_family;
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::vm::{Counters, DelegationsAndFamiliesCounters};
use std::alloc::Global;
use worker::Worker;

// Must match the constants the per-family test (and the compiled circuit
// layouts) were produced with.
const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
const PROVE_EMPTY: bool = true;

#[test]
fn gkr_prove_add_sub_family_sec_80() {
    let level = SecurityLevel::Sec80;
    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    let config = ProgramConfig::keccak_f1600();
    let vm = run_vm_and_capture::<DelegationsAndFamiliesCounters, FullUnsignedMachineDecoderConfig>(
        &config, &worker,
    );

    println!("Finished at PC = 0x{:08x}", vm.final_pc());

    let expected_final_state = vm.expected_final_state();
    let counters = vm.counters;
    let cycles_bound = vm.cycles_bound;
    let snapshotter = vm.snapshotter;
    let tape = vm.tape;
    let text_section = vm.text_section;

    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
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
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ],
    );

    let external_challenges = hardcoded_external_challenges();

    const CIRCUIT_TYPE: u8 = ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
    let num_calls = counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
    assert!(num_calls < NUM_CYCLES_PER_CHUNK);

    std::fs::create_dir_all("test_proofs").unwrap();

    let out = prove_non_mem_family::<CIRCUIT_TYPE, DelegationsAndFamiliesCounters>(
        &snapshotter,
        &tape,
        &expected_final_state,
        cycles_bound,
        num_calls,
        &preprocessing_data[&CIRCUIT_TYPE],
        cs::gkr_circuits::add_sub_family::add_sub_lui_auipc_mop_table_driver_fn::<BabyBearField>,
        trace_len,
        NUM_CYCLES_PER_CHUNK,
        &external_challenges,
        level,
        PROVE_EMPTY,
        false,
        &None,
        "add_sub_lui_auipc_mop",
        level.dir_suffix(),
        &worker,
        add_sub_lui_auipc_mop::witness_eval_fn,
    );

    let proof = out.proof.expect("add/sub family proof must be produced");
    println!(
        "grand product accumulator = {:?}",
        proof.grand_product_accumulator_computed
    );
}
