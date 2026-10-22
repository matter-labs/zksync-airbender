//! The SSA-generated unified witness functions satisfy the committed layouts on real
//! traces: regular 2^23 over the multi-family smoke program and Proth120 2^21
//! over `circuit_tester` (no delegations).

use super::large_field::{build_unified_trace_without_precompiles, circuit_tester_config};
use super::orchestration::common::{
    run_vm_and_capture, run_vm_and_capture_with_rom, ProgramConfig,
};
use super::orchestration::unified::build_unified_full_trace;
use super::{
    base_trace_len, check_lookups_in_range, check_satisfied, deserialize_from_file,
    find_base_layer_address, first_decoder_lookup_violation, read_cell,
};
use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use ::field::baby_bear::base::BabyBearField;
use ::field::{PrimeField, Proth120};
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use common_constants::rom::L1_WRAP_ROM;
use cs::gkr_circuits::unified_reduced_machine::{
    FAMILY_2_FLAG_OFFSET, FAMILY_3_FLAG_OFFSET, FAMILY_4_LW_BIT, UNIFIED_REDUCED_MACHINE_NUM_FLAGS,
};
use cs::gkr_circuits::ExecutorFamilyDecoderData;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::vm::{Counters, DelegationsAndUnifiedCounters};
use std::alloc::Global;
use worker::Worker;

/// Every checker accepts the trace, every family executes, and some non-F3 row holds a
/// register limb above a byte in the aliased slot 17.
fn assert_generated_witness_satisfies<F: PrimeField>(
    label: &str,
    circuit: &GKRCircuitArtifact<F>,
    trace: &GKRFullWitnessTrace<F, Global, Global>,
    decoder_table: &[Option<ExecutorFamilyDecoderData>],
) {
    assert!(check_satisfied(circuit, trace), "{label}: arithmetic");
    assert!(check_lookups_in_range(circuit, trace), "{label}: ranges");
    assert_eq!(
        first_decoder_lookup_violation(circuit, trace, decoder_table),
        None,
        "{label}: decoder membership"
    );

    let execute = find_base_layer_address(circuit, "Execute flag for cycle");
    let bits: Vec<_> = (0..UNIFIED_REDUCED_MACHINE_NUM_FLAGS)
        .map(|i| find_base_layer_address(circuit, &format!("family_bit[{i}]")))
        .collect();
    let register_low = find_base_layer_address(circuit, "shared scratch var[17]");
    let family_of = |bit: usize| match bit {
        b if b < FAMILY_2_FLAG_OFFSET => 0,
        b if b < FAMILY_3_FLAG_OFFSET => 1,
        b if b < FAMILY_4_LW_BIT => 2,
        _ => 3,
    };
    let mut rows_per_family = [0usize; 4];
    let mut wide_non_f3_register_rows = 0usize;
    for row in 0..base_trace_len(trace) {
        if read_cell(trace, execute, row) != F::ONE {
            continue;
        }
        let family = (0..bits.len())
            .find(|&i| read_cell(trace, bits[i], row) == F::ONE)
            .map(family_of)
            .unwrap_or_else(|| panic!("{label}: executing row {row} without a dispatch bit"));
        rows_per_family[family] += 1;
        if family != 2 && read_cell(trace, register_low, row).as_u32_reduced() > 0xFF {
            wide_non_f3_register_rows += 1;
        }
    }
    println!(
        "{label}: rows per family {rows_per_family:?}, non-F3 rows with slot 17 > 0xFF: \
         {wide_non_f3_register_rows}"
    );
    assert!(
        rows_per_family.iter().all(|&n| n > 0),
        "{label}: family coverage {rows_per_family:?}"
    );
    assert!(
        wide_non_f3_register_rows > 0,
        "{label}: no non-F3 row holds a register limb above 0xFF in slot 17"
    );
}

fn regular_witness_satisfies(label: &str, layout: &str) {
    let worker = Worker::new_with_num_threads(8);
    let vm = run_vm_and_capture::<DelegationsAndUnifiedCounters, ReducedMachineDecoderConfig>(
        &ProgramConfig::multi_family_smoke_blake_compression(),
        &worker,
    );
    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(layout);
    let num_calls = vm
        .counters
        .get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    assert!(num_calls < circuit.trace_len);
    let (trace, _table_driver, decoder_table, _top_bits) = build_unified_full_trace(
        &vm,
        &circuit,
        num_calls,
        super::unified_reduced_machine::witness_eval_fn,
        false,
        &worker,
    );
    assert_generated_witness_satisfies(label, &circuit, &trace, &decoder_table);
}

#[test]
fn generated_witness_satisfies_regular_layout() {
    regular_witness_satisfies(
        "regular 2^23 smoke",
        "../cs/compiled_circuits/unified_reduced_machine_layout_gkr.json",
    );
}

#[test]
fn generated_witness_satisfies_proth120_wrap_layout() {
    let worker = Worker::new_with_num_threads(8);
    let vm = run_vm_and_capture_with_rom::<
        DelegationsAndUnifiedCounters,
        ReducedMachineDecoderConfig,
        { L1_WRAP_ROM.second_word_bits() },
    >(&circuit_tester_config(), &worker);
    let circuit: GKRCircuitArtifact<Proth120> = deserialize_from_file(
        "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json",
    );
    let num_teardown_sets = circuit.memory_layout.teardown_sets.len();
    let (trace, _table_driver, decoder_table, _top_bits) = build_unified_trace_without_precompiles(
        &vm,
        super::unified_reduced_machine_proth120::witness_eval_fn,
        &circuit,
        num_teardown_sets,
        circuit.trace_len,
        &worker,
    );
    assert_generated_witness_satisfies(
        "proth120 2^21 circuit_tester",
        &circuit,
        &trace,
        &decoder_table,
    );
}
