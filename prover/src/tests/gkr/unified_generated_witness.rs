//! The SSA-generated unified witness functions satisfy the committed layouts on real
//! traces: regular 2^23 over the multi-family smoke program and Proth120 2^21
//! over `circuit_tester` (no delegations).

use super::orchestration::common::{
    run_vm_and_capture, run_vm_and_capture_with_rom, ProgramConfig, VmRunOutput,
};
use super::orchestration::unified::build_unified_full_trace;
use super::{
    base_trace_len, check_lookups_in_range, check_satisfied, deserialize_from_file,
    find_base_layer_address, first_decoder_lookup_violation, read_cell,
};
use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use crate::gkr::witness_gen::family_circuits::{
    build_unified_table_driver_with_rom, evaluate_gkr_witness_for_executor_family,
    GKRFullWitnessTrace,
};
use crate::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use ::field::baby_bear::base::BabyBearField;
use ::field::{PrimeField, Proth120};
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use common_constants::rom::L1_WRAP_ROM;
use cs::gkr_circuits::unified_reduced_machine::{
    FAMILY_2_FLAG_OFFSET, FAMILY_3_FLAG_OFFSET, FAMILY_4_LW_BIT, UNIFIED_REDUCED_MACHINE_NUM_FLAGS,
};
use cs::gkr_circuits::{
    process_binary_into_separate_tables_ext, ExecutorFamilyDecoderData, OpcodeFamilyDecoder,
    UnifiedReducedMachineDecoder,
};
use cs::tables::TableDriver;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{Counters, DelegationsAndUnifiedCounters, ReplayBuffer};
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::UnifiedDestinationHolder;
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

/// `circuit_tester`: some hand crafted program for testing, uses no oracles and no
/// delegations (reduced-machine ASM), so nothing exercises a precompile CSR.
fn circuit_tester_config() -> ProgramConfig {
    ProgramConfig {
        program: riscv_transpiler::elf::ProgramSource::legacy_binaries(
            "../examples/circuit_tester/app.bin",
            "../examples/circuit_tester/app.text",
        ),
        // no non-determinism oracle reads
        non_determinism_reads: vec![],
        cycles_bound: 1 << 20,
        ram_bound_bytes: 1 << 30,
    }
}

/// Inlined analogue of `orchestration::unified::build_unified_full_trace`, but with
/// the delegation CSRs removed from the preprocessing supported-CSR set (precompiles
/// disabled at preprocessing) and without the optional memory-consistency cross-check.
fn build_unified_trace_without_precompiles<C, F: PrimeField>(
    vm: &VmRunOutput<C, { L1_WRAP_ROM.second_word_bits() }>,
    witness_eval_fn_ptr: fn(&mut ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, F>),
    unified_circuit: &GKRCircuitArtifact<F>,
    num_teardown_sets: usize,
    cycles_per_chunks: usize,
    worker: &Worker,
) -> (
    GKRFullWitnessTrace<F, Global, Global>,
    TableDriver<F>,
    Vec<Option<ExecutorFamilyDecoderData>>,
    Vec<u32>,
)
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let num_calls = vm
        .counters
        .get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    println!("Replaying {} cycles for witness data", num_calls);
    // Replay the captured trace into the unified destination holder.
    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ L1_WRAP_ROM.second_word_bits() }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = [&mut buffer[..]];
    let mut tracer = UnifiedDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut replay_ram,
        &vm.tape,
        &mut (),
        vm.cycles_bound,
        &mut tracer,
    );
    assert_eq!(vm.expected_final_state(), state);

    // Preprocessing WITHOUT any delegation CSRs => no precompiles.
    println!("Creating decoder table");
    let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> = vec![Box::new(UnifiedReducedMachineDecoder)];
    const SUPPORTED_CSRS: &[u16] = &[common_constants::NON_DETERMINISM_CSR as u16];
    let mut preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        ReducedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &decoders,
        L1_WRAP_ROM.word_size(),
        SUPPORTED_CSRS,
    );
    let decoder_table = preprocessing_data
        .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .expect("UnifiedReducedMachineDecoder must produce a family-128 entry");

    let oracle = UnifiedRiscvCircuitOracle {
        inner: &buffer,
        decoder_table: &decoder_table,
    };
    let unified_table_driver =
        build_unified_table_driver_with_rom::<F, { L1_WRAP_ROM.second_word_bits() }>(&vm.binary);

    println!("Collecting inits and teardowns");

    // we should collect carefully here, as regions will not be continuous
    let max_ram_touch = vm
        .shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.iter().map(|el| el.0).max().unwrap_or(0))
        .max()
        .expect("max address touched");
    assert_eq!(max_ram_touch % 4, 0);
    let mut inits_and_teardowns = vm.ram.collect_inits_and_teardowns_sets::<F, Global>(
        worker,
        cycles_per_chunks.trailing_zeros() as usize,
        num_teardown_sets,
        Some(((max_ram_touch as usize) + 4) / 4),
    );
    assert_eq!(inits_and_teardowns.len(), 1);
    let (top_bits, inits_and_teardowns_chunks) = inits_and_teardowns
        .drain(..1)
        .next()
        .expect("inits and teardowns");
    assert_eq!(top_bits.len(), num_teardown_sets);

    println!("Calculating full witness trace");

    let full_trace = evaluate_gkr_witness_for_executor_family::<F, _, _, _>(
        unified_circuit,
        witness_eval_fn_ptr,
        cycles_per_chunks,
        &oracle,
        &unified_table_driver,
        worker,
        Some(inits_and_teardowns_chunks),
        Global,
        Global,
    );

    (full_trace, unified_table_driver, decoder_table, top_bits)
}
