//! Proth120 wrap witness helpers.

#[cfg(test)]
use super::orchestration::common::ProgramConfig;
use super::orchestration::common::VmRunOutput;
use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use crate::gkr::witness_gen::family_circuits::{
    build_unified_table_driver_with_rom, evaluate_gkr_witness_for_executor_family,
    GKRFullWitnessTrace,
};
use crate::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use ::field::baby_bear::base::BabyBearField;
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use common_constants::rom::L1_WRAP_ROM;
use cs::gkr_circuits::{
    process_binary_into_separate_tables_ext, ExecutorFamilyDecoderData, OpcodeFamilyDecoder,
    UnifiedReducedMachineDecoder,
};
use cs::tables::TableDriver;
use field::PrimeField;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{Counters, ReplayBuffer};
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::UnifiedDestinationHolder;
use std::alloc::Global;
use worker::Worker;

/// `circuit_tester`: some hand crafted program for testing, uses no oracles and no
/// delegations (reduced-machine ASM), so nothing exercises a precompile CSR.
#[cfg(test)]
pub(super) fn circuit_tester_config() -> ProgramConfig {
    ProgramConfig {
        binary_path: "../examples/circuit_tester/app.bin".to_string(),
        text_section_path: "../examples/circuit_tester/app.text".to_string(),
        // no non-determinism oracle reads
        non_determinism_reads: vec![],
        cycles_bound: 1 << 20,
        ram_bound_bytes: 1 << 30,
    }
}

/// Inlined analogue of `orchestration::unified::build_unified_full_trace`, but with
/// the delegation CSRs removed from the preprocessing supported-CSR set (precompiles
/// disabled at preprocessing) and without the optional memory-consistency cross-check.
pub fn build_unified_trace_without_precompiles<C, F: PrimeField>(
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
