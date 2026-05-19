use super::*;
use crate::gkr::witness_gen::family_circuits::{
    build_unified_table_driver, evaluate_gkr_witness_for_executor_family,
};
use crate::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use ::field::baby_bear::base::BabyBearField;
use ::field::Field;
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use cs::gkr_circuits::unified_reduced_machine::{FAMILY_4_LW_BIT, FAMILY_4_SW_BIT};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::replayer::*;
use riscv_transpiler::vm::*;
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::UnifiedDestinationHolder;
use std::alloc::Global;
use worker::Worker;

const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
const WORD_BITS: u32 = core::mem::size_of::<u32>().trailing_zeros();

const USE_GKR_WITH_CACHES: bool = cfg!(not(feature = "no_caches"));

fn find_base_layer_address(
    circuit: &GKRCircuitArtifact<BabyBearField>,
    name: &str,
) -> GKRAddress {
    for (var, var_name) in circuit.variable_names.iter() {
        if var_name == name {
            let addr = *circuit
                .placement_data
                .get(var)
                .expect("variable_names entry missing from placement_data");
            return match addr {
                GKRAddress::BaseLayerWitness(_) | GKRAddress::BaseLayerMemory(_) => addr,
                other => panic!("variable '{name}' not in the base layer: {other:?}"),
            };
        }
    }
    panic!("no variable named '{name}' in unified circuit artifact");
}

fn read_cell(
    trace: &GKRFullWitnessTrace<BabyBearField, Global, Global>,
    addr: GKRAddress,
    row: usize,
) -> BabyBearField {
    match addr {
        GKRAddress::BaseLayerWitness(col) => trace.column_major_witness_trace[col][row],
        GKRAddress::BaseLayerMemory(col) => trace.column_major_memory_trace[col][row],
        other => panic!("not a base-layer address: {other:?}"),
    }
}

fn write_cell(
    trace: &mut GKRFullWitnessTrace<BabyBearField, Global, Global>,
    addr: GKRAddress,
    row: usize,
    value: BabyBearField,
) {
    match addr {
        GKRAddress::BaseLayerWitness(col) => trace.column_major_witness_trace[col][row] = value,
        GKRAddress::BaseLayerMemory(col) => trace.column_major_memory_trace[col][row] = value,
        other => panic!("not a base-layer address: {other:?}"),
    }
}

fn base_trace_len(trace: &GKRFullWitnessTrace<BabyBearField, Global, Global>) -> usize {
    trace.column_major_witness_trace[0].len()
}

fn build_satisfying_trace_with_mutation(
    mutate: impl FnOnce(
        &GKRCircuitArtifact<BabyBearField>,
        &mut GKRFullWitnessTrace<BabyBearField, Global, Global>,
    ),
) -> (
    GKRCircuitArtifact<BabyBearField>,
    GKRFullWitnessTrace<BabyBearField, Global, Global>,
) {
    type CountersT = DelegationsAndUnifiedCounters;

    let worker = Worker::new_with_num_threads(8);

    let circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
        deserialize_from_file("../cs/compiled_circuits/unified_reduced_machine_layout_gkr.json")
    } else {
        deserialize_from_file(
            "../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json",
        )
    };
    let num_teardown_sets = circuit.memory_layout.teardown_sets.len();
    let ram_bound_bytes: usize = (num_teardown_sets << TRACE_LEN_LOG2) << (WORD_BITS as usize);

    let binary = std::fs::read("../examples/multi_family_smoke/app.bin").unwrap();
    let text_section = std::fs::read("../examples/multi_family_smoke/app.text").unwrap();
    assert!(binary.len() % 4 == 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    assert!(text_section.len() % 4 == 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ common_constants::ROM_SECOND_WORD_BITS }>::from_rom_content(
        &binary,
        ram_bound_bytes,
    );
    let cycles_bound = 1 << 20;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter = SimpleSnapshotter::<
        CountersT,
        { common_constants::ROM_SECOND_WORD_BITS },
    >::new_with_cycle_limit(cycles_bound, state);
    let mut non_determinism = QuasiUARTSource::new_with_reads(vec![0x9u32, 0xDEAD_BEEFu32]);

    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<_, _, _, BabyBearField>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_program_finished);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;
    let num_calls = counters.get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    assert!(num_calls < NUM_CYCLES_PER_CHUNK);

    let _shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(&worker, Global);

    let mut inits_and_teardowns = Vec::with_capacity(num_teardown_sets);
    for _ in 0..num_teardown_sets {
        let a = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let b = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let c = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let d = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        inits_and_teardowns.push(([a, b], [c, d]));
    }
    ram.collect_inits_and_teardowns_into_columns::<BabyBearField, _>(
        &worker,
        TRACE_LEN_LOG2,
        0,
        &mut inits_and_teardowns,
    );

    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

    let mut state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = UnifiedDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        &tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state, state);

    let oracle = UnifiedRiscvCircuitOracle::new::<BabyBearField>(
        &buffer[..],
        &text_section,
        common_constants::ROM_WORD_SIZE,
    );

    let table_driver = build_unified_table_driver::<BabyBearField>(&binary);

    let mut full_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
        &circuit,
        super::unified_reduced_machine::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &table_driver,
        &worker,
        Some(inits_and_teardowns),
        Global,
        Global,
    );

    mutate(&circuit, &mut full_trace);

    (circuit, full_trace)
}

/// Force a misaligned `writeaddr_lo` on an SW row.
/// The decomposition `4*top_14 + 2*bit_1 + bit_0 = writeaddr_lo` becomes
/// inconsistent (low bits unchanged, but `writeaddr_lo` no longer matches),
/// so `check_satisfied` rejects.
#[test]
fn misaligned_sw_writeaddr_lo_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let sw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_SW_BIT}]"));
        let writeaddr_lo_addr = find_base_layer_address(circuit, "unified memwrite_addr[0]");
        let sw_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, sw_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one SW");
        // `0xFFFD` is a 16-bit value with bit 0 = 1 → misaligned. The
        // decomposition constraint (degree 1, ungated) catches it because
        // we leave bit_0/bit_1/top_14 unchanged.
        write_cell(trace, writeaddr_lo_addr, sw_row, BabyBearField::new(0xFFFD));
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected misaligned SW writeaddr_lo mutation to fail check_satisfied"
    );
}

/// one-hot family dispatch. Set a second family bit on an LW row,
/// so two dispatch bits are hot on the same executing row. The setup
/// constraint `is_any_family_active - execute * Σ family-bits = 0` then
/// evaluates to `1 - 1*2 = -1 ≠ 0`, so `check_satisfied` rejects.
#[test]
fn two_family_bits_on_one_row_rejected() {
    let (circuit, full_trace) = build_satisfying_trace_with_mutation(|circuit, trace| {
        let lw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_LW_BIT}]"));
        let sw_addr = find_base_layer_address(circuit, &format!("family_bit[{FAMILY_4_SW_BIT}]"));
        let lw_row = (0..base_trace_len(trace))
            .find(|&r| read_cell(trace, lw_addr, r) == BabyBearField::ONE)
            .expect("multi_family_smoke must execute at least one LW");
        // LW row already has family_bit[15] = 1; force family_bit[16] = 1 too.
        write_cell(trace, sw_addr, lw_row, BabyBearField::ONE);
    });
    assert!(
        !check_satisfied(&circuit, &full_trace),
        "expected two-family-bits-on-one-row mutation to fail check_satisfied"
    );
}
