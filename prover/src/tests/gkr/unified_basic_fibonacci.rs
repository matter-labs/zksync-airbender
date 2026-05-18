use super::family_circuits::SecurityLevel;
use super::*;
use crate::definitions::produce_initial_permutation_product_contribution;
use crate::gkr::prover::prove_configured_with_gkr;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::prover_config::example_configs;
use crate::gkr::witness_gen::family_circuits::{
    build_unified_table_driver, evaluate_gkr_memory_witness_for_unified_family,
    evaluate_gkr_witness_for_unified_family,
};
use crate::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use crate::gkr::witness_gen::trace_structs::RamShuffleMemStateRecord;
use crate::merkle_trees::DefaultTreeConstructor;
use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use common_constants::TIMESTAMP_STEP;
use cs::definitions::INITIAL_TIMESTAMP;
use cs::definitions::*;
use cs::gkr_circuits::process_binary_into_separate_tables_ext;
use cs::gkr_circuits::unified_reduced_machine::UnifiedReducedMachineDecoder;
use cs::gkr_circuits::OpcodeFamilyDecoder;
use fft::materialize_powers_serial_starting_with_elem;
use fft::Twiddles;
use field::Field;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::{preprocess_bytecode, Instruction};
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::replayer::*;
use riscv_transpiler::vm::*;
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::UnifiedDestinationHolder;
use std::alloc::Global;
use std::collections::BTreeSet;
use worker::Worker;

const INITIAL_PC: u32 = 0;
const WORD_BITS: u32 = core::mem::size_of::<u32>().trailing_zeros();

const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;

const USE_GKR_WITH_CACHES: bool = cfg!(not(feature = "no_caches"));

#[test]
fn gkr_run_basic_unrolled_test_sec_80_unified_reduced_machine() {
    run_unified_smoke_test(SecurityLevel::Sec80);
}

fn run_unified_smoke_test(level: SecurityLevel) {
    type CountersT = DelegationsAndUnifiedCounters;

    let proof_suffix = level.dir_suffix();
    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    // Load the circuit first so we can size `inits_and_teardowns` + the RAM bound
    // from the actual layout. `num_inits_and_teardowns_pairs` in the compile API
    // expands to 2× layout teardown_sets (init set + teardown set per pair);
    // hardcoding the count drifts.
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
    // CSR inputs read by multi_family_smoke: n (loop bound, masked to 0xF) and seed.
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

    let exact_cycles_passed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
    println!("multi_family_smoke ran {} cycles", exact_cycles_passed);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;
    let num_calls = counters.get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    assert!(num_calls < NUM_CYCLES_PER_CHUNK);

    let shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(&worker, Global);
    let total_unique_teardowns: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();
    println!("Touched {} unique addresses", total_unique_teardowns);

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
    let final_pc = state.pc;
    let final_timestamp = state.timestamp;
    let register_final_state = state.registers.map(|el| RamShuffleMemStateRecord {
        last_access_timestamp: el.timestamp,
        current_value: el.value,
    });

    let memory_argument_alpha = BabyBearExt4::from_array_of_base([
        BabyBearField::new(2),
        BabyBearField::new(5),
        BabyBearField::new(42),
        BabyBearField::new(123),
    ]);
    let permutation_argument_additive_part = BabyBearExt4::from_array_of_base([
        BabyBearField::new(7),
        BabyBearField::new(11),
        BabyBearField::new(1024),
        BabyBearField::new(8000),
    ]);
    let permutation_argument_linearization_challenges: [BabyBearExt4;
        NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();
    let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4> {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    };

    // Unified-circuit decoder produces a single family-128 entry covering every
    // PC slot in the bytecode region.
    let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> = vec![Box::new(UnifiedReducedMachineDecoder)];
    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(&text_section, &decoders, 1 << 20, &[]);

    // Replay capturing every reduced-machine cycle into a single buffer.
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

    let decoder_table_data = &preprocessing_data[&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX];
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|el| el.unwrap_or(Default::default()))
        .collect::<Vec<_>>();

    let oracle = UnifiedRiscvCircuitOracle {
        inner: &buffer[..],
        decoder_table: &witness_gen_data,
    };

    let table_driver = build_unified_table_driver::<BabyBearField>(&binary);

    println!("Computing memory trace");
    let memory_trace = evaluate_gkr_memory_witness_for_unified_family::<BabyBearField, _, _, _>(
        &circuit,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &worker,
        Some(inits_and_teardowns.clone()),
        Global,
        Global,
    );

    println!("Computing full trace");
    let full_trace = evaluate_gkr_witness_for_unified_family::<BabyBearField, _, _, _>(
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

    ensure_memory_trace_consistency(&memory_trace, &full_trace);

    println!("Checking constraint satisfiability");
    assert!(
        check_satisfied(&circuit, &full_trace),
        "unified circuit constraint not satisfied"
    );

    let register_final_state_raw = register_final_state
        .map(|el| (el.current_value, split_timestamp(el.last_access_timestamp)));
    let mut permutation_argument_accumulator =
        produce_initial_permutation_product_contribution::<BabyBearField, BabyBearExt4>(
            &register_final_state_raw,
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            final_pc,
            split_timestamp(final_timestamp),
            &external_challenges,
        );

    let mut write_set = BTreeSet::<(u32, TimestampScalar)>::new();
    let mut read_set = BTreeSet::<(u32, TimestampScalar)>::new();
    write_set.insert((INITIAL_PC, INITIAL_TIMESTAMP));
    read_set.insert((final_pc, final_timestamp));

    let mut memory_read_set = BTreeSet::new();
    let mut memory_write_set = BTreeSet::new();
    let mut delegation_write_set = BTreeSet::new();
    for i in 0..32 {
        memory_write_set.insert((true, i as u32, 0, 0));
        memory_read_set.insert((
            true,
            i as u32,
            register_final_state[i].last_access_timestamp,
            register_final_state[i].current_value,
        ));
    }

    parse_state_permutation_elements_from_full_trace(
        &circuit,
        &memory_trace,
        &mut write_set,
        &mut read_set,
    );
    parse_shuffle_ram_accesses_from_full_trace(
        &circuit,
        &memory_trace,
        &mut memory_write_set,
        &mut memory_read_set,
        &mut delegation_write_set,
    );

    for (pc, ts) in write_set.iter().copied() {
        assert!(
            read_set.contains(&(pc, ts)),
            "read set doesn't contain machine-state pair {:?}",
            (pc, ts)
        );
    }
    for (pc, ts) in read_set.iter().copied() {
        assert!(
            write_set.contains(&(pc, ts)),
            "write set doesn't contain machine-state pair {:?}",
            (pc, ts)
        );
    }
    
    {
        let flattened_inits_and_teardowns: Vec<_> = shuffle_ram_touched_addresses
            .iter()
            .flatten()
            .copied()
            .collect();
        let expected_init_set: Vec<_> = memory_read_set.difference(&memory_write_set).collect();
        let expected_teardown_set: Vec<_> = memory_write_set.difference(&memory_read_set).collect();
        assert_eq!(
            expected_init_set.len(),
            expected_teardown_set.len(),
            "inits and teardowns must have the same cardinality"
        );
        assert_eq!(
            total_unique_teardowns,
            expected_teardown_set.len(),
            "prover's teardown count must match the read - write difference"
        );
        for (idx, (is_register, addr, ts, init_value)) in expected_init_set.iter().enumerate() {
            assert!(
                !*is_register,
                "found an unexpected init for register {} (value={}, ts={})",
                addr, init_value, ts
            );
            assert_eq!(*ts, 0, "init timestamp must be 0 for address {}", addr);
            assert_eq!(*init_value, 0, "init value must be 0 for address {}", addr);
            assert_eq!(
                flattened_inits_and_teardowns[idx].0, *addr,
                "init address divergence at index {}",
                idx
            );
        }
        for (idx, (is_register, addr, ts, value)) in expected_teardown_set.iter().enumerate() {
            assert!(
                !*is_register,
                "found an unexpected teardown for register {} (value={}, ts={})",
                addr, value, ts
            );
            assert!(
                *ts > INITIAL_TIMESTAMP,
                "teardown ts must be > INITIAL_TIMESTAMP at address {}",
                addr
            );
            assert_eq!(
                flattened_inits_and_teardowns[idx].1 .0, *ts,
                "teardown timestamp divergence at index {}",
                idx
            );
            assert_eq!(
                flattened_inits_and_teardowns[idx].1 .1, *value,
                "teardown value divergence at index {}",
                idx
            );
        }
        for ((_, addr_init, _, _), (_, addr_teardown, _, _)) in
            expected_init_set.iter().zip(expected_teardown_set.iter())
        {
            assert_eq!(
                *addr_init, *addr_teardown,
                "init/teardown address pair must align"
            );
        }
    }

    let prover_config = example_configs::config_for_security_level_under_pessimistic_conjecture(
        trace_len.trailing_zeros() as usize,
        level,
    );
    println!("Preparing twiddles");
    let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
    println!("Preparing setup");
    let setup = GKRSetup::construct(&table_driver, &decoder_table_data, trace_len, &circuit);
    let setup_commitment = setup.commit(
        &twiddles,
        prover_config.lde_factor,
        prover_config.base_oracles_values_per_leaf.trailing_zeros() as usize,
        prover_config.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );

    // Inline inits/teardowns: one set of `top_bits` per teardown_set the artifact
    // carries. Standalone i/t uses the same shape.
    let inits_and_teardowns_top_bits: Vec<u32> = (0..circuit.memory_layout.teardown_sets.len())
        .map(|i| i as u32)
        .collect();

    println!("Trying to prove");
    let now = std::time::Instant::now();
    let proof = prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
        &circuit,
        &external_challenges,
        full_trace,
        &setup,
        &setup_commitment,
        &twiddles,
        &prover_config,
        inits_and_teardowns_top_bits,
        trace_len,
        &worker,
    );
    println!("Proving time is {:?}", now.elapsed());
    println!(
        "Estimated proof size without compression is {} bytes",
        proof.estimate_size()
    );

    permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);

    serialize_to_file(
        &proof,
        &format!(
            "test_proofs/unified_reduced_machine_{}_gkr_proof.json",
            proof_suffix
        ),
    );

    // The unified circuit subsumes machine state + inline inits/teardowns into a
    // single grand product. With no delegations the accumulator must close to ONE.
    assert_eq!(
        permutation_argument_accumulator,
        BabyBearExt4::ONE,
        "unified grand-product accumulator should be ONE"
    );
}
