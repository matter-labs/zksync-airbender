use super::*;

use crate::unrolled::evaluate_witness_for_unified_executor;
use crate::unrolled::UnifiedRiscvCircuitOracle;
use common_constants::circuit_families::*;
use common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER;
use cs::cs::circuit::Circuit;
use cs::machine::ops::unrolled::*;
use cs::machine::NON_DETERMINISM_CSR;
use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use risc_v_simulator::machine_mode_only_unrolled::UnifiedOpcodeTracingDataWithTimestamp;
use risc_v_simulator::{cycle::*, delegations::DelegationsCSRProcessor};
use riscv_transpiler::witness::UnifiedDestinationHolder;

use crate::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits;
use crate::witness_evaluator::unrolled::evaluate_memory_witness_for_unified_executor;

pub mod reduced_machine {
    use crate::unrolled::UnifiedRiscvCircuitOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;
    use ::cs::cs::placeholder::Placeholder;
    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../reduced_machine_preprocessed_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, UnifiedRiscvCircuitOracle<'b>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, UnifiedRiscvCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

#[test]
fn run_unrolled_reduced_test() {
    run_unrolled_reduced_test_impl(None);
}

pub fn run_unrolled_reduced_test_impl(
    maybe_gpu_comparison_hook: Option<Box<dyn Fn(&GpuComparisonArgs)>>,
) {
    use riscv_transpiler::ir::*;
    use riscv_transpiler::replayer::*;
    use riscv_transpiler::vm::*;

    type CountersT = DelegationsCounters;

    // NOTE: these constants must match with ones used in CS crate to produce
    // layout and SSA forms, otherwise derived witness-gen functions may write into
    // invalid locations
    const TRACE_LEN_LOG2: usize = 23;
    const NUM_CYCLES_PER_CHUNK: usize = (1 << TRACE_LEN_LOG2) - 1;

    const SECOND_WORD_BITS: usize = 4;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let lde_factor = 2;
    let tree_cap_size = 32;

    // let worker = Worker::new_with_num_threads(1);
    let worker = Worker::new_with_num_threads(8);

    // load binary
    let binary = std::fs::read("../examples/basic_fibonacci/app.bin").unwrap();
    // let binary = std::fs::read("../tools/verifier/recursion_layer.bin").unwrap();
    assert!(binary.len() % 4 == 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let text_section = std::fs::read("../examples/basic_fibonacci/app.text").unwrap();
    assert!(text_section.len() % 4 == 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    println!("Opcode = 0x{:08x}", text_section[8 / 4]);

    // first run to capture minimal information
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig>(&text_section);

    println!("Opcode = {:?}", instructions[8 / 4]);

    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<SECOND_WORD_BITS>::from_rom_content(&binary, 1 << 30);

    let cycles_bound = 1 << 20;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(cycles_bound, state);
    let mut non_determinism = QuasiUARTSource::default();

    VM::<CountersT>::run_basic_unrolled::<
        SimpleSnapshotter<CountersT, SECOND_WORD_BITS>,
        RamWithRomRegion<SECOND_WORD_BITS>,
        _,
    >(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );

    dbg!(state.counters);

    let total_snapshots = snapshotter.snapshots.len();
    let cycles_upper_bound = cycles_bound;

    let exact_cycles_passed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

    println!("Passed exactly {} cycles", exact_cycles_passed);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;

    let shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(&worker, Global);

    use crate::tracers::oracles::chunk_lazy_init_and_teardown;
    let total_unique_teardowns: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();

    println!("Touched {} unique addresses", total_unique_teardowns);

    let (num_trivial, inits_and_teardowns) = chunk_lazy_init_and_teardown::<Global, _>(
        1,
        NUM_CYCLES_PER_CHUNK,
        &shuffle_ram_touched_addresses,
        &worker,
    );
    assert_eq!(num_trivial, 0, "trivial padding is not expected in tests");

    let final_pc = state.pc;
    let final_timestamp = state.timestamp;

    let register_final_state = state.registers.map(|el| RamShuffleMemStateRecord {
        last_access_timestamp: el.timestamp,
        current_value: el.value,
    });

    let (decoder_table_data, witness_gen_data) =
        process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
            &text_section,
            // &binary, // text_section,
            &[Box::new(ReducedMachineDecoder::new())],
            1 << 20,
            &[NON_DETERMINISM_CSR, BLAKE2S_DELEGATION_CSR_REGISTER as u16],
        )
        .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .unwrap();

    println!("Finished at PC = 0x{:08x}", final_pc);
    for (reg_idx, reg) in register_final_state.iter().enumerate() {
        println!("x{} = {}", reg_idx, reg.current_value);
    }

    let flattened_inits_and_teardowns: Vec<_> = shuffle_ram_touched_addresses
        .into_iter()
        .flatten()
        .collect();

    let mut memory_read_set = BTreeSet::new();
    let mut memory_write_set = BTreeSet::new();

    for i in 0..32 {
        memory_write_set.insert((true, i as u32, 0, 0));
        memory_read_set.insert((
            true,
            i as u32,
            register_final_state[i].last_access_timestamp,
            register_final_state[i].current_value,
        ));
    }

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

    let memory_argument_linearization_challenges_powers: [Mersenne31Quartic;
        NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let delegation_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(5),
        Mersenne31Field(8),
        Mersenne31Field(32),
        Mersenne31Field(16),
    ]);
    let delegation_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(200),
        Mersenne31Field(100),
        Mersenne31Field(300),
        Mersenne31Field(400),
    ]);

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

    let delegation_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            delegation_argument_alpha,
            NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let linearization_challenges: [Mersenne31Quartic; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            state_permutation_argument_alpha,
            NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES,
        )
        .try_into()
        .unwrap();

    let external_challenges = ExternalChallenges {
        memory_argument: ExternalMemoryArgumentChallenges {
            memory_argument_linearization_challenges:
                memory_argument_linearization_challenges_powers,
            memory_argument_gamma,
        },
        delegation_argument: Some(ExternalDelegationArgumentChallenges {
            delegation_argument_linearization_challenges,
            delegation_argument_gamma,
        }),
        machine_state_permutation_argument: Some(ExternalMachineStateArgumentChallenges {
            linearization_challenges,
            additive_term: state_permutation_argument_gamma,
        }),
    };

    let mut permutation_argument_accumulator = produce_pc_into_permutation_accumulator_raw(
        INITIAL_PC,
        split_timestamp(INITIAL_TIMESTAMP),
        final_pc,
        split_timestamp(final_timestamp),
        &external_challenges
            .machine_state_permutation_argument
            .as_ref()
            .unwrap()
            .linearization_challenges,
        &external_challenges
            .machine_state_permutation_argument
            .as_ref()
            .unwrap()
            .additive_term,
    );
    let t = produce_register_contribution_into_memory_accumulator(
        &register_final_state,
        external_challenges
            .memory_argument
            .memory_argument_linearization_challenges,
        external_challenges.memory_argument.memory_argument_gamma,
    );
    permutation_argument_accumulator.mul_assign(&t);

    if true {
        println!("Will try to prove ReducedMachine circuit");

        use cs::machine::ops::unrolled::reduced_machine_ops::*;

        let extra_tables = create_reduced_machine_special_tables::<_, SECOND_WORD_BITS>(
            &binary,
            &[
                common_constants::NON_DETERMINISM_CSR,
                BLAKE2S_DELEGATION_CSR_REGISTER,
            ],
        );
        let circuit = {
            compile_unified_circuit_state_transition::<Mersenne31Field>(
                &|cs| {
                    reduced_machine_table_addition_fn(cs);
                    for (table_type, table) in extra_tables.clone() {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                &|cs| {
                    reduced_machine_circuit_with_preprocessed_bytecode::<_, _, SECOND_WORD_BITS>(cs)
                },
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let mut table_driver = TableDriver::<Mersenne31Field>::new();
        reduced_machine_table_driver_fn(&mut table_driver);
        for (table_type, table) in extra_tables.clone() {
            table_driver.add_table_with_content(table_type, table);
        }

        let num_calls = exact_cycles_passed as usize;
        dbg!(num_calls);

        let mut state = snapshotter.initial_snapshot.state;
        let mut ram_log_buffers = snapshotter
            .reads_buffer
            .make_range(0..snapshotter.reads_buffer.len());

        let mut ram = ReplayerRam::<SECOND_WORD_BITS> {
            ram_log: &mut ram_log_buffers,
        };

        let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
        let mut buffers = vec![&mut buffer[..]];
        let mut tracer = UnifiedDestinationHolder {
            buffers: &mut buffers[..],
        };

        ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _>(
            &mut state,
            &mut ram,
            &tape,
            &mut (),
            cycles_bound,
            &mut tracer,
        );

        assert!(num_calls >= total_unique_teardowns);

        let decoder_table_data = materialize_flattened_decoder_table(&decoder_table_data);

        let oracle = UnifiedRiscvCircuitOracle {
            // prepadding: NUM_CYCLES_PER_CHUNK - num_calls,
            inner: &buffer[..],
            decoder_table: &witness_gen_data,
        };

        let aux_boundary_data = get_aux_boundary_data(
            &circuit,
            NUM_CYCLES_PER_CHUNK,
            &inits_and_teardowns[0].lazy_init_data,
        );

        println!("PC = 0x{:08x}", buffer[18].initial_pc());

        println!(
            "Opcode = 0x{:08x}",
            text_section[buffer[18].initial_pc() as usize / 4]
        );

        println!(
            "Opcode = {:?}",
            instructions[buffer[18].initial_pc() as usize / 4]
        );

        assert_eq!(
            inits_and_teardowns[0].lazy_init_data.len(),
            NUM_CYCLES_PER_CHUNK
        );

        println!("Evaluating memory witness");

        let memory_trace = evaluate_memory_witness_for_unified_executor::<_, Global>(
            &circuit,
            NUM_CYCLES_PER_CHUNK,
            &inits_and_teardowns[0].lazy_init_data,
            &oracle,
            &worker,
            Global,
        );

        println!("Evaluating full witness");

        let full_trace = evaluate_witness_for_unified_executor::<_, Global>(
            &circuit,
            reduced_machine::witness_eval_fn,
            &inits_and_teardowns[0].lazy_init_data,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
        );

        ensure_memory_trace_consistency(&memory_trace, &full_trace);

        parse_shuffle_ram_accesses_from_full_trace(
            &circuit,
            &full_trace,
            &mut memory_write_set,
            &mut memory_read_set,
        );

        println!("Checking is satisfied");

        let is_satisfied = check_satisfied(
            &circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        println!("Precomputing");

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table_data,
            trace_len,
            &circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        let default_security_config =
            prover_stages::ProofSecurityConfig::for_queries_only(5, 28, 63);

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &circuit,
            &vec![],
            &external_challenges,
            full_trace,
            &aux_boundary_data,
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            &default_security_config,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());

        assert_eq!(
            proof.delegation_argument_accumulator.unwrap(),
            Mersenne31Quartic::ZERO
        );
        permutation_argument_accumulator.mul_assign(&proof.permutation_grand_product_accumulator);

        serialize_to_file(&proof, "unified_reduced_unrolled_proof.json");
    }

    // inits and teardowns
    {
        let expected_init_set: Vec<_> = memory_read_set.difference(&memory_write_set).collect();
        let expected_teardown_set: Vec<_> = memory_write_set.difference(&memory_read_set).collect();
        assert_eq!(expected_init_set.len(), expected_teardown_set.len());
        // assert_eq!(expected_init_set.len(), flattened_inits_and_teardowns.len());

        if flattened_inits_and_teardowns.len() != expected_init_set.len() {
            for (idx, (address, (teardown_ts, teardown_value))) in
                flattened_inits_and_teardowns.iter().enumerate()
            {
                let mut init_set_el = None;
                for (i, (is_reg, addr, ts, init_value)) in expected_init_set.iter().enumerate() {
                    if *addr == *address {
                        init_set_el = Some((*is_reg, *addr, *ts, *init_value));
                    }
                }
                let Some(init_set_el) = init_set_el else {
                    panic!("No expected init set element for address {} of flattened inits or teardowns", *address);
                };

                let mut teardown_set_el = None;
                for (i, (is_reg, addr, ts, teardown_value)) in
                    expected_teardown_set.iter().enumerate()
                {
                    if *addr == *address {
                        teardown_set_el = Some((*is_reg, *addr, *ts, *teardown_value));
                    }
                }
                let Some(teardown_set_el) = teardown_set_el else {
                    panic!("No expected teardown set element for address {} of flattened inits or teardowns", *address);
                };
                let (_, _, expected_teardown_ts, expected_teardown_value) = teardown_set_el;
                assert_eq!(
                    *teardown_ts, expected_teardown_ts,
                    "failed for address {}",
                    address
                );
                assert_eq!(
                    *teardown_value, expected_teardown_value,
                    "failed for address {}",
                    address
                );
            }
        }

        for (idx, (is_register, addr, ts, init_value)) in expected_init_set.iter().enumerate() {
            assert!(
                *is_register == false,
                "found an unexpected init for register {} with value {} at timestamp {}",
                *addr,
                *init_value,
                *ts
            );
            assert_eq!(
                *ts, 0,
                "init timestamp is invalid for memory address {}",
                addr
            );
            assert_eq!(
                *init_value, 0,
                "init value is invalid for memory address {}",
                addr
            );
            assert_eq!(
                flattened_inits_and_teardowns[idx].0, *addr,
                "diverged at expected lazy init {}",
                idx
            );
        }
        for (idx, (is_register, addr, ts, value)) in expected_teardown_set.iter().enumerate() {
            assert!(
                *is_register == false,
                "found an unexpected teardown for register {} with value {} at timestamp {}",
                *addr,
                *value,
                *ts
            );
            assert!(
                *ts > INITIAL_TIMESTAMP,
                "teardown timestamp is invalid for memory address {}",
                addr
            );
            assert_eq!(
                flattened_inits_and_teardowns[idx].1 .0, *ts,
                "diverged at expected lazy init {}",
                idx
            );
            assert_eq!(
                flattened_inits_and_teardowns[idx].1 .1, *value,
                "diverged at expected lazy init {}",
                idx
            );
        }

        for ((_, addr0, _, _), (_, addr1, _, _)) in
            expected_init_set.iter().zip(expected_teardown_set.iter())
        {
            assert_eq!(*addr0, *addr1);
        }

        assert_eq!(total_unique_teardowns, expected_teardown_set.len());
    }

    assert_eq!(permutation_argument_accumulator, Mersenne31Quartic::ONE);
}
