use super::*;

use crate::tracers::unrolled::tracer::*;
use crate::unrolled::evaluate_witness_for_executor_family;
use crate::unrolled::run_unrolled_machine_for_num_cycles;
use crate::unrolled::UnifiedRiscvCircuitOracle;
use common_constants::circuit_families::*;
use common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER;
use cs::cs::circuit::Circuit;
use cs::machine::ops::unrolled::*;
use cs::machine::NON_DETERMINISM_CSR;
use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use risc_v_simulator::{cycle::*, delegations::DelegationsCSRProcessor};

use crate::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits;
use crate::witness_evaluator::unrolled::evaluate_memory_witness_for_executor_family;

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

    pub fn witness_eval_fn<'a, 'b>(proxy: &'_ mut SimpleWitnessProxy<'a, UnifiedRiscvCircuitOracle<'b>>) {
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
    // NOTE: these constants must match with ones used in CS crate to produce
    // layout and SSA forms, otherwise derived witness-gen functions may write into
    // invalid locations
    const TRACE_LEN_LOG2: usize = 23;
    const NUM_CYCLES_PER_CHUNK: usize = (1 << TRACE_LEN_LOG2) - 1;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let lde_factor = 2;
    let tree_cap_size = 32;

    let worker = Worker::new_with_num_threads(1);
    // load binary
    let binary = std::fs::read("../tools/verifier/recursion_layer.bin").unwrap();
    assert!(binary.len() % 4 == 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    // let text_section = std::fs::read("../examples/hashed_fibonacci/app.text").unwrap();
    // assert!(text_section.len() % 4 == 0);
    // let text_section: Vec<_> = text_section
    //     .as_chunks::<4>()
    //     .0
    //     .into_iter()
    //     .map(|el| u32::from_le_bytes(*el))
    //     .collect();

    let mut opcode_family_factories = HashMap::new();

    for family in [128] {
        let factory =
            Box::new(|| NonMemTracingFamilyChunk::new_for_num_cycles(NUM_CYCLES_PER_CHUNK));
        opcode_family_factories.insert(family, factory as _);
    }
    let mem_factory =
        Box::new(|| MemTracingFamilyChunk::new_for_num_cycles(NUM_CYCLES_PER_CHUNK)) as _;

    let csr_processor = DelegationsCSRProcessor;

    let mut memory = VectorMemoryImplWithRom::new_for_byte_size(1 << 32, 1 << 21 as usize); // use full RAM
    for (idx, insn) in binary.iter().enumerate() {
        memory.populate(INITIAL_PC + idx as u32 * 4, *insn);
    }

    use crate::tracers::delegation::*;

    let mut factories = HashMap::new();
    for delegation_type in [BLAKE2S_DELEGATION_CSR_REGISTER] {
        if delegation_type == BLAKE2S_DELEGATION_CSR_REGISTER {
            let num_requests_per_circuit = (1 << 20) - 1;
            let delegation_type = delegation_type as u16;
            let factory_fn = move || {
                blake2_with_control_factory_fn(delegation_type, num_requests_per_circuit, Global)
            };
            factories.insert(
                delegation_type,
                Box::new(factory_fn) as Box<dyn Fn() -> DelegationWitness + Send + Sync + 'static>,
            );
        } else {
            panic!(
                "delegation type {} is unsupported for tests",
                delegation_type
            )
        }
    }

    let mut src = std::fs::File::open("../execution_utils/recursion_layer_flattened.json").unwrap();
    let raw_src: Vec<u32> = serde_json::from_reader(&mut src).unwrap();

    let preprocessing_data = process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        &binary, // text_section,
        &[Box::new(ReducedMachineDecoder)],
        1 << 20,
        &[NON_DETERMINISM_CSR, BLAKE2S_DELEGATION_CSR_REGISTER as u16],
    );

    let (
        final_pc,
        family_circuits,
        mem_circuits,
        delegation_circuits,
        register_final_state,
        shuffle_ram_touched_addresses,
    ) = {
        let mut non_determinism = QuasiUARTSource::new_with_reads(raw_src);

        // TODO: use other tracer
        run_unrolled_machine_for_num_cycles::<_, IMStandardIsaConfigWithUnsignedMulDiv, Global>(
            NUM_CYCLES_PER_CHUNK,
            INITIAL_PC,
            csr_processor,
            &mut memory,
            1 << 21,
            &mut non_determinism,
            opcode_family_factories,
            mem_factory,
            factories,
            1 << 32,
            &worker,
        )
    };

    println!("Finished at PC = 0x{:08x}", final_pc);
    for (reg_idx, reg) in register_final_state.iter().enumerate() {
        println!("x{} = {}", reg_idx, reg.current_value);
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

    let external_values = ExternalValues {
        challenges: ExternalChallenges {
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
        },
        aux_boundary_values: AuxArgumentsBoundaryValues::default(),
    };

    if true {
        println!("Will try to prove ReducedMachine circuit");

        use cs::machine::ops::unrolled::reduced_machine_ops::*;
        const SECOND_WORD_BITS: usize = 5;

        let extra_tables = create_reduced_machine_special_tables::<_, SECOND_WORD_BITS>(
            &binary,
            &[common_constants::NON_DETERMINISM_CSR, BLAKE2S_DELEGATION_CSR_REGISTER],
        );
        let circuit = {
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
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

        let family_data = &mem_circuits;
        assert_eq!(family_data.len(), 1);
        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = MemoryCircuitOracle {
            inner: &family_data[0].data,
            decoder_table: witness_gen_data,
        };

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[29].opcode_data.opcode
        // );

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &circuit,
            reduced_machine::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
        );

        let is_satisfied = check_satisfied(
            &circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

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

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &circuit,
            &vec![],
            &external_values.challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            53,
            28,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());
    }
}
