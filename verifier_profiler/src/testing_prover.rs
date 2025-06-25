use super::*;

use worker::Worker;
use prover::prover_stages::Proof;

pub mod blake2s_delegation_with_gpu_tracer {
    use prover::tracers::oracles::delegation_oracle::DelegationCircuitOracle;
    use prover::witness_evaluator::SimpleWitnessProxy;
    use prover::witness_proxy::WitnessProxy;

    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalInteger,
        WitnessComputationalU16, WitnessComputationalU32,
    };
    use ::field::*;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../prover/blake_delegation_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, DelegationCircuitOracle<'b>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, DelegationCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

pub fn generate_testing_proof(
    config: &ProfilingConfig,
) -> Proof {
    const SECOND_WORD_BITS_FOUR: usize = 4;
    const SECOND_WORD_BITS_FIVE: usize = 5;
    const NUM_DELEGATION_CYCLES: usize = (1 << 20) - 1;

    let domain_size = 1 << config.trace_len_log;
    let delegation_domain_size = NUM_DELEGATION_CYCLES + 1;
    let lde_factor = 2;
    let tree_cap_size = 32;

    // let worker = Worker::new_with_num_threads(1);
    let worker = Worker::new();

    // load binary

    let binary = std::fs::read("../examples/hashed_fibonacci/app.bin").unwrap();
    assert!(binary.len() % 4 == 0);
    let binary: Vec<_> = binary
        .array_chunks::<4>()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let rom_table = match config.second_word_bits {
        SECOND_WORD_BITS_FOUR => create_table_for_rom_image::<Mersenne31Field, SECOND_WORD_BITS_FOUR>(
            &binary,
            TableType::RomRead.to_table_id(),
        ),
        SECOND_WORD_BITS_FIVE => create_table_for_rom_image::<_, SECOND_WORD_BITS_FIVE>(
            &binary,
            TableType::RomRead.to_table_id(),
        ),
        _ => panic!("Unsupported second word bits: {}", config.second_word_bits),
    };

    use risc_v_simulator::delegations::blake2_round_function_with_compression_mode::BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID;

    let csr_table = create_csr_table_for_delegation(
        true,
        // &[BLAKE2_ROUND_FUNCTION_ACCESS_ID],
        &[BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID],
        TableType::SpecialCSRProperties.to_table_id(),
    );

    let compiled_machine = if config.reduced_machine {
        let machine = MinimalMachineNoExceptionHandlingWithDelegation;
        match config.second_word_bits {
            SECOND_WORD_BITS_FOUR => default_compile_machine::<MinimalMachineNoExceptionHandlingWithDelegation, SECOND_WORD_BITS_FOUR>(
                machine,
                rom_table.clone(),
                Some(csr_table.clone()),
                config.trace_len_log
            ),
            SECOND_WORD_BITS_FIVE => default_compile_machine::<_, SECOND_WORD_BITS_FIVE>(
                machine,
                rom_table.clone(),
                Some(csr_table.clone()),
                config.trace_len_log
            ),
            _ => panic!("Unsupported second word bits: {}", config.second_word_bits),
        }
    } else {
        let machine = FullIsaMachineWithDelegationNoExceptionHandling;
        match config.second_word_bits {
            SECOND_WORD_BITS_FOUR =>
                default_compile_machine::<_, SECOND_WORD_BITS_FOUR>(
                    machine, 
                    rom_table.clone(), 
                    Some(csr_table.clone()), 
                    config.trace_len_log
            ),
            SECOND_WORD_BITS_FIVE => default_compile_machine::<_, SECOND_WORD_BITS_FIVE>(
                machine, 
                rom_table.clone(), 
                Some(csr_table.clone()), 
                config.trace_len_log
            ),
            _ => panic!("Unsupported second word bits: {}", config.second_word_bits),
        }
    };

    // recreate table driver for witness evaluation
    use cs::machine::machine_configurations::create_table_driver;
    // let mut table_driver = create_table_driver::<_, _, SECOND_WORD_BITS>(machine);
    let mut table_driver = if config.reduced_machine {
        let machine = MinimalMachineNoExceptionHandlingWithDelegation;
        match config.second_word_bits {
            SECOND_WORD_BITS_FOUR => create_table_driver::<_, _, SECOND_WORD_BITS_FOUR>(machine),
            SECOND_WORD_BITS_FIVE => create_table_driver::<_, _, SECOND_WORD_BITS_FIVE>(machine),
            _ => panic!("Unsupported second word bits: {}", config.second_word_bits),
        }
    } else {
        let machine = FullIsaMachineWithDelegationNoExceptionHandling;
        match config.second_word_bits {
            SECOND_WORD_BITS_FOUR => create_table_driver::<_, _, SECOND_WORD_BITS_FOUR>(machine),
            SECOND_WORD_BITS_FIVE => create_table_driver::<_, _, SECOND_WORD_BITS_FIVE>(machine),
            _ => panic!("Unsupported second word bits: {}", config.second_word_bits),
        }
    };

    use cs::tables::LookupWrapper;
    // add preimage into table driver
    table_driver.add_table_with_content(TableType::RomRead, LookupWrapper::Dimensional3(rom_table));
    // add table of allowed delegation
    table_driver.add_table_with_content(
        TableType::SpecialCSRProperties,
        LookupWrapper::Dimensional3(csr_table.clone()),
    );

    use risc_v_simulator::delegations::DelegationsCSRProcessor;
    let trace_len = domain_size;
    let csr_processor = DelegationsCSRProcessor;

    // compile all delegation circuit

    use std::collections::HashMap;
    use prover::tracers::oracles::delegation_oracle::DelegationCircuitOracle;
    use cs::cs::cs_reference::BasicAssembly;
    use cs::one_row_compiler::OneRowCompiler;
    use cs::cs::circuit::Circuit;
    use prover::DelegationProcessorDescription;

    let mut delegation_circuits_eval_fns: HashMap<
        u32,
        fn(&mut SimpleWitnessProxy<'_, DelegationCircuitOracle<'_>>),
    > = HashMap::new();
    let mut delegation_circuits = vec![];
    {
        use cs::delegation::blake2_round_with_extended_control::define_blake2_with_extended_control_delegation_circuit;
        let mut cs = BasicAssembly::<Mersenne31Field>::new();
        define_blake2_with_extended_control_delegation_circuit(&mut cs);
        let (circuit_output, _) = cs.finalize();
        let table_driver = circuit_output.table_driver.clone();
        let compiler = OneRowCompiler::default();
        let circuit = compiler.compile_to_evaluate_delegations(
            circuit_output,
            delegation_domain_size.trailing_zeros() as usize,
        );

        // if !for_gpu_comparison {
        //     serialize_to_file(&circuit, "blake2s_delegation_circuit_layout.json");
        // }

        let delegation_type = BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID;
        let description = DelegationProcessorDescription {
            delegation_type: BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID,
            num_requests_per_circuit: NUM_DELEGATION_CYCLES,
            trace_len: NUM_DELEGATION_CYCLES + 1,
            table_driver,
            compiled_circuit: circuit,
        };

        delegation_circuits.push((delegation_type, description));
        delegation_circuits_eval_fns.insert(
            delegation_type,
            blake2s_delegation_with_gpu_tracer::witness_eval_fn,
        );
    }

    // 15 fibs, 1 hash
    let non_determinism_responses = vec![15u32, 1];

    use prover::dev_run_all_and_make_witness_ext_with_gpu_tracers;

    let witness_eval_fn = crate::witness_generation_functions::get_witness_function_from_config(config);

    let (witness_chunks, register_final_values, delegation_circuits) = if config.reduced_machine {
        let machine = MinimalMachineNoExceptionHandlingWithDelegation;
        match config.second_word_bits {
            SECOND_WORD_BITS_FOUR => dev_run_all_and_make_witness_ext_with_gpu_tracers::<
                _,
                IMStandardIsaConfig,
                _,
                SECOND_WORD_BITS_FOUR,
            >(
                machine,
                &compiled_machine,
                witness_eval_fn,
                delegation_circuits_eval_fns,
                &delegation_circuits,
                &binary,
                domain_size - 1,
                trace_len,
                csr_processor,
                Some(LookupWrapper::Dimensional3(csr_table)),
                non_determinism_responses,
                &worker,
            ),
            SECOND_WORD_BITS_FIVE => dev_run_all_and_make_witness_ext_with_gpu_tracers::<
                _,
                IMStandardIsaConfig,
                _,
                SECOND_WORD_BITS_FIVE,
            >(
                machine,
                &compiled_machine,
                witness_eval_fn,
                delegation_circuits_eval_fns,
                &delegation_circuits,
                &binary,
                domain_size - 1,
                trace_len,
                csr_processor,
                Some(LookupWrapper::Dimensional3(csr_table)),
                non_determinism_responses,
                &worker,
            ),
            _ => panic!("Unsupported second word bits: {}", config.second_word_bits),
        }
    } else {
        let machine = FullIsaMachineWithDelegationNoExceptionHandling;
        match config.second_word_bits {
            SECOND_WORD_BITS_FOUR => dev_run_all_and_make_witness_ext_with_gpu_tracers::<
                _,
                IMStandardIsaConfig,
                _,
                SECOND_WORD_BITS_FOUR,
            >(
                machine,
                &compiled_machine,
                witness_eval_fn,
                delegation_circuits_eval_fns,
                &delegation_circuits,
                &binary,
                domain_size - 1,
                trace_len,
                csr_processor,
                Some(LookupWrapper::Dimensional3(csr_table)),
                non_determinism_responses,
                &worker,
            ),
            SECOND_WORD_BITS_FIVE => dev_run_all_and_make_witness_ext_with_gpu_tracers::<
                _,
                IMStandardIsaConfig,
                _,
                SECOND_WORD_BITS_FIVE,
            >(
                machine,
                &compiled_machine,
                witness_eval_fn,
                delegation_circuits_eval_fns,
                &delegation_circuits,
                &binary,
                domain_size - 1,
                trace_len,
                csr_processor,
                Some(LookupWrapper::Dimensional3(csr_table)),
                non_determinism_responses,
                &worker,
            ),
            _ => panic!("Unsupported second word bits: {}", config.second_word_bits),
        }
    };

    assert_eq!(witness_chunks.len(), 1);

    use std::alloc::Global;
    use fft::Twiddles;
    use fft::LdePrecomputations;
    use prover::prover_stages::SetupPrecomputations;

    let twiddles: Twiddles<_, Global> = Twiddles::new(domain_size, &worker);
    let lde_precomputations = LdePrecomputations::new(domain_size, lde_factor, &[0, 1], &worker);

    let setup = SetupPrecomputations::from_tables_and_trace_len(
        &table_driver,
        trace_len,
        &compiled_machine.setup_layout,
        &twiddles,
        &lde_precomputations,
        lde_factor,
        tree_cap_size,
        &worker,
    );

    let witness = witness_chunks.into_iter().next().unwrap();

    use prover::check_satisfied;

    println!("Checking if satisfied");
    let is_satisfied = check_satisfied(
        &compiled_machine,
        &witness.exec_trace,
        witness.num_witness_columns,
    );
    assert!(is_satisfied);

    use field::Mersenne31Quartic;
    use field::Mersenne31Complex;
    use field::PrimeField;
    use field::Field;

    let challenge = Mersenne31Quartic {
        c0: Mersenne31Complex {
            c0: Mersenne31Field::from_u64_unchecked(42),
            c1: Mersenne31Field::from_u64_unchecked(42),
        },
        c1: Mersenne31Complex {
            c0: Mersenne31Field::from_u64_unchecked(42),
            c1: Mersenne31Field::from_u64_unchecked(42),
        },
    };

    let mut current_challenge = Mersenne31Quartic::ONE;

    // tau == 1 here
    let tau = Mersenne31Quartic::ONE;
    use field::FieldExtension;

    // TODO: properly adjust challenges by tau^H/2, so we can move similar powers to compiled constraint without
    // touching quadratic coefficients
    current_challenge.mul_assign_by_base(&tau);
    current_challenge.mul_assign_by_base(&tau);

    let mut quad_terms_challenges = vec![];
    for _ in 0..compiled_machine.degree_2_constraints.len() {
        quad_terms_challenges.push(current_challenge);
        current_challenge.mul_assign(&challenge);
    }

    current_challenge.mul_assign_by_base(&tau.inverse().unwrap());

    let mut linear_terms_challenges = vec![];
    for _ in 0..compiled_machine.degree_1_constraints.len() {
        linear_terms_challenges.push(current_challenge);
        current_challenge.mul_assign(&challenge);
    }

//     // // we can also evaluate constraint for debug purposes
//     // {
//     //     let compiled_constraints = CompiledConstraintsForDomain::from_compiled_circuit(
//     //         &compiled_machine,
//     //         Mersenne31Complex::ONE,
//     //         trace_len as u32,
//     //     );

//     //     let now = std::time::Instant::now();
//     //     let quotient_view = evaluate_constraints_on_domain(
//     //         &witness.exec_trace,
//     //         witness.num_witness_columns,
//     //         &quad_terms_challenges,
//     //         &linear_terms_challenges,
//     //         &compiled_constraints,
//     //         &worker,
//     //     );
//     //     dbg!(&now.elapsed());

//     //     let mut quotient_row = quotient_view.row_view(0..NUM_PROC_CYCLES);
//     //     for _ in 0..NUM_PROC_CYCLES {
//     //         let as_field = unsafe {
//     //             quotient_row
//     //                 .current_row_ref()
//     //                 .as_ptr()
//     //                 .cast::<Mersenne31Quartic>()
//     //                 .read()
//     //         };
//     //         assert_eq!(as_field, Mersenne31Quartic::ZERO);
//     //         quotient_row.advance_row();
//     //     }
//     // }

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

    use cs::one_row_compiler::NUM_MEM_ARGUMENT_KEY_PARTS;
    use fft::materialize_powers_serial_starting_with_elem;

    let memory_argument_linearization_challenges_powers: [Mersenne31Quartic;
        NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    dbg!(&witness.aux_data);

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

    use cs::one_row_compiler::NUM_DELEGATION_ARGUMENT_KEY_PARTS;

    let delegation_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            delegation_argument_alpha,
            NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    use prover::definitions::*;

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
        },
        aux_boundary_values: AuxArgumentsBoundaryValues {
            lazy_init_first_row: witness.aux_data.lazy_init_first_row,
            teardown_value_first_row: witness.aux_data.teardown_value_first_row,
            teardown_timestamp_first_row: witness.aux_data.teardown_timestamp_first_row,
            lazy_init_one_before_last_row: witness.aux_data.lazy_init_one_before_last_row,
            teardown_value_one_before_last_row: witness.aux_data.teardown_value_one_before_last_row,
            teardown_timestamp_one_before_last_row: witness
                .aux_data
                .teardown_timestamp_one_before_last_row,
        },
    };

    let mut public_inputs = witness.aux_data.first_row_public_inputs.clone();
    public_inputs.extend(witness.aux_data.one_before_last_row_public_inputs.clone());

    dbg!(&external_values);

    use prover::prover_stages::prove;

    let now = std::time::Instant::now();
    let (prover_data, proof) = prove::<{prover::DEFAULT_TRACE_PADDING_MULTIPLE}, _>(
        &compiled_machine,
        &public_inputs,
        &external_values,
        witness,
        &setup,
        &twiddles,
        &lde_precomputations,
        0,
        None,
        lde_factor,
        tree_cap_size,
        53,
        28,
        &worker,
    );
    println!("Full machine proving time is {:?}", now.elapsed());

    proof

//     if !for_gpu_comparison {
//         serialize_to_file(&proof, "delegation_proof");
//     }

//     if let Some(ref gpu_comparison_hook) = maybe_delegator_gpu_comparison_hook {
//         let log_n = (NUM_PROC_CYCLES + 1).trailing_zeros();
//         assert_eq!(log_n, 20);
//         let gpu_comparison_args = GpuComparisonArgs {
//             circuit: &compiled_machine,
//             setup: &setup,
//             external_values: &external_values,
//             public_inputs: &public_inputs,
//             twiddles: &twiddles,
//             lde_precomputations: &lde_precomputations,
//             table_driver: &table_driver,
//             lookup_mapping: lookup_mapping_for_gpu.unwrap(),
//             log_n: log_n as usize,
//             circuit_sequence: 0,
//             delegation_processing_type: None,
//             prover_data: &prover_data,
//         };
//         gpu_comparison_hook(&gpu_comparison_args);
//     }

//     let register_contribution_in_memory_argument =
//         produce_register_contribution_into_memory_accumulator(
//             &register_final_values,
//             memory_argument_linearization_challenges_powers,
//             memory_argument_gamma,
//         );

//     dbg!(&prover_data.stage_2_result.grand_product_accumulator);
//     dbg!(&prover_data.stage_2_result.sum_over_delegation_poly);
//     dbg!(register_contribution_in_memory_argument);

//     let mut memory_accumulator = prover_data.stage_2_result.grand_product_accumulator;
//     memory_accumulator.mul_assign(&register_contribution_in_memory_argument);

//     let mut sum_over_delegation_poly = prover_data.stage_2_result.sum_over_delegation_poly;

//     // now prove delegation circuits
//     let mut external_values = external_values;
//     external_values.aux_boundary_values = Default::default();
//     for work_type in delegation_circuits.into_iter() {
//         dbg!(work_type.delegation_type);
//         dbg!(work_type.trace_len);
//         dbg!(work_type.work_units.len());

//         let delegation_type = work_type.delegation_type;
//         // create setup
//         let twiddles: Twiddles<_, Global> = Twiddles::new(work_type.trace_len, &worker);
//         let lde_precomputations =
//             LdePrecomputations::new(work_type.trace_len, lde_factor, &[0, 1], &worker);

//         let setup = SetupPrecomputations::from_tables_and_trace_len(
//             &work_type.table_driver,
//             work_type.trace_len,
//             &work_type.compiled_circuit.setup_layout,
//             &twiddles,
//             &lde_precomputations,
//             lde_factor,
//             tree_cap_size,
//             &worker,
//         );

//         for witness in work_type.work_units.into_iter() {
//             println!(
//                 "Checking if delegation type {} circuit is satisfied",
//                 delegation_type
//             );
//             let is_satisfied = check_satisfied(
//                 &work_type.compiled_circuit,
//                 &witness.witness.exec_trace,
//                 witness.witness.num_witness_columns,
//             );
//             assert!(is_satisfied);

//             let lookup_mapping_for_gpu = if maybe_delegated_gpu_comparison_hook.is_some() {
//                 Some(witness.witness.lookup_mapping.clone())
//             } else {
//                 None
//             };

//             dbg!(witness.witness.exec_trace.len());
//             let now = std::time::Instant::now();
//             let (prover_data, proof) = prove::<DEFAULT_TRACE_PADDING_MULTIPLE, _>(
//                 &work_type.compiled_circuit,
//                 &[],
//                 &external_values,
//                 witness.witness,
//                 &setup,
//                 &twiddles,
//                 &lde_precomputations,
//                 0,
//                 Some(delegation_type),
//                 lde_factor,
//                 tree_cap_size,
//                 53,
//                 28,
//                 &worker,
//             );
//             println!(
//                 "Delegation circuit type {} proving time is {:?}",
//                 delegation_type,
//                 now.elapsed()
//             );

//             if let Some(ref gpu_comparison_hook) = maybe_delegated_gpu_comparison_hook {
//                 let log_n = work_type.trace_len.trailing_zeros();
//                 assert_eq!(work_type.trace_len, 1 << log_n);
//                 let dummy_public_inputs = Vec::<Mersenne31Field>::new();
//                 let gpu_comparison_args = GpuComparisonArgs {
//                     circuit: &work_type.compiled_circuit,
//                     setup: &setup,
//                     external_values: &external_values,
//                     public_inputs: &dummy_public_inputs,
//                     twiddles: &twiddles,
//                     lde_precomputations: &lde_precomputations,
//                     table_driver: &work_type.table_driver,
//                     lookup_mapping: lookup_mapping_for_gpu.unwrap(),
//                     log_n: log_n as usize,
//                     circuit_sequence: 0,
//                     delegation_processing_type: Some(delegation_type),
//                     prover_data: &prover_data,
//                 };
//                 gpu_comparison_hook(&gpu_comparison_args);
//             }

//             if !for_gpu_comparison {
//                 serialize_to_file(&proof, "blake2s_delegator_proof");
//             }

//             dbg!(prover_data.stage_2_result.grand_product_accumulator);
//             dbg!(prover_data.stage_2_result.sum_over_delegation_poly);

//             memory_accumulator.mul_assign(&prover_data.stage_2_result.grand_product_accumulator);
//             sum_over_delegation_poly
//                 .sub_assign(&prover_data.stage_2_result.sum_over_delegation_poly);
//         }
//     }

//     assert_eq!(memory_accumulator, Mersenne31Quartic::ONE);
//     assert_eq!(sum_over_delegation_poly, Mersenne31Quartic::ZERO);
}
