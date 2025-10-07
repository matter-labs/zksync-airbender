use super::*;

use crate::tracers::oracles::delegation_oracle::DelegationCircuitOracle;
use cs::cs::{circuit::Circuit, cs_reference::BasicAssembly};
use full_isa_with_delegation_no_exceptions::FullIsaMachineWithDelegationNoExceptionHandling;
use risc_v_simulator::{cycle::IMStandardIsaConfig, delegations::DelegationsCSRProcessor};

const SECOND_WORD_BITS: usize = 4;

use common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER;

// use --features debug_satisfiable
pub fn run_keccak_test_impl(
    maybe_delegator_gpu_comparison_hook: Option<Box<dyn Fn(&GpuComparisonArgs)>>,
    maybe_delegated_gpu_comparison_hook: Option<Box<dyn Fn(&GpuComparisonArgs)>>,
) {
    // NOTE: these constants must match with ones used in CS crate to produce
    // layout and SSA forms, otherwise derived witness-gen functions may write into
    // invalid locations
    const NUM_PROC_CYCLES: usize = (1 << 20) - 1;
    const NUM_DELEGATION_CYCLES: usize = (1 << 20) - 1;

    let domain_size = NUM_PROC_CYCLES + 1;
    let delegation_domain_size = NUM_DELEGATION_CYCLES + 1;
    let lde_factor = 2;
    let tree_cap_size = 32;

    let worker = Worker::new_with_num_threads(1);
    // let worker = Worker::new_with_num_threads(2);
    // let worker = Worker::new_with_num_threads(4);
    // let worker = Worker::new_with_num_threads(8);
    // let worker = Worker::new_with_num_threads(16);

    // load binary
    // let binary = KECCAK_F1600_BIN; // old bin just does one f1600 iteration w/out checks
    let binary = {
        let bytes = APP_KECCAK_SIMPLE_BIN; // single keccak_f1600 testcase
                                           // let bytes = APP_KECCAK_BENCH_BIN; // 2k iterations of keccak_f1600 on same state (no checks)
        let (chunks, []) = bytes.as_chunks::<4>() else {
            unreachable!()
        };
        chunks
            .into_iter()
            .map(|&x| u32::from_le_bytes(x))
            .collect::<Vec<u32>>()
    };

    let rom_table = create_table_for_rom_image::<_, SECOND_WORD_BITS>(
        &binary,
        TableType::RomRead.to_table_id(),
    );

    let csr_table = create_csr_table_for_delegation(
        true,
        &[KECCAK_SPECIAL5_CSR_REGISTER],
        TableType::SpecialCSRProperties.to_table_id(),
    );

    let machine = FullIsaMachineWithDelegationNoExceptionHandling;
    let compiled_machine = default_compile_machine::<_, SECOND_WORD_BITS>(
        machine,
        rom_table.clone(),
        Some(csr_table.clone()),
        domain_size.trailing_zeros() as usize,
    );

    // recreate table driver for witness evaluation
    let mut table_driver = create_table_driver::<_, _, SECOND_WORD_BITS>(machine);
    // add preimage into table driver
    table_driver.add_table_with_content(TableType::RomRead, LookupWrapper::Dimensional3(rom_table));
    // add table of allowed delegation
    table_driver.add_table_with_content(
        TableType::SpecialCSRProperties,
        LookupWrapper::Dimensional3(csr_table.clone()),
    );

    let trace_len = NUM_PROC_CYCLES + 1;
    let csr_processor = DelegationsCSRProcessor;

    let for_gpu_comparison = maybe_delegator_gpu_comparison_hook.is_some()
        || maybe_delegated_gpu_comparison_hook.is_some();

    if !for_gpu_comparison {
        serialize_to_file(&compiled_machine, "full_machine_layout.json");
    }

    // compile all delegation circuit

    let mut delegation_circuits_eval_fns: HashMap<
        u32,
        fn(&mut SimpleWitnessProxy<'_, DelegationCircuitOracle<'_>>),
    > = HashMap::new();
    let mut delegation_circuits = vec![];
    {
        use cs::delegation::keccak_special5::define_keccak_special5_delegation_circuit;
        let mut cs = BasicAssembly::<Mersenne31Field>::new();
        define_keccak_special5_delegation_circuit::<_, _, false>(&mut cs);
        let (circuit_output, _) = cs.finalize();
        let table_driver = circuit_output.table_driver.clone();
        let compiler = OneRowCompiler::default();
        let circuit = compiler.compile_to_evaluate_delegations(
            circuit_output,
            delegation_domain_size.trailing_zeros() as usize,
        );

        if !for_gpu_comparison {
            serialize_to_file(&circuit, "keccak_delegation_circuit_layout.json");
        }

        let delegation_type = KECCAK_SPECIAL5_CSR_REGISTER;
        let description = DelegationProcessorDescription {
            delegation_type: KECCAK_SPECIAL5_CSR_REGISTER,
            num_requests_per_circuit: NUM_DELEGATION_CYCLES,
            trace_len: NUM_DELEGATION_CYCLES + 1,
            table_driver,
            compiled_circuit: circuit,
        };

        delegation_circuits.push((delegation_type, description));
        delegation_circuits_eval_fns.insert(
            delegation_type,
            super::keccak_special5_delegation_with_gpu_tracer::witness_eval_fn,
        );
    }

    // NO inputs: 0 fibs, 0 hash
    let non_determinism_responses = vec![];

    let (witness_chunks, register_final_values, delegation_circuits) =
        dev_run_all_and_make_witness_ext_with_gpu_tracers::<
            _,
            IMStandardIsaConfig,
            _,
            SECOND_WORD_BITS,
        >(
            machine,
            &compiled_machine,
            super::full_machine_with_gpu_tracer::witness_eval_fn,
            delegation_circuits_eval_fns,
            &delegation_circuits,
            &binary,
            NUM_PROC_CYCLES,
            trace_len,
            csr_processor,
            Some(LookupWrapper::Dimensional3(csr_table)),
            &non_determinism_responses,
            &worker,
        );

    assert_eq!(witness_chunks.len(), 1);

    let twiddles: Twiddles<_, Global> = Twiddles::new(NUM_PROC_CYCLES + 1, &worker);
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

    println!("Checking if satisfied");
    let is_satisfied = check_satisfied(
        &compiled_machine,
        &witness.exec_trace,
        witness.num_witness_columns,
    );
    assert!(is_satisfied);

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

    // // we can also evaluate constraint for debug purposes
    // {
    //     let compiled_constraints = CompiledConstraintsForDomain::from_compiled_circuit(
    //         &compiled_machine,
    //         Mersenne31Complex::ONE,
    //         trace_len as u32,
    //     );

    //     let now = std::time::Instant::now();
    //     let quotient_view = evaluate_constraints_on_domain(
    //         &witness.exec_trace,
    //         witness.num_witness_columns,
    //         &quad_terms_challenges,
    //         &linear_terms_challenges,
    //         &compiled_constraints,
    //         &worker,
    //     );
    //     dbg!(&now.elapsed());

    //     let mut quotient_row = quotient_view.row_view(0..NUM_PROC_CYCLES);
    //     for _ in 0..NUM_PROC_CYCLES {
    //         let as_field = unsafe {
    //             quotient_row
    //                 .current_row_ref()
    //                 .as_ptr()
    //                 .cast::<Mersenne31Quartic>()
    //                 .read()
    //         };
    //         assert_eq!(as_field, Mersenne31Quartic::ZERO);
    //         quotient_row.advance_row();
    //     }
    // }

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

    let delegation_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            delegation_argument_alpha,
            NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1,
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
            machine_state_permutation_argument: None,
        },
        aux_boundary_values: witness
            .aux_data
            .aux_boundary_data
            .get(0)
            .cloned()
            .unwrap_or_default(),
    };

    let mut public_inputs = witness.aux_data.first_row_public_inputs.clone();
    public_inputs.extend(witness.aux_data.one_before_last_row_public_inputs.clone());

    dbg!(&external_values);

    let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        Some(witness.lookup_mapping.clone())
    } else {
        None
    };

    let now = std::time::Instant::now();
    let (prover_data, proof) = prove::<DEFAULT_TRACE_PADDING_MULTIPLE, _>(
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

    if !for_gpu_comparison {
        serialize_to_file(&proof, "k_delegation_proof");
    }

    if let Some(ref gpu_comparison_hook) = maybe_delegator_gpu_comparison_hook {
        let log_n = (NUM_PROC_CYCLES + 1).trailing_zeros();
        assert_eq!(log_n, 20);
        let gpu_comparison_args = GpuComparisonArgs {
            circuit: &compiled_machine,
            setup: &setup,
            external_values: &external_values,
            public_inputs: &public_inputs,
            twiddles: &twiddles,
            lde_precomputations: &lde_precomputations,
            table_driver: &table_driver,
            lookup_mapping: lookup_mapping_for_gpu.unwrap(),
            log_n: log_n as usize,
            circuit_sequence: 0,
            delegation_processing_type: None,
            prover_data: &prover_data,
        };
        gpu_comparison_hook(&gpu_comparison_args);
    }

    let register_contribution_in_memory_argument =
        produce_register_contribution_into_memory_accumulator(
            &register_final_values,
            memory_argument_linearization_challenges_powers,
            memory_argument_gamma,
        );

    dbg!(&prover_data.stage_2_result.grand_product_accumulator);
    dbg!(&prover_data.stage_2_result.sum_over_delegation_poly);
    dbg!(register_contribution_in_memory_argument);

    let mut memory_accumulator = prover_data.stage_2_result.grand_product_accumulator;
    memory_accumulator.mul_assign(&register_contribution_in_memory_argument);

    let mut sum_over_delegation_poly = prover_data.stage_2_result.sum_over_delegation_poly;

    // now prove delegation circuits
    let mut external_values = external_values;
    external_values.aux_boundary_values = Default::default();
    for work_type in delegation_circuits.into_iter() {
        dbg!(work_type.delegation_type);
        dbg!(work_type.trace_len);
        dbg!(work_type.work_units.len());

        let delegation_type = work_type.delegation_type;
        // create setup
        let twiddles: Twiddles<_, Global> = Twiddles::new(work_type.trace_len, &worker);
        let lde_precomputations =
            LdePrecomputations::new(work_type.trace_len, lde_factor, &[0, 1], &worker);

        let setup = SetupPrecomputations::from_tables_and_trace_len(
            &work_type.table_driver,
            work_type.trace_len,
            &work_type.compiled_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        for witness in work_type.work_units.into_iter() {
            println!(
                "Checking if delegation type {} circuit is satisfied",
                delegation_type
            );
            let is_satisfied = check_satisfied(
                &work_type.compiled_circuit,
                &witness.witness.exec_trace,
                witness.witness.num_witness_columns,
            );
            assert!(is_satisfied);

            let lookup_mapping_for_gpu = if maybe_delegated_gpu_comparison_hook.is_some() {
                Some(witness.witness.lookup_mapping.clone())
            } else {
                None
            };

            dbg!(witness.witness.exec_trace.len());
            let now = std::time::Instant::now();
            let (prover_data, proof) = prove::<DEFAULT_TRACE_PADDING_MULTIPLE, _>(
                &work_type.compiled_circuit,
                &[],
                &external_values,
                witness.witness,
                &setup,
                &twiddles,
                &lde_precomputations,
                0,
                Some(delegation_type),
                lde_factor,
                tree_cap_size,
                53,
                28,
                &worker,
            );
            println!(
                "Delegation circuit type {} proving time is {:?}",
                delegation_type,
                now.elapsed()
            );

            if let Some(ref gpu_comparison_hook) = maybe_delegated_gpu_comparison_hook {
                let log_n = work_type.trace_len.trailing_zeros();
                assert_eq!(work_type.trace_len, 1 << log_n);
                let dummy_public_inputs = Vec::<Mersenne31Field>::new();
                let gpu_comparison_args = GpuComparisonArgs {
                    circuit: &work_type.compiled_circuit,
                    setup: &setup,
                    external_values: &external_values,
                    public_inputs: &dummy_public_inputs,
                    twiddles: &twiddles,
                    lde_precomputations: &lde_precomputations,
                    table_driver: &work_type.table_driver,
                    lookup_mapping: lookup_mapping_for_gpu.unwrap(),
                    log_n: log_n as usize,
                    circuit_sequence: 0,
                    delegation_processing_type: Some(delegation_type),
                    prover_data: &prover_data,
                };
                gpu_comparison_hook(&gpu_comparison_args);
            }

            if !for_gpu_comparison {
                serialize_to_file(&proof, "keccak_delegator_proof");
            }

            dbg!(prover_data.stage_2_result.grand_product_accumulator);
            dbg!(prover_data.stage_2_result.sum_over_delegation_poly);

            memory_accumulator.mul_assign(&prover_data.stage_2_result.grand_product_accumulator);
            sum_over_delegation_poly
                .sub_assign(&prover_data.stage_2_result.sum_over_delegation_poly);
        }
    }

    assert_eq!(memory_accumulator, Mersenne31Quartic::ONE);
    assert_eq!(sum_over_delegation_poly, Mersenne31Quartic::ZERO);
}

// use --features debug_satisfiable ?
#[test]
fn run_keccak_test() {
    run_keccak_test_impl(None, None);
}

#[cfg_attr(
    not(feature = "debug_satisfiable"),
    ignore = "Running prover test without the 'debug_satisfiable' feature; run cargo test --features debug_satisfiable for the full test"
)]
#[test]
fn run_keccak_test_info() {}

#[allow(unused)]
const APP_KECCAK_SIMPLE_BIN: &[u8] = include_bytes!("../../app_keccak_simple.bin");

// #[allow(unused)]
// const APP_KECCAK_BAD_BIN: &[u8] = include_bytes!("../../app_keccak_bad.bin"); // SHOULD FAIL

// #[allow(unused)]
// const APP_KECCAK_BENCH_BIN: &[u8] = include_bytes!("../../app_keccak_bench.bin");

// expects state ptr to be in x10
#[allow(unused)]
#[deprecated = "this is using an old version of the keccak ABI"]
const KECCAK_F1600_BIN: &[u32] = &[
    0x00200537, // init: loads 1<<21 in x10
    329107, 2164023, 1049628787, 4261175, 1049628787, 8455479, 1049628787, 16844087, 1049628787,
    33621303, 1049628787, 2229559, 1049628787, 2360631, 1049628787, 4457783, 1049628787, 8652087,
    1049628787, 17040695, 1049628787, 33817911, 1049628787, 2622775, 1049628787, 3147063,
    1049628787, 4719927, 1049628787, 5244215, 1049628787, 8914231, 1049628787, 9438519, 1049628787,
    17302839, 1049628787, 17827127, 1049628787, 34080055, 1049628787, 34604343, 1049628787,
    69272887, 1049628787, 71370039, 1049628787, 75564343, 1049628787, 83952951, 1049628787,
    100730167, 1049628787, 69338423, 1049628787, 69469495, 1049628787, 71566647, 1049628787,
    75760951, 1049628787, 84149559, 1049628787, 100926775, 1049628787, 69731639, 1049628787,
    70255927, 1049628787, 71828791, 1049628787, 72353079, 1049628787, 76023095, 1049628787,
    76547383, 1049628787, 84411703, 1049628787, 84935991, 1049628787, 101188919, 1049628787,
    101713207, 1049628787, 136381751, 1049628787, 138478903, 1049628787, 142673207, 1049628787,
    151061815, 1049628787, 167839031, 1049628787, 136447287, 1049628787, 136578359, 1049628787,
    138675511, 1049628787, 142869815, 1049628787, 151258423, 1049628787, 168035639, 1049628787,
    136840503, 1049628787, 137364791, 1049628787, 138937655, 1049628787, 139461943, 1049628787,
    143131959, 1049628787, 143656247, 1049628787, 151520567, 1049628787, 152044855, 1049628787,
    168297783, 1049628787, 168822071, 1049628787, 203490615, 1049628787, 205587767, 1049628787,
    209782071, 1049628787, 218170679, 1049628787, 234947895, 1049628787, 203556151, 1049628787,
    203687223, 1049628787, 205784375, 1049628787, 209978679, 1049628787, 218367287, 1049628787,
    235144503, 1049628787, 203949367, 1049628787, 204473655, 1049628787, 206046519, 1049628787,
    206570807, 1049628787, 210240823, 1049628787, 210765111, 1049628787, 218629431, 1049628787,
    219153719, 1049628787, 235406647, 1049628787, 235930935, 1049628787, 270599479, 1049628787,
    272696631, 1049628787, 276890935, 1049628787, 285279543, 1049628787, 302056759, 1049628787,
    270665015, 1049628787, 270796087, 1049628787, 272893239, 1049628787, 277087543, 1049628787,
    285476151, 1049628787, 302253367, 1049628787, 271058231, 1049628787, 271582519, 1049628787,
    273155383, 1049628787, 273679671, 1049628787, 277349687, 1049628787, 277873975, 1049628787,
    285738295, 1049628787, 286262583, 1049628787, 302515511, 1049628787, 303039799, 1049628787,
    337708343, 1049628787, 339805495, 1049628787, 343999799, 1049628787, 352388407, 1049628787,
    369165623, 1049628787, 337773879, 1049628787, 337904951, 1049628787, 340002103, 1049628787,
    344196407, 1049628787, 352585015, 1049628787, 369362231, 1049628787, 338167095, 1049628787,
    338691383, 1049628787, 340264247, 1049628787, 340788535, 1049628787, 344458551, 1049628787,
    344982839, 1049628787, 352847159, 1049628787, 353371447, 1049628787, 369624375, 1049628787,
    370148663, 1049628787, 404817207, 1049628787, 406914359, 1049628787, 411108663, 1049628787,
    419497271, 1049628787, 436274487, 1049628787, 404882743, 1049628787, 405013815, 1049628787,
    407110967, 1049628787, 411305271, 1049628787, 419693879, 1049628787, 436471095, 1049628787,
    405275959, 1049628787, 405800247, 1049628787, 407373111, 1049628787, 407897399, 1049628787,
    411567415, 1049628787, 412091703, 1049628787, 419956023, 1049628787, 420480311, 1049628787,
    436733239, 1049628787, 437257527, 1049628787, 471926071, 1049628787, 474023223, 1049628787,
    478217527, 1049628787, 486606135, 1049628787, 503383351, 1049628787, 471991607, 1049628787,
    472122679, 1049628787, 474219831, 1049628787, 478414135, 1049628787, 486802743, 1049628787,
    503579959, 1049628787, 472384823, 1049628787, 472909111, 1049628787, 474481975, 1049628787,
    475006263, 1049628787, 478676279, 1049628787, 479200567, 1049628787, 487064887, 1049628787,
    487589175, 1049628787, 503842103, 1049628787, 504366391, 1049628787, 539034935, 1049628787,
    541132087, 1049628787, 545326391, 1049628787, 553714999, 1049628787, 570492215, 1049628787,
    539100471, 1049628787, 539231543, 1049628787, 541328695, 1049628787, 545522999, 1049628787,
    553911607, 1049628787, 570688823, 1049628787, 539493687, 1049628787, 540017975, 1049628787,
    541590839, 1049628787, 542115127, 1049628787, 545785143, 1049628787, 546309431, 1049628787,
    554173751, 1049628787, 554698039, 1049628787, 570950967, 1049628787, 571475255, 1049628787,
    606143799, 1049628787, 608240951, 1049628787, 612435255, 1049628787, 620823863, 1049628787,
    637601079, 1049628787, 606209335, 1049628787, 606340407, 1049628787, 608437559, 1049628787,
    612631863, 1049628787, 621020471, 1049628787, 637797687, 1049628787, 606602551, 1049628787,
    607126839, 1049628787, 608699703, 1049628787, 609223991, 1049628787, 612894007, 1049628787,
    613418295, 1049628787, 621282615, 1049628787, 621806903, 1049628787, 638059831, 1049628787,
    638584119, 1049628787, 673252663, 1049628787, 675349815, 1049628787, 679544119, 1049628787,
    687932727, 1049628787, 704709943, 1049628787, 673318199, 1049628787, 673449271, 1049628787,
    675546423, 1049628787, 679740727, 1049628787, 688129335, 1049628787, 704906551, 1049628787,
    673711415, 1049628787, 674235703, 1049628787, 675808567, 1049628787, 676332855, 1049628787,
    680002871, 1049628787, 680527159, 1049628787, 688391479, 1049628787, 688915767, 1049628787,
    705168695, 1049628787, 705692983, 1049628787, 740361527, 1049628787, 742458679, 1049628787,
    746652983, 1049628787, 755041591, 1049628787, 771818807, 1049628787, 740427063, 1049628787,
    740558135, 1049628787, 742655287, 1049628787, 746849591, 1049628787, 755238199, 1049628787,
    772015415, 1049628787, 740820279, 1049628787, 741344567, 1049628787, 742917431, 1049628787,
    743441719, 1049628787, 747111735, 1049628787, 747636023, 1049628787, 755500343, 1049628787,
    756024631, 1049628787, 772277559, 1049628787, 772801847, 1049628787, 807470391, 1049628787,
    809567543, 1049628787, 813761847, 1049628787, 822150455, 1049628787, 838927671, 1049628787,
    807535927, 1049628787, 807666999, 1049628787, 809764151, 1049628787, 813958455, 1049628787,
    822347063, 1049628787, 839124279, 1049628787, 807929143, 1049628787, 808453431, 1049628787,
    810026295, 1049628787, 810550583, 1049628787, 814220599, 1049628787, 814744887, 1049628787,
    822609207, 1049628787, 823133495, 1049628787, 839386423, 1049628787, 839910711, 1049628787,
    874579255, 1049628787, 876676407, 1049628787, 880870711, 1049628787, 889259319, 1049628787,
    906036535, 1049628787, 874644791, 1049628787, 874775863, 1049628787, 876873015, 1049628787,
    881067319, 1049628787, 889455927, 1049628787, 906233143, 1049628787, 875038007, 1049628787,
    875562295, 1049628787, 877135159, 1049628787, 877659447, 1049628787, 881329463, 1049628787,
    881853751, 1049628787, 889718071, 1049628787, 890242359, 1049628787, 906495287, 1049628787,
    907019575, 1049628787, 941688119, 1049628787, 943785271, 1049628787, 947979575, 1049628787,
    956368183, 1049628787, 973145399, 1049628787, 941753655, 1049628787, 941884727, 1049628787,
    943981879, 1049628787, 948176183, 1049628787, 956564791, 1049628787, 973342007, 1049628787,
    942146871, 1049628787, 942671159, 1049628787, 944244023, 1049628787, 944768311, 1049628787,
    948438327, 1049628787, 948962615, 1049628787, 956826935, 1049628787, 957351223, 1049628787,
    973604151, 1049628787, 974128439, 1049628787, 1008796983, 1049628787, 1010894135, 1049628787,
    1015088439, 1049628787, 1023477047, 1049628787, 1040254263, 1049628787, 1008862519, 1049628787,
    1008993591, 1049628787, 1011090743, 1049628787, 1015285047, 1049628787, 1023673655, 1049628787,
    1040450871, 1049628787, 1009255735, 1049628787, 1009780023, 1049628787, 1011352887, 1049628787,
    1011877175, 1049628787, 1015547191, 1049628787, 1016071479, 1049628787, 1023935799, 1049628787,
    1024460087, 1049628787, 1040713015, 1049628787, 1041237303, 1049628787, 1075905847, 1049628787,
    1078002999, 1049628787, 1082197303, 1049628787, 1090585911, 1049628787, 1107363127, 1049628787,
    1075971383, 1049628787, 1076102455, 1049628787, 1078199607, 1049628787, 1082393911, 1049628787,
    1090782519, 1049628787, 1107559735, 1049628787, 1076364599, 1049628787, 1076888887, 1049628787,
    1078461751, 1049628787, 1078986039, 1049628787, 1082656055, 1049628787, 1083180343, 1049628787,
    1091044663, 1049628787, 1091568951, 1049628787, 1107821879, 1049628787, 1108346167, 1049628787,
    1143014711, 1049628787, 1145111863, 1049628787, 1149306167, 1049628787, 1157694775, 1049628787,
    1174471991, 1049628787, 1143080247, 1049628787, 1143211319, 1049628787, 1145308471, 1049628787,
    1149502775, 1049628787, 1157891383, 1049628787, 1174668599, 1049628787, 1143473463, 1049628787,
    1143997751, 1049628787, 1145570615, 1049628787, 1146094903, 1049628787, 1149764919, 1049628787,
    1150289207, 1049628787, 1158153527, 1049628787, 1158677815, 1049628787, 1174930743, 1049628787,
    1175455031, 1049628787, 1210123575, 1049628787, 1212220727, 1049628787, 1216415031, 1049628787,
    1224803639, 1049628787, 1241580855, 1049628787, 1210189111, 1049628787, 1210320183, 1049628787,
    1212417335, 1049628787, 1216611639, 1049628787, 1225000247, 1049628787, 1241777463, 1049628787,
    1210582327, 1049628787, 1211106615, 1049628787, 1212679479, 1049628787, 1213203767, 1049628787,
    1216873783, 1049628787, 1217398071, 1049628787, 1225262391, 1049628787, 1225786679, 1049628787,
    1242039607, 1049628787, 1242563895, 1049628787, 1277232439, 1049628787, 1279329591, 1049628787,
    1283523895, 1049628787, 1291912503, 1049628787, 1308689719, 1049628787, 1277297975, 1049628787,
    1277429047, 1049628787, 1279526199, 1049628787, 1283720503, 1049628787, 1292109111, 1049628787,
    1308886327, 1049628787, 1277691191, 1049628787, 1278215479, 1049628787, 1279788343, 1049628787,
    1280312631, 1049628787, 1283982647, 1049628787, 1284506935, 1049628787, 1292371255, 1049628787,
    1292895543, 1049628787, 1309148471, 1049628787, 1309672759, 1049628787, 1344341303, 1049628787,
    1346438455, 1049628787, 1350632759, 1049628787, 1359021367, 1049628787, 1375798583, 1049628787,
    1344406839, 1049628787, 1344537911, 1049628787, 1346635063, 1049628787, 1350829367, 1049628787,
    1359217975, 1049628787, 1375995191, 1049628787, 1344800055, 1049628787, 1345324343, 1049628787,
    1346897207, 1049628787, 1347421495, 1049628787, 1351091511, 1049628787, 1351615799, 1049628787,
    1359480119, 1049628787, 1360004407, 1049628787, 1376257335, 1049628787, 1376781623, 1049628787,
    1411450167, 1049628787, 1413547319, 1049628787, 1417741623, 1049628787, 1426130231, 1049628787,
    1442907447, 1049628787, 1411515703, 1049628787, 1411646775, 1049628787, 1413743927, 1049628787,
    1417938231, 1049628787, 1426326839, 1049628787, 1443104055, 1049628787, 1411908919, 1049628787,
    1412433207, 1049628787, 1414006071, 1049628787, 1414530359, 1049628787, 1418200375, 1049628787,
    1418724663, 1049628787, 1426588983, 1049628787, 1427113271, 1049628787, 1443366199, 1049628787,
    1443890487, 1049628787, 1478559031, 1049628787, 1480656183, 1049628787, 1484850487, 1049628787,
    1493239095, 1049628787, 1510016311, 1049628787, 1478624567, 1049628787, 1478755639, 1049628787,
    1480852791, 1049628787, 1485047095, 1049628787, 1493435703, 1049628787, 1510212919, 1049628787,
    1479017783, 1049628787, 1479542071, 1049628787, 1481114935, 1049628787, 1481639223, 1049628787,
    1485309239, 1049628787, 1485833527, 1049628787, 1493697847, 1049628787, 1494222135, 1049628787,
    1510475063, 1049628787, 1510999351, 1049628787, 1545667895, 1049628787, 1547765047, 1049628787,
    1551959351, 1049628787, 1560347959, 1049628787, 1577125175, 1049628787, 1545733431, 1049628787,
    1545864503, 1049628787, 1547961655, 1049628787, 1552155959, 1049628787, 1560544567, 1049628787,
    1577321783, 1049628787, 1546126647, 1049628787, 1546650935, 1049628787, 1548223799, 1049628787,
    1548748087, 1049628787, 1552418103, 1049628787, 1552942391, 1049628787, 1560806711, 1049628787,
    1561330999, 1049628787, 1577583927, 1049628787, 1578108215, 1049628787, 4564227, 370179,
    2147485367, 13976883, 2147518135, 8816275, 14042675, 12951587, 10854947,
    0x0000006f, // fin: infinite loop to avoid padding with tons of noop
];
