use crate::bincode_serialize_to_file;
use crate::cs::cs::oracle::ExecutorFamilyDecoderData;
use crate::cs::machine::ops::unrolled::*;
use crate::u32_from_field_elems;
use crate::NonDeterminismCSRSource;
use crate::DUMP_WITNESS_VAR;
use common_constants::TimestampScalar;
use common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
use common_constants::INITIAL_TIMESTAMP;
use common_constants::TIMESTAMP_STEP;
use prover::check_satisfied;
use prover::cs::utils::split_timestamp;
use prover::definitions::*;
use prover::fft::*;
use prover::field::*;
use prover::merkle_trees::DefaultTreeConstructor;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::prover_stages::Proof;
use prover::risc_v_simulator;
use prover::tracers::delegation::DelegationWitness;
use prover::tracers::oracles::delegation_oracle::DelegationCircuitOracle;
use prover::tracers::oracles::transpiler_oracles::delegation::DelegationOracle;
use prover::tracers::unrolled::tracer::MemTracingFamilyChunk;
use prover::tracers::unrolled::tracer::NonMemTracingFamilyChunk;
use prover::unrolled::evaluate_init_and_teardown_witness;
use prover::unrolled::MemoryCircuitOracle;
use prover::unrolled::NonMemoryCircuitOracle;
use prover::witness_evaluator::unrolled::run_unrolled_machine_for_num_cycles_with_word_memory_ops_specialization;
use prover::worker;
use prover::ExecutorFamilyWitnessEvaluationAuxData;
use prover::ShuffleRamSetupAndTeardown;
use prover::VectorMemoryImplWithRom;
use prover::WitnessEvaluationData;
use prover::WitnessEvaluationDataForExecutionFamily;
use prover::DEFAULT_TRACE_PADDING_MULTIPLE;
use risc_v_simulator::cycle::IMStandardIsaConfig;
use risc_v_simulator::cycle::IMStandardIsaConfigWithUnsignedMulDiv;
use risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation;
use risc_v_simulator::cycle::MachineConfig;
use risc_v_simulator::delegations::DelegationsCSRProcessor;
use risc_v_simulator::machine_mode_only_unrolled::DelegationCSRProcessor;
use riscv_transpiler::witness::delegation::bigint::BigintAbiDescription;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionAbiDescription;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5AbiDescription;
use riscv_transpiler::witness::DelegationAbiDescription;
use setups::inits_and_teardowns;
use setups::DelegationCircuitPrecomputations;
use setups::UnrolledCircuitPrecomputations;
use setups::UnrolledCircuitWitnessEvalFn;
use std::alloc::Global;
use std::collections::BTreeMap;
use std::collections::HashMap;
use trace_and_split::commit_memory_tree_for_delegation_circuit_with_gpu_tracer;
use trace_and_split::commit_memory_tree_for_delegation_circuit_with_replayer_format;
use trace_and_split::commit_memory_tree_for_inits_and_teardowns_unrolled_circuit;
use trace_and_split::commit_memory_tree_for_unrolled_mem_circuits;
use trace_and_split::commit_memory_tree_for_unrolled_nonmem_circuits;
use trace_and_split::fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits;
use trace_and_split::FinalRegisterValue;
use trace_and_split::ENTRY_POINT;

pub fn preprocess_text_section_for_machine_config<
    C: MachineConfig,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
    A: GoodAllocator,
>(
    text_section: &[u32],
) -> HashMap<
    u8,
    (
        Vec<Option<DecoderTableEntry<Mersenne31Field>>, A>,
        Vec<ExecutorFamilyDecoderData, A>,
    ),
> {
    let rom_size_in_words: usize = 1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS - 2);
    if setups::is_default_machine_configuration::<C>() {
        process_binary_into_separate_tables_ext::<Mersenne31Field, true, A>(
            &text_section,
            &opcodes_for_full_machine_with_mem_word_access_specialization(),
            rom_size_in_words,
            setups::shift_binary_csr::ALLOWED_DELEGATION_CSRS_U16,
        )
    } else if setups::is_machine_without_signed_mul_div_configuration::<C>() {
        process_binary_into_separate_tables_ext::<Mersenne31Field, true, A>(
            &text_section,
            &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
            rom_size_in_words,
            setups::shift_binary_csr::ALLOWED_DELEGATION_CSRS_U16,
        )
    } else if setups::is_reduced_machine_configuration::<C>() {
        process_binary_into_separate_tables_ext::<Mersenne31Field, true, A>(
            &text_section,
            &opcodes_for_reduced_machine(),
            rom_size_in_words,
            setups::shift_binary_csr::ALLOWED_DELEGATION_CSRS_U16,
        )
    } else {
        panic!("Unknown configuration {:?}", std::any::type_name::<C>());
    }
}

pub fn run_and_split_unrolled<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig,
    A: GoodAllocator,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    non_determinism: &mut ND,
    non_mem_factories: HashMap<
        u8,
        Box<dyn Fn() -> NonMemTracingFamilyChunk<A> + Send + Sync + 'static>,
    >,
    mut mem_factories: HashMap<
        u8,
        Box<dyn Fn() -> MemTracingFamilyChunk<A> + Send + Sync + 'static>,
    >,
    delegation_factories: HashMap<
        u16,
        Box<dyn Fn() -> DelegationWitness<A> + Send + Sync + 'static>,
    >,
    ram_bound: usize,
    worker: &worker::Worker,
) -> (
    u32,
    TimestampScalar,
    usize,
    BTreeMap<u8, Vec<NonMemTracingFamilyChunk<A>>>,
    (Vec<MemTracingFamilyChunk<A>>, Vec<MemTracingFamilyChunk<A>>),
    BTreeMap<u16, Vec<DelegationWitness<A>>>,
    [FinalRegisterValue; 32],
    Vec<ShuffleRamSetupAndTeardown<A>>,
) {
    let rom_address_space_bound: usize = 1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS);
    assert!(ram_bound > rom_address_space_bound);
    let mut memory = VectorMemoryImplWithRom::new_for_byte_size(ram_bound, rom_address_space_bound);
    for (idx, insn) in binary_image.iter().enumerate() {
        memory.populate(ENTRY_POINT + idx as u32 * 4, *insn);
    }

    let csr_processor = DelegationsCSRProcessor;

    let (
        final_pc,
        final_timestamp,
        cycles_used,
        family_circuits,
        (word_mem_circuits, subword_mem_circuits),
        delegation_circuits,
        register_final_state,
        shuffle_ram_touched_addresses,
    ) = if setups::is_default_machine_configuration::<C>() {
        let word_mem_factory = mem_factories
            .remove(&common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX)
            .expect("must exist");
        let subword_mem_factory = mem_factories
            .remove(&common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX)
            .expect("must exist");
        run_unrolled_machine_for_num_cycles_with_word_memory_ops_specialization::<
            _,
            IMStandardIsaConfigWithUnsignedMulDiv,
            A,
        >(
            cycles_bound,
            ENTRY_POINT,
            csr_processor,
            &mut memory,
            rom_address_space_bound,
            non_determinism,
            non_mem_factories,
            word_mem_factory,
            subword_mem_factory,
            delegation_factories,
            ram_bound,
            &worker,
        )
    } else if setups::is_machine_without_signed_mul_div_configuration::<C>() {
        let word_mem_factory = mem_factories
            .remove(&common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX)
            .expect("must exist");
        let subword_mem_factory = mem_factories
            .remove(&common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX)
            .expect("must exist");
        run_unrolled_machine_for_num_cycles_with_word_memory_ops_specialization::<
            _,
            IMStandardIsaConfigWithUnsignedMulDiv,
            A,
        >(
            cycles_bound,
            ENTRY_POINT,
            csr_processor,
            &mut memory,
            rom_address_space_bound,
            non_determinism,
            non_mem_factories,
            word_mem_factory,
            subword_mem_factory,
            delegation_factories,
            ram_bound,
            &worker,
        )
    } else if setups::is_reduced_machine_configuration::<C>() {
        let word_mem_factory = mem_factories
            .remove(&common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX)
            .expect("must exist");
        let (_, subword_mem_factory) = setups::load_store_subword_only::get_tracer_factory(); // NOT used internally
        run_unrolled_machine_for_num_cycles_with_word_memory_ops_specialization::<
            _,
            IWithoutByteAccessIsaConfigWithDelegation,
            A,
        >(
            cycles_bound,
            ENTRY_POINT,
            csr_processor,
            &mut memory,
            rom_address_space_bound,
            non_determinism,
            non_mem_factories,
            word_mem_factory,
            subword_mem_factory,
            delegation_factories,
            ram_bound,
            &worker,
        )
    } else {
        panic!("Unknown configuration {:?}", std::any::type_name::<C>());
    };

    assert_eq!(
        (cycles_used as u64) * TIMESTAMP_STEP + INITIAL_TIMESTAMP,
        final_timestamp
    );

    let num_inits_per_circuit = setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS
        * (setups::inits_and_teardowns::DOMAIN_SIZE - 1);

    let total_input_len: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();
    let num_needed_chunks =
        total_input_len.next_multiple_of(num_inits_per_circuit) / num_inits_per_circuit;

    use crate::tracers::oracles::chunk_lazy_init_and_teardown;

    let (num_trivial, inits_and_teardowns) = chunk_lazy_init_and_teardown::<A, _>(
        num_needed_chunks,
        num_inits_per_circuit,
        &shuffle_ram_touched_addresses,
        &worker,
    );
    assert_eq!(num_trivial, 0);

    (
        final_pc,
        final_timestamp,
        cycles_used,
        BTreeMap::from_iter(family_circuits.into_iter()),
        (word_mem_circuits, subword_mem_circuits),
        BTreeMap::from_iter(delegation_circuits.into_iter()),
        register_final_state.map(|el| FinalRegisterValue {
            value: el.current_value,
            last_access_timestamp: el.last_access_timestamp,
        }),
        inits_and_teardowns,
    )
}

pub fn trace_unrolled_execution<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig,
    A: GoodAllocator,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    mut non_determinism: ND,
    ram_bound: usize,
    worker: &worker::Worker,
) -> (
    u32,
    TimestampScalar,
    usize,
    BTreeMap<u8, Vec<NonMemTracingFamilyChunk<A>>>,
    (Vec<MemTracingFamilyChunk<A>>, Vec<MemTracingFamilyChunk<A>>),
    BTreeMap<u16, Vec<DelegationWitness<A>>>,
    [FinalRegisterValue; 32],
    Vec<ShuffleRamSetupAndTeardown<A>>,
) {
    let (non_mem_factories, mem_factories) = if setups::is_default_machine_configuration::<C>() {
        setups::factories_for_unrolled_circuits_base_layer::<A>()
    } else if setups::is_machine_without_signed_mul_div_configuration::<C>() {
        setups::factories_for_unrolled_circuits_base_layer_unsigned_only::<A>()
    } else if setups::is_reduced_machine_configuration::<C>() {
        setups::factories_for_unrolled_circuits_recursion_layer::<A>()
    } else {
        panic!("Unknown configuration {:?}", std::any::type_name::<C>());
    };

    let delegation_factories = setups::delegation_factories_for_machine::<C, A>();

    let (
        final_pc,
        final_timestamp,
        cycles_used,
        family_circuits,
        (word_mem_circuits, subword_mem_circuits),
        delegation_circuits,
        register_final_state,
        inits_and_teardowns,
    ) = run_and_split_unrolled::<ND, C, A, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(
        cycles_bound,
        binary_image,
        text_section,
        &mut non_determinism,
        non_mem_factories,
        mem_factories,
        delegation_factories,
        ram_bound,
        worker,
    );

    println!(
        "Program finished execution with final pc = 0x{:08x} and final register state\n{}",
        final_pc,
        register_final_state
            .iter()
            .enumerate()
            .map(|(idx, r)| format!("x{} = {}", idx, r.value))
            .collect::<Vec<_>>()
            .join(", ")
    );

    (
        final_pc,
        final_timestamp,
        cycles_used,
        family_circuits,
        (word_mem_circuits, subword_mem_circuits),
        delegation_circuits,
        register_final_state,
        inits_and_teardowns,
    )
}

pub fn prove_unrolled_execution<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig,
    A: GoodAllocator,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    non_determinism: ND,
    unrolled_circuits_precomputations: &BTreeMap<u8, UnrolledCircuitPrecomputations<A, A>>,
    inits_and_teardowns_precomputation: &UnrolledCircuitPrecomputations<A, A>,
    delegation_circuits_precomputations: &[(u32, DelegationCircuitPrecomputations<A, A>)],
    ram_bound: usize,
    worker: &worker::Worker,
) -> (
    BTreeMap<u8, Vec<UnrolledModeProof>>,
    Vec<UnrolledModeProof>,
    Vec<(u32, Vec<Proof>)>,
    [FinalRegisterValue; 32],
    (u32, TimestampScalar),
) {
    let (
        final_pc,
        final_timestamp,
        cycles_used,
        family_circuits,
        (word_mem_circuits, subword_mem_circuits),
        delegation_circuits,
        register_final_state,
        inits_and_teardowns,
    ) = trace_unrolled_execution::<ND, C, A, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(
        cycles_bound,
        binary_image,
        text_section,
        non_determinism,
        ram_bound,
        worker,
    );

    let should_dump_witness = std::env::var(DUMP_WITNESS_VAR)
        .map(|el| el.parse::<u32>().unwrap_or(0) == 1)
        .unwrap_or(false);

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    let mut memory_trees = vec![];

    // let decoder_preprocessing = preprocess_text_section_for_machine_config::<C, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(text_section);

    // commit memory trees
    for (family_idx, witness_chunks) in family_circuits.iter() {
        if witness_chunks.is_empty() {
            continue;
        }

        let mut family_caps = vec![];
        let precomputation = &unrolled_circuits_precomputations[family_idx];
        let UnrolledCircuitWitnessEvalFn::NonMemory {
            decoder_table,
            default_pc_value_in_padding,
            ..
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for chunk in witness_chunks.iter() {
            let caps = commit_memory_tree_for_unrolled_nonmem_circuits(
                &precomputation.compiled_circuit,
                &chunk.data,
                &precomputation.twiddles,
                &precomputation.lde_precomputations,
                *default_pc_value_in_padding,
                decoder_table,
                worker,
            );

            family_caps.push(caps);
        }
        memory_trees.push((*family_idx as u32, family_caps));
    }

    let mem_circuits = [
        (
            common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX,
            word_mem_circuits,
        ),
        (
            common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
            subword_mem_circuits,
        ),
    ];
    for (family_idx, witness_chunks) in mem_circuits.iter() {
        if witness_chunks.is_empty() {
            continue;
        }

        let mut family_caps = vec![];
        let precomputation = &unrolled_circuits_precomputations[family_idx];
        let UnrolledCircuitWitnessEvalFn::Memory { decoder_table, .. } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for chunk in witness_chunks.iter() {
            let caps = commit_memory_tree_for_unrolled_mem_circuits(
                &precomputation.compiled_circuit,
                &chunk.data,
                &precomputation.twiddles,
                &precomputation.lde_precomputations,
                decoder_table,
                worker,
            );

            family_caps.push(caps);
        }
        memory_trees.push((*family_idx as u32, family_caps));
    }

    // and inits and teardowns
    let mut inits_and_teardown_trees = vec![];
    let mut previous_aux: Option<AuxArgumentsBoundaryValues> = None;
    for witness_chunk in inits_and_teardowns.iter() {
        let (caps, aux_data) = commit_memory_tree_for_inits_and_teardowns_unrolled_circuit(
            &inits_and_teardowns_precomputation.compiled_circuit,
            &witness_chunk.lazy_init_data,
            &inits_and_teardowns_precomputation.twiddles,
            &inits_and_teardowns_precomputation.lde_precomputations,
            worker,
        );

        inits_and_teardown_trees.push(caps);

        for aux_data in aux_data.aux_boundary_data.iter() {
            if let Some(previous_aux) = previous_aux.take() {
                let previous_aux = &previous_aux;
                let this = u32_from_field_elems(&aux_data.lazy_init_first_row);
                let previous = u32_from_field_elems(&previous_aux.lazy_init_one_before_last_row);
                if this > previous {
                    // normal ascending comparison
                } else {
                    // we expect zero prepadding, and zero teardown data
                    assert_eq!(this, previous);
                    assert_eq!(previous, 0);
                    assert_eq!(
                        u32_from_field_elems(&previous_aux.teardown_value_one_before_last_row),
                        0
                    );
                    assert_eq!(
                        u32_from_field_elems(&previous_aux.teardown_timestamp_one_before_last_row),
                        0
                    );
                }
            }
            previous_aux = Some(*aux_data);
        }
    }

    // #[cfg(feature = "timing_logs")]
    // println!(
    //     "=== Commitment for {} RISC-V circuits memory trees took {:?}",
    //     main_circuits_witness.len(),
    //     now.elapsed()
    // );

    // same for delegation circuits
    let now = std::time::Instant::now();
    let mut delegation_memory_trees = vec![];

    for (delegation_type, els) in delegation_circuits.iter() {
        if els.is_empty() {
            continue;
        }
        let idx = delegation_circuits_precomputations
            .iter()
            .position(|el| el.0 == *delegation_type as u32)
            .unwrap();
        let prec = &delegation_circuits_precomputations[idx].1;
        let mut per_tree_set = vec![];
        for el in els.iter() {
            let (caps, delegation_t) = commit_memory_tree_for_delegation_circuit_with_gpu_tracer(
                &prec.compiled_circuit.compiled_circuit,
                el,
                &prec.twiddles,
                &prec.lde_precomputations,
                prec.lde_factor,
                prec.tree_cap_size,
                worker,
            );
            assert_eq!(*delegation_type as u32, delegation_t);
            per_tree_set.push(caps);
        }

        delegation_memory_trees.push((*delegation_type as u32, per_tree_set));
    }
    // #[cfg(feature = "timing_logs")]
    // println!(
    //     "=== Commitment for {} delegation circuits memory trees took {:?}",
    //     delegation_circuits_witness.len(),
    //     now.elapsed()
    // );

    #[cfg(feature = "debug_logs")]
    println!("Will create FS transformation challenge for memory and delegation arguments");

    // commit memory challenges
    let all_challenges_seed =
        fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits(
            &register_final_state,
            final_pc,
            final_timestamp,
            &memory_trees,
            &inits_and_teardown_trees,
            &delegation_memory_trees,
        );

    #[cfg(feature = "debug_logs")]
    println!("FS transformation memory seed is {:?}", all_challenges_seed);

    let external_challenges =
        ExternalChallenges::draw_from_transcript_seed_with_state_permutation(all_challenges_seed);

    #[cfg(feature = "debug_logs")]
    println!("External challenges = {:?}", external_challenges);

    let input = register_final_state
        .iter()
        .map(|el| (el.value, split_timestamp(el.last_access_timestamp)))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let mut permutation_argument_grand_product =
        produce_register_contribution_into_memory_accumulator_raw(
            &input,
            external_challenges
                .memory_argument
                .memory_argument_linearization_challenges,
            external_challenges.memory_argument.memory_argument_gamma,
        );
    let pc_permutation_contribution = produce_pc_into_permutation_accumulator_raw(
        ENTRY_POINT,
        split_timestamp(INITIAL_TIMESTAMP),
        final_pc,
        split_timestamp(final_timestamp),
        &external_challenges
            .machine_state_permutation_argument
            .unwrap()
            .linearization_challenges,
        &external_challenges
            .machine_state_permutation_argument
            .unwrap()
            .additive_term,
    );
    permutation_argument_grand_product.mul_assign(&pc_permutation_contribution);
    let mut delegation_argument_sum = Mersenne31Quartic::ZERO;

    let mut aux_memory_trees = vec![];

    // println!(
    //     "Producing proofs for main RISC-V circuit, {} proofs in total",
    //     main_circuits_witness.len()
    // );

    let total_proving_start = std::time::Instant::now();

    // now prove one by one
    let mut main_proofs = BTreeMap::new();
    for (family_idx, witness_chunks) in family_circuits.into_iter() {
        if witness_chunks.is_empty() {
            continue;
        }

        if should_dump_witness {
            // TODO
        }

        let mut family_caps = vec![];
        let mut family_proofs = vec![];

        let precomputation = &unrolled_circuits_precomputations[&family_idx];
        let UnrolledCircuitWitnessEvalFn::NonMemory {
            decoder_table,
            default_pc_value_in_padding,
            witness_fn,
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for chunk in witness_chunks.into_iter() {
            let oracle = NonMemoryCircuitOracle {
                inner: &chunk.data,
                decoder_table,
                default_pc_value_in_padding: *default_pc_value_in_padding,
            };

            let now = std::time::Instant::now();
            let witness_trace = prover::unrolled::evaluate_witness_for_executor_family::<_, A>(
                &precomputation.compiled_circuit,
                *witness_fn,
                precomputation.trace_len - 1,
                &oracle,
                &precomputation.table_driver,
                &worker,
                A::default(),
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Witness generation for unrolled circuit type {} took {:?}",
                family_idx,
                now.elapsed()
            );

            if crate::PRECHECK_SATISFIED {
                println!("Will evaluate basic satisfiability checks for main circuit");

                assert!(check_satisfied(
                    &precomputation.compiled_circuit,
                    &witness_trace.exec_trace,
                    witness_trace.num_witness_columns
                ));
            }

            let now = std::time::Instant::now();
            let (prover_data, proof) =
                prover::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits::<
                    DEFAULT_TRACE_PADDING_MULTIPLE,
                    A,
                    DefaultTreeConstructor,
                >(
                    &precomputation.compiled_circuit,
                    &[],
                    &external_challenges,
                    witness_trace,
                    &[],
                    &precomputation.setup,
                    &precomputation.twiddles,
                    &precomputation.lde_precomputations,
                    None,
                    precomputation.lde_factor,
                    precomputation.tree_cap_size,
                    crate::NUM_QUERIES,
                    verifier_common::POW_BITS as u32,
                    &worker,
                );
            println!(
                "Proving time for unrolled circuit type {} is {:?}",
                family_idx,
                now.elapsed()
            );

            // {
            //     serialize_to_file(&proof, &format!("riscv_proof_{}", circuit_sequence));
            // }

            permutation_argument_grand_product
                .mul_assign(&proof.permutation_grand_product_accumulator);
            if let Some(delegation_argument_accumulator) = proof.delegation_argument_accumulator {
                assert_eq!(
                    family_idx,
                    common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
                );
                delegation_argument_sum.add_assign(&delegation_argument_accumulator);
            } else {
                assert_ne!(
                    family_idx,
                    common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
                );
            }

            family_caps.push(proof.memory_tree_caps.clone());
            family_proofs.push(proof);
        }
        aux_memory_trees.push((family_idx as u32, family_caps));
        main_proofs.insert(family_idx, family_proofs);
    }

    for (family_idx, witness_chunks) in mem_circuits.into_iter() {
        if witness_chunks.is_empty() {
            continue;
        }

        if should_dump_witness {
            // TODO
        }

        let mut family_caps = vec![];
        let mut family_proofs = vec![];

        let precomputation = &unrolled_circuits_precomputations[&family_idx];
        let UnrolledCircuitWitnessEvalFn::Memory {
            decoder_table,
            witness_fn,
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for chunk in witness_chunks.into_iter() {
            let oracle = MemoryCircuitOracle {
                inner: &chunk.data[..],
                decoder_table,
            };

            let now = std::time::Instant::now();
            let witness_trace = prover::unrolled::evaluate_witness_for_executor_family::<_, A>(
                &precomputation.compiled_circuit,
                *witness_fn,
                precomputation.trace_len - 1,
                &oracle,
                &precomputation.table_driver,
                &worker,
                A::default(),
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Witness generation for unrolled circuit type {} took {:?}",
                family_idx,
                now.elapsed()
            );

            if crate::PRECHECK_SATISFIED {
                println!("Will evaluate basic satisfiability checks for main circuit");

                assert!(check_satisfied(
                    &precomputation.compiled_circuit,
                    &witness_trace.exec_trace,
                    witness_trace.num_witness_columns
                ));
            }

            let now = std::time::Instant::now();
            let (prover_data, proof) =
                prover::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits::<
                    DEFAULT_TRACE_PADDING_MULTIPLE,
                    A,
                    DefaultTreeConstructor,
                >(
                    &precomputation.compiled_circuit,
                    &[],
                    &external_challenges,
                    witness_trace,
                    &[],
                    &precomputation.setup,
                    &precomputation.twiddles,
                    &precomputation.lde_precomputations,
                    None,
                    precomputation.lde_factor,
                    precomputation.tree_cap_size,
                    crate::NUM_QUERIES,
                    verifier_common::POW_BITS as u32,
                    &worker,
                );
            println!(
                "Proving time for unrolled circuit type {} is {:?}",
                family_idx,
                now.elapsed()
            );

            // {
            //     serialize_to_file(&proof, &format!("riscv_proof_{}", circuit_sequence));
            // }

            permutation_argument_grand_product
                .mul_assign(&proof.permutation_grand_product_accumulator);
            if let Some(delegation_argument_accumulator) = proof.delegation_argument_accumulator {
                assert_eq!(
                    family_idx,
                    common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
                );
                delegation_argument_sum.add_assign(&delegation_argument_accumulator);
            } else {
                assert_ne!(
                    family_idx,
                    common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
                );
            }

            family_caps.push(proof.memory_tree_caps.clone());
            family_proofs.push(proof);
        }
        aux_memory_trees.push((family_idx as u32, family_caps));
        main_proofs.insert(family_idx, family_proofs);
    }

    // inits and teardowns
    let mut aux_inits_and_teardown_trees = vec![];
    let mut inits_and_teardowns_proofs = vec![];
    for witness_chunk in inits_and_teardowns.into_iter() {
        let now = std::time::Instant::now();
        let witness_trace = evaluate_init_and_teardown_witness::<A>(
            &inits_and_teardowns_precomputation.compiled_circuit,
            inits_and_teardowns_precomputation.trace_len - 1,
            &witness_chunk.lazy_init_data,
            &worker,
            A::default(),
        );
        #[cfg(feature = "timing_logs")]
        println!(
            "Witness generation for inits and teardowns circuit took {:?}",
            now.elapsed()
        );

        let WitnessEvaluationData {
            aux_data,
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        } = witness_trace;
        let witness_trace = WitnessEvaluationDataForExecutionFamily {
            aux_data: ExecutorFamilyWitnessEvaluationAuxData {},
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        };

        let now = std::time::Instant::now();
        let (prover_data, proof) =
            prover::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits::<
                DEFAULT_TRACE_PADDING_MULTIPLE,
                A,
                DefaultTreeConstructor,
            >(
                &inits_and_teardowns_precomputation.compiled_circuit,
                &[],
                &external_challenges,
                witness_trace,
                &aux_data.aux_boundary_data,
                &inits_and_teardowns_precomputation.setup,
                &inits_and_teardowns_precomputation.twiddles,
                &inits_and_teardowns_precomputation.lde_precomputations,
                None,
                inits_and_teardowns_precomputation.lde_factor,
                inits_and_teardowns_precomputation.tree_cap_size,
                crate::NUM_QUERIES,
                verifier_common::POW_BITS as u32,
                &worker,
            );
        #[cfg(feature = "timing_logs")]
        println!(
            "Proving time for inits and teardowns circuit is {:?}",
            now.elapsed()
        );

        permutation_argument_grand_product.mul_assign(&proof.permutation_grand_product_accumulator);

        aux_inits_and_teardown_trees.push(proof.memory_tree_caps.clone());
        inits_and_teardowns_proofs.push(proof);
    }

    // all the same for delegation circuit
    let mut aux_delegation_memory_trees = vec![];
    let mut delegation_proofs = vec![];
    let delegation_proving_start = std::time::Instant::now();
    let mut delegation_proofs_count = 0u32;
    // commit memory trees
    for (delegation_type, els) in delegation_circuits.into_iter() {
        if els.is_empty() {
            continue;
        }

        println!(
            "Producing proofs for delegation circuit type {}, {} proofs in total",
            delegation_type,
            els.len()
        );

        let idx = delegation_circuits_precomputations
            .iter()
            .position(|el| el.0 == delegation_type as u32)
            .unwrap();
        let prec = &delegation_circuits_precomputations[idx].1;
        let mut per_tree_set = vec![];

        let mut per_delegation_type_proofs = vec![];
        for (_circuit_idx, el) in els.iter().enumerate() {
            delegation_proofs_count += 1;
            let oracle: DelegationCircuitOracle<'_, A> =
                DelegationCircuitOracle::<A> { cycle_data: el };

            if should_dump_witness {
                // println!(
                //     "Will serialize witness for delegaiton circuit {}",
                //     delegation_type
                // );
                // bincode_serialize_to_file(
                //     &oracle.cycle_data,
                //     &format!(
                //         "delegation_circuit_{}_{}_oracle_witness.bin",
                //         delegation_type, _circuit_idx
                //     ),
                // );
                // println!("Serialization is done");
            }

            #[cfg(feature = "timing_logs")]
            let now = std::time::Instant::now();
            let witness_trace = prover::evaluate_witness::<DelegationCircuitOracle<'_, A>, A>(
                &prec.compiled_circuit.compiled_circuit,
                prec.witness_eval_fn_for_gpu_tracer,
                prec.compiled_circuit.num_requests_per_circuit,
                &oracle,
                &[],
                &prec.compiled_circuit.table_driver,
                0,
                worker,
                A::default(),
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Witness generation for delegation circuit type {} took {:?}",
                delegation_type,
                now.elapsed()
            );

            if crate::PRECHECK_SATISFIED {
                println!(
                    "Will evaluate basic satisfiability checks for delegation circuit {}",
                    delegation_type
                );

                assert!(check_satisfied(
                    &prec.compiled_circuit.compiled_circuit,
                    &witness_trace.exec_trace,
                    witness_trace.num_witness_columns
                ));
            }

            // and prove
            let external_values = ExternalValues {
                challenges: external_challenges,
                aux_boundary_values: AuxArgumentsBoundaryValues::default(),
            };

            #[cfg(feature = "timing_logs")]
            let now = std::time::Instant::now();
            assert!(delegation_type < 1 << 12);
            let (_, proof) = prover::prover_stages::prove(
                &prec.compiled_circuit.compiled_circuit,
                &[],
                &external_values,
                witness_trace,
                &prec.setup,
                &prec.twiddles,
                &prec.lde_precomputations,
                0,
                Some(delegation_type as u16),
                prec.lde_factor,
                prec.tree_cap_size,
                crate::NUM_QUERIES,
                verifier_common::POW_BITS as u32,
                worker,
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Proving for delegation circuit type {} took {:?}",
                delegation_type,
                now.elapsed()
            );

            permutation_argument_grand_product.mul_assign(&proof.memory_grand_product_accumulator);
            delegation_argument_sum.sub_assign(&proof.delegation_argument_accumulator.unwrap());

            per_tree_set.push(proof.memory_tree_caps.clone());

            per_delegation_type_proofs.push(proof);
        }

        aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
        delegation_proofs.push((delegation_type as u32, per_delegation_type_proofs));
    }

    if delegation_proofs_count > 0 {
        println!(
            "=== Total delegation proving time: {:?} for {} circuits - avg: {:?}",
            delegation_proving_start.elapsed(),
            delegation_proofs_count,
            delegation_proving_start.elapsed() / (delegation_proofs_count as u32)
        )
    }

    assert_eq!(permutation_argument_grand_product, Mersenne31Quartic::ONE);
    assert_eq!(delegation_argument_sum, Mersenne31Quartic::ZERO);

    assert_eq!(&aux_memory_trees, &memory_trees);
    assert_eq!(&aux_inits_and_teardown_trees, &inits_and_teardown_trees);
    assert_eq!(&aux_delegation_memory_trees, &delegation_memory_trees);

    // compare challenge
    let aux_all_challenges_seed =
        fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits(
            &register_final_state,
            final_pc,
            final_timestamp,
            &aux_memory_trees,
            &aux_inits_and_teardown_trees,
            &aux_delegation_memory_trees,
        );

    assert_eq!(aux_all_challenges_seed, all_challenges_seed);

    (
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
    )
}

pub fn prove_unrolled_execution_with_replayer<
    C: MachineConfig,
    A: GoodAllocator,
    const ROM_BOUND_SECOND_WORD_BITS: usize,
>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    mut non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource<
        riscv_transpiler::vm::RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS>,
    >,
    unrolled_circuits_precomputations: &BTreeMap<u8, UnrolledCircuitPrecomputations<A, A>>,
    inits_and_teardowns_precomputation: &UnrolledCircuitPrecomputations<A, A>,
    delegation_circuits_precomputations: &[(u32, DelegationCircuitPrecomputations<A, A>)],
    ram_bound: usize,
    worker: &worker::Worker,
) -> (
    BTreeMap<u8, Vec<UnrolledModeProof>>,
    Vec<UnrolledModeProof>,
    Vec<(u32, Vec<Proof>)>,
    [FinalRegisterValue; 32],
    (u32, TimestampScalar),
) {
    use prover::unrolled::run_unrolled_machine;

    const DEFAULT_SNAPSHOT_PERIOD: usize = 1 << 20;
    let max_snapshots = cycles_bound.div_ceil(DEFAULT_SNAPSHOT_PERIOD);

    let family_chunk_sizes = HashMap::from_iter(
        [
            (
                setups::add_sub_lui_auipc_mop::FAMILY_IDX,
                setups::add_sub_lui_auipc_mop::NUM_CYCLES,
            ),
            (
                setups::jump_branch_slt::FAMILY_IDX,
                setups::jump_branch_slt::NUM_CYCLES,
            ),
            (
                setups::shift_binary_csr::FAMILY_IDX,
                setups::shift_binary_csr::NUM_CYCLES,
            ),
            (
                setups::mul_div_unsigned::FAMILY_IDX,
                setups::mul_div_unsigned::NUM_CYCLES,
            ),
            (
                setups::load_store_word_only::FAMILY_IDX,
                setups::load_store_word_only::NUM_CYCLES,
            ),
            (
                setups::load_store_subword_only::FAMILY_IDX,
                setups::load_store_subword_only::NUM_CYCLES,
            ),
        ]
        .into_iter(),
    );

    let delegation_chunk_sizes = HashMap::from_iter(
        [
            (
                setups::blake2_with_compression::DELEGATION_TYPE_ID as u16,
                setups::blake2_with_compression::NUM_DELEGATION_CYCLES,
            ),
            (
                setups::bigint_with_control::DELEGATION_TYPE_ID as u16,
                setups::bigint_with_control::NUM_DELEGATION_CYCLES,
            ),
            (
                setups::keccak_special5::DELEGATION_TYPE_ID as u16,
                setups::keccak_special5::NUM_DELEGATION_CYCLES,
            ),
        ]
        .into_iter(),
    );

    let (
        final_pc,
        final_timestamp,
        cycles_used,
        non_mem_circuits,
        mem_circuits,
        (blake_circuits, bigint_circuits, keccak_circuits),
        register_final_state,
        shuffle_ram_touched_addresses,
    ) = run_unrolled_machine::<C, A, ROM_BOUND_SECOND_WORD_BITS>(
        common_constants::INITIAL_PC,
        text_section,
        binary_image,
        max_snapshots,
        DEFAULT_SNAPSHOT_PERIOD,
        ram_bound,
        &mut non_determinism,
        family_chunk_sizes,
        delegation_chunk_sizes,
        worker,
    );

    let should_dump_witness = std::env::var(DUMP_WITNESS_VAR)
        .map(|el| el.parse::<u32>().unwrap_or(0) == 1)
        .unwrap_or(false);

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    let mut memory_trees = vec![];

    // let decoder_preprocessing = preprocess_text_section_for_machine_config::<C, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(text_section);

    // order by family index
    let non_mem_circuits = BTreeMap::from_iter(non_mem_circuits.into_iter());
    let mem_circuits = BTreeMap::from_iter(mem_circuits.into_iter());

    for (k, v) in non_mem_circuits.iter() {
        println!("{} circuits of family {}", v.len(), k);
    }
    for (k, v) in mem_circuits.iter() {
        println!("{} circuits of family {}", v.len(), k);
    }

    // restructure inits/teardowns
    let num_inits_per_circuit = setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS
        * (setups::inits_and_teardowns::DOMAIN_SIZE - 1);

    let total_input_len: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();
    let num_needed_chunks =
        total_input_len.next_multiple_of(num_inits_per_circuit) / num_inits_per_circuit;

    use crate::tracers::oracles::chunk_lazy_init_and_teardown;

    let (num_trivial, inits_and_teardowns) = chunk_lazy_init_and_teardown::<A, _>(
        num_needed_chunks,
        num_inits_per_circuit,
        &shuffle_ram_touched_addresses,
        &worker,
    );
    assert_eq!(num_trivial, 0);

    let register_final_state = register_final_state.map(|el| FinalRegisterValue {
        value: el.current_value,
        last_access_timestamp: el.last_access_timestamp,
    });

    // commit memory trees
    for (family_idx, witness_chunks) in non_mem_circuits.iter() {
        if witness_chunks.is_empty() {
            continue;
        }

        let mut family_caps = vec![];
        let precomputation = &unrolled_circuits_precomputations[family_idx];
        let UnrolledCircuitWitnessEvalFn::NonMemory {
            decoder_table,
            default_pc_value_in_padding,
            ..
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for chunk in witness_chunks.iter() {
            let caps = commit_memory_tree_for_unrolled_nonmem_circuits(
                &precomputation.compiled_circuit,
                &chunk.data,
                &precomputation.twiddles,
                &precomputation.lde_precomputations,
                *default_pc_value_in_padding,
                decoder_table,
                worker,
            );

            family_caps.push(caps);
        }
        memory_trees.push((*family_idx as u32, family_caps));
    }

    for (family_idx, witness_chunks) in mem_circuits.iter() {
        if witness_chunks.is_empty() {
            continue;
        }

        let mut family_caps = vec![];
        let precomputation = &unrolled_circuits_precomputations[family_idx];
        let UnrolledCircuitWitnessEvalFn::Memory { decoder_table, .. } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for chunk in witness_chunks.iter() {
            let caps = commit_memory_tree_for_unrolled_mem_circuits(
                &precomputation.compiled_circuit,
                &chunk.data,
                &precomputation.twiddles,
                &precomputation.lde_precomputations,
                decoder_table,
                worker,
            );

            family_caps.push(caps);
        }
        memory_trees.push((*family_idx as u32, family_caps));
    }

    // and inits and teardowns
    let mut inits_and_teardown_trees = vec![];
    let mut previous_aux: Option<AuxArgumentsBoundaryValues> = None;
    for witness_chunk in inits_and_teardowns.iter() {
        let (caps, aux_data) = commit_memory_tree_for_inits_and_teardowns_unrolled_circuit(
            &inits_and_teardowns_precomputation.compiled_circuit,
            &witness_chunk.lazy_init_data,
            &inits_and_teardowns_precomputation.twiddles,
            &inits_and_teardowns_precomputation.lde_precomputations,
            worker,
        );

        inits_and_teardown_trees.push(caps);

        for aux_data in aux_data.aux_boundary_data.iter() {
            if let Some(previous_aux) = previous_aux.take() {
                let previous_aux = &previous_aux;
                let this = u32_from_field_elems(&aux_data.lazy_init_first_row);
                let previous = u32_from_field_elems(&previous_aux.lazy_init_one_before_last_row);
                if this > previous {
                    // normal ascending comparison
                } else {
                    // we expect zero prepadding, and zero teardown data
                    assert_eq!(this, previous);
                    assert_eq!(previous, 0);
                    assert_eq!(
                        u32_from_field_elems(&previous_aux.teardown_value_one_before_last_row),
                        0
                    );
                    assert_eq!(
                        u32_from_field_elems(&previous_aux.teardown_timestamp_one_before_last_row),
                        0
                    );
                }
            }
            previous_aux = Some(*aux_data);
        }
    }

    // #[cfg(feature = "timing_logs")]
    // println!(
    //     "=== Commitment for {} RISC-V circuits memory trees took {:?}",
    //     main_circuits_witness.len(),
    //     now.elapsed()
    // );

    // same for delegation circuits
    let now = std::time::Instant::now();
    let mut delegation_memory_trees = vec![];
    {
        type DelegationDescription = Blake2sRoundFunctionAbiDescription;
        let delegation_type = setups::blake2_with_compression::DELEGATION_TYPE_ID;
        let delegation_circuits = &blake_circuits;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit_with_replayer_format::<
                    A,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &prec.compiled_circuit.compiled_circuit,
                    el,
                    prec.trace_len - 1,
                    &prec.twiddles,
                    &prec.lde_precomputations,
                    prec.lde_factor,
                    prec.tree_cap_size,
                    worker,
                );
                per_tree_set.push(caps);
            }

            delegation_memory_trees.push((delegation_type as u32, per_tree_set));
        }
    }
    {
        type DelegationDescription = BigintAbiDescription;
        let delegation_type = setups::bigint_with_control::DELEGATION_TYPE_ID;
        let delegation_circuits = &bigint_circuits;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit_with_replayer_format::<
                    A,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &prec.compiled_circuit.compiled_circuit,
                    el,
                    prec.trace_len - 1,
                    &prec.twiddles,
                    &prec.lde_precomputations,
                    prec.lde_factor,
                    prec.tree_cap_size,
                    worker,
                );
                per_tree_set.push(caps);
            }

            delegation_memory_trees.push((delegation_type as u32, per_tree_set));
        }
    }
    {
        type DelegationDescription = KeccakSpecial5AbiDescription;
        let delegation_type = setups::keccak_special5::DELEGATION_TYPE_ID;
        let delegation_circuits = &keccak_circuits;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit_with_replayer_format::<
                    A,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &prec.compiled_circuit.compiled_circuit,
                    el,
                    prec.trace_len - 1,
                    &prec.twiddles,
                    &prec.lde_precomputations,
                    prec.lde_factor,
                    prec.tree_cap_size,
                    worker,
                );
                per_tree_set.push(caps);
            }

            delegation_memory_trees.push((delegation_type as u32, per_tree_set));
        }
    }
    // #[cfg(feature = "timing_logs")]
    // println!(
    //     "=== Commitment for {} delegation circuits memory trees took {:?}",
    //     delegation_circuits_witness.len(),
    //     now.elapsed()
    // );

    #[cfg(feature = "debug_logs")]
    println!("Will create FS transformation challenge for memory and delegation arguments");

    // commit memory challenges
    let all_challenges_seed =
        fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits(
            &register_final_state,
            final_pc,
            final_timestamp,
            &memory_trees,
            &inits_and_teardown_trees,
            &delegation_memory_trees,
        );

    #[cfg(feature = "debug_logs")]
    println!("FS transformation memory seed is {:?}", all_challenges_seed);

    let external_challenges =
        ExternalChallenges::draw_from_transcript_seed_with_state_permutation(all_challenges_seed);

    #[cfg(feature = "debug_logs")]
    println!("External challenges = {:?}", external_challenges);

    let input = register_final_state
        .iter()
        .map(|el| (el.value, split_timestamp(el.last_access_timestamp)))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let mut permutation_argument_grand_product =
        produce_register_contribution_into_memory_accumulator_raw(
            &input,
            external_challenges
                .memory_argument
                .memory_argument_linearization_challenges,
            external_challenges.memory_argument.memory_argument_gamma,
        );
    let pc_permutation_contribution = produce_pc_into_permutation_accumulator_raw(
        ENTRY_POINT,
        split_timestamp(INITIAL_TIMESTAMP),
        final_pc,
        split_timestamp(final_timestamp),
        &external_challenges
            .machine_state_permutation_argument
            .unwrap()
            .linearization_challenges,
        &external_challenges
            .machine_state_permutation_argument
            .unwrap()
            .additive_term,
    );
    permutation_argument_grand_product.mul_assign(&pc_permutation_contribution);
    let mut delegation_argument_sum = Mersenne31Quartic::ZERO;

    let mut aux_memory_trees = vec![];

    // println!(
    //     "Producing proofs for main RISC-V circuit, {} proofs in total",
    //     main_circuits_witness.len()
    // );

    let total_proving_start = std::time::Instant::now();

    // now prove one by one
    let mut main_proofs = BTreeMap::new();
    for (family_idx, witness_chunks) in non_mem_circuits.into_iter() {
        if witness_chunks.is_empty() {
            // for consistency
            main_proofs.insert(family_idx, vec![]);
            continue;
        }

        if should_dump_witness {
            // TODO
        }

        let mut family_caps = vec![];
        let mut family_proofs = vec![];

        let precomputation = &unrolled_circuits_precomputations[&family_idx];
        let UnrolledCircuitWitnessEvalFn::NonMemory {
            decoder_table,
            default_pc_value_in_padding,
            witness_fn,
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for chunk in witness_chunks.into_iter() {
            let oracle = NonMemoryCircuitOracle {
                inner: &chunk.data,
                decoder_table,
                default_pc_value_in_padding: *default_pc_value_in_padding,
            };

            let now = std::time::Instant::now();
            let witness_trace = prover::unrolled::evaluate_witness_for_executor_family::<_, A>(
                &precomputation.compiled_circuit,
                *witness_fn,
                precomputation.trace_len - 1,
                &oracle,
                &precomputation.table_driver,
                &worker,
                A::default(),
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Witness generation for unrolled circuit type {} took {:?}",
                family_idx,
                now.elapsed()
            );

            if crate::PRECHECK_SATISFIED {
                println!("Will evaluate basic satisfiability checks for main circuit");

                assert!(check_satisfied(
                    &precomputation.compiled_circuit,
                    &witness_trace.exec_trace,
                    witness_trace.num_witness_columns
                ));
            }

            let now = std::time::Instant::now();
            let (prover_data, proof) =
                prover::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits::<
                    DEFAULT_TRACE_PADDING_MULTIPLE,
                    A,
                    DefaultTreeConstructor,
                >(
                    &precomputation.compiled_circuit,
                    &[],
                    &external_challenges,
                    witness_trace,
                    &[],
                    &precomputation.setup,
                    &precomputation.twiddles,
                    &precomputation.lde_precomputations,
                    None,
                    precomputation.lde_factor,
                    precomputation.tree_cap_size,
                    crate::NUM_QUERIES,
                    verifier_common::POW_BITS as u32,
                    &worker,
                );
            println!(
                "Proving time for unrolled circuit type {} is {:?}",
                family_idx,
                now.elapsed()
            );

            // {
            //     serialize_to_file(&proof, &format!("riscv_proof_{}", circuit_sequence));
            // }

            permutation_argument_grand_product
                .mul_assign(&proof.permutation_grand_product_accumulator);
            if let Some(delegation_argument_accumulator) = proof.delegation_argument_accumulator {
                assert_eq!(
                    family_idx,
                    common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
                );
                delegation_argument_sum.add_assign(&delegation_argument_accumulator);
            } else {
                assert_ne!(
                    family_idx,
                    common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
                );
            }

            family_caps.push(proof.memory_tree_caps.clone());
            family_proofs.push(proof);
        }
        aux_memory_trees.push((family_idx as u32, family_caps));
        main_proofs.insert(family_idx, family_proofs);
    }

    for (family_idx, witness_chunks) in mem_circuits.into_iter() {
        if witness_chunks.is_empty() {
            // for consistency
            main_proofs.insert(family_idx, vec![]);
            continue;
        }

        if should_dump_witness {
            // TODO
        }

        let mut family_caps = vec![];
        let mut family_proofs = vec![];

        let precomputation = &unrolled_circuits_precomputations[&family_idx];
        let UnrolledCircuitWitnessEvalFn::Memory {
            decoder_table,
            witness_fn,
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for chunk in witness_chunks.into_iter() {
            let oracle = MemoryCircuitOracle {
                inner: &chunk.data[..],
                decoder_table,
            };

            let now = std::time::Instant::now();
            let witness_trace = prover::unrolled::evaluate_witness_for_executor_family::<_, A>(
                &precomputation.compiled_circuit,
                *witness_fn,
                precomputation.trace_len - 1,
                &oracle,
                &precomputation.table_driver,
                &worker,
                A::default(),
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Witness generation for unrolled circuit type {} took {:?}",
                family_idx,
                now.elapsed()
            );

            if crate::PRECHECK_SATISFIED {
                println!("Will evaluate basic satisfiability checks for main circuit");

                assert!(check_satisfied(
                    &precomputation.compiled_circuit,
                    &witness_trace.exec_trace,
                    witness_trace.num_witness_columns
                ));
            }

            let now = std::time::Instant::now();
            let (prover_data, proof) =
                prover::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits::<
                    DEFAULT_TRACE_PADDING_MULTIPLE,
                    A,
                    DefaultTreeConstructor,
                >(
                    &precomputation.compiled_circuit,
                    &[],
                    &external_challenges,
                    witness_trace,
                    &[],
                    &precomputation.setup,
                    &precomputation.twiddles,
                    &precomputation.lde_precomputations,
                    None,
                    precomputation.lde_factor,
                    precomputation.tree_cap_size,
                    crate::NUM_QUERIES,
                    verifier_common::POW_BITS as u32,
                    &worker,
                );
            println!(
                "Proving time for unrolled circuit type {} is {:?}",
                family_idx,
                now.elapsed()
            );

            // {
            //     serialize_to_file(&proof, &format!("riscv_proof_{}", circuit_sequence));
            // }

            permutation_argument_grand_product
                .mul_assign(&proof.permutation_grand_product_accumulator);
            if let Some(delegation_argument_accumulator) = proof.delegation_argument_accumulator {
                assert_eq!(
                    family_idx,
                    common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
                );
                delegation_argument_sum.add_assign(&delegation_argument_accumulator);
            } else {
                assert_ne!(
                    family_idx,
                    common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
                );
            }

            family_caps.push(proof.memory_tree_caps.clone());
            family_proofs.push(proof);
        }
        aux_memory_trees.push((family_idx as u32, family_caps));
        main_proofs.insert(family_idx, family_proofs);
    }

    // inits and teardowns
    let mut aux_inits_and_teardown_trees = vec![];
    let mut inits_and_teardowns_proofs = vec![];
    for witness_chunk in inits_and_teardowns.into_iter() {
        let now = std::time::Instant::now();
        let witness_trace = evaluate_init_and_teardown_witness::<A>(
            &inits_and_teardowns_precomputation.compiled_circuit,
            inits_and_teardowns_precomputation.trace_len - 1,
            &witness_chunk.lazy_init_data,
            &worker,
            A::default(),
        );
        #[cfg(feature = "timing_logs")]
        println!(
            "Witness generation for inits and teardowns circuit took {:?}",
            now.elapsed()
        );

        let WitnessEvaluationData {
            aux_data,
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        } = witness_trace;
        let witness_trace = WitnessEvaluationDataForExecutionFamily {
            aux_data: ExecutorFamilyWitnessEvaluationAuxData {},
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        };

        let now = std::time::Instant::now();
        let (prover_data, proof) =
            prover::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits::<
                DEFAULT_TRACE_PADDING_MULTIPLE,
                A,
                DefaultTreeConstructor,
            >(
                &inits_and_teardowns_precomputation.compiled_circuit,
                &[],
                &external_challenges,
                witness_trace,
                &aux_data.aux_boundary_data,
                &inits_and_teardowns_precomputation.setup,
                &inits_and_teardowns_precomputation.twiddles,
                &inits_and_teardowns_precomputation.lde_precomputations,
                None,
                inits_and_teardowns_precomputation.lde_factor,
                inits_and_teardowns_precomputation.tree_cap_size,
                crate::NUM_QUERIES,
                verifier_common::POW_BITS as u32,
                &worker,
            );
        #[cfg(feature = "timing_logs")]
        println!(
            "Proving time for inits and teardowns circuit is {:?}",
            now.elapsed()
        );

        permutation_argument_grand_product.mul_assign(&proof.permutation_grand_product_accumulator);

        aux_inits_and_teardown_trees.push(proof.memory_tree_caps.clone());
        inits_and_teardowns_proofs.push(proof);
    }

    // all the same for delegation circuit
    let mut aux_delegation_memory_trees = vec![];
    let mut delegation_proofs = vec![];
    let delegation_proving_start = std::time::Instant::now();
    let mut delegation_proofs_count = 0;

    {
        type DelegationDescription = Blake2sRoundFunctionAbiDescription;
        let delegation_type = setups::blake2_with_compression::DELEGATION_TYPE_ID;
        let delegation_circuits = blake_circuits;
        let witness_eval_fn = setups::blake2_with_compression::witness_eval_fn_for_replayer;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let (proofs, per_tree_set) = prove_delegation_circuit_with_replayer_format::<
                A,
                DelegationDescription,
                _,
                _,
                _,
                _,
            >(
                &delegation_circuits,
                external_challenges,
                prec,
                witness_eval_fn,
                delegation_type as u16,
                &mut permutation_argument_grand_product,
                &mut delegation_argument_sum,
                &mut delegation_proofs_count,
                should_dump_witness,
                worker,
            );

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type as u32, proofs));
        }
    }
    {
        type DelegationDescription = BigintAbiDescription;
        let delegation_type = setups::bigint_with_control::DELEGATION_TYPE_ID;
        let delegation_circuits = bigint_circuits;
        let witness_eval_fn = setups::bigint_with_control::witness_eval_fn_for_replayer;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let (proofs, per_tree_set) = prove_delegation_circuit_with_replayer_format::<
                A,
                DelegationDescription,
                _,
                _,
                _,
                _,
            >(
                &delegation_circuits,
                external_challenges,
                prec,
                witness_eval_fn,
                delegation_type as u16,
                &mut permutation_argument_grand_product,
                &mut delegation_argument_sum,
                &mut delegation_proofs_count,
                should_dump_witness,
                worker,
            );

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type as u32, proofs));
        }
    }
    {
        type DelegationDescription = KeccakSpecial5AbiDescription;
        let delegation_type = setups::keccak_special5::DELEGATION_TYPE_ID;
        let delegation_circuits = keccak_circuits;
        let witness_eval_fn = setups::keccak_special5::witness_eval_fn_for_replayer;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let (proofs, per_tree_set) = prove_delegation_circuit_with_replayer_format::<
                A,
                DelegationDescription,
                _,
                _,
                _,
                _,
            >(
                &delegation_circuits,
                external_challenges,
                prec,
                witness_eval_fn,
                delegation_type as u16,
                &mut permutation_argument_grand_product,
                &mut delegation_argument_sum,
                &mut delegation_proofs_count,
                should_dump_witness,
                worker,
            );

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type as u32, proofs));
        }
    }

    if delegation_proofs_count > 0 {
        println!(
            "=== Total delegation proving time: {:?} for {} circuits - avg: {:?}",
            delegation_proving_start.elapsed(),
            delegation_proofs_count,
            delegation_proving_start.elapsed() / (delegation_proofs_count as u32)
        )
    }

    assert_eq!(permutation_argument_grand_product, Mersenne31Quartic::ONE);
    assert_eq!(delegation_argument_sum, Mersenne31Quartic::ZERO);

    assert_eq!(&aux_memory_trees, &memory_trees);
    assert_eq!(&aux_inits_and_teardown_trees, &inits_and_teardown_trees);
    assert_eq!(&aux_delegation_memory_trees, &delegation_memory_trees);

    // compare challenge
    let aux_all_challenges_seed =
        fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits(
            &register_final_state,
            final_pc,
            final_timestamp,
            &aux_memory_trees,
            &aux_inits_and_teardown_trees,
            &aux_delegation_memory_trees,
        );

    assert_eq!(aux_all_challenges_seed, all_challenges_seed);

    (
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
    )
}

fn prove_delegation_circuit_with_replayer_format<
    A: GoodAllocator,
    D: DelegationAbiDescription,
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
>(
    witnesses: &[Vec<
        riscv_transpiler::witness::DelegationWitness<
            REG_ACCESSES,
            INDIRECT_READS,
            INDIRECT_WRITES,
            VARIABLE_OFFSETS,
        >,
        A,
    >],
    external_challenges: ExternalChallenges,
    prec: &DelegationCircuitPrecomputations<A, A>,
    witness_eval_fn: fn(
        &mut prover::SimpleWitnessProxy<
            '_,
            DelegationOracle<
                '_,
                D,
                REG_ACCESSES,
                INDIRECT_READS,
                INDIRECT_WRITES,
                VARIABLE_OFFSETS,
            >,
        >,
    ),
    delegation_type: u16,
    permutation_argument_grand_product: &mut Mersenne31Quartic,
    delegation_argument_sum: &mut Mersenne31Quartic,
    delegation_proofs_count: &mut usize,
    should_dump_witness: bool,
    worker: &worker::Worker,
) -> (
    Vec<Proof>,
    Vec<Vec<prover::merkle_trees::MerkleTreeCapVarLength>>,
) {
    let mut per_tree_set = vec![];

    let mut per_delegation_type_proofs = vec![];
    for (_circuit_idx, el) in witnesses.iter().enumerate() {
        *delegation_proofs_count += 1;
        let oracle = DelegationOracle::<D, _, _, _, _> {
            cycle_data: el,
            marker: core::marker::PhantomData,
        };

        if should_dump_witness {
            // println!(
            //     "Will serialize witness for delegaiton circuit {}",
            //     delegation_type
            // );
            // bincode_serialize_to_file(
            //     &oracle.cycle_data,
            //     &format!(
            //         "delegation_circuit_{}_{}_oracle_witness.bin",
            //         delegation_type, _circuit_idx
            //     ),
            // );
            // println!("Serialization is done");
        }

        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        let witness_trace = prover::evaluate_witness::<DelegationOracle<'_, D, _, _, _, _>, A>(
            &prec.compiled_circuit.compiled_circuit,
            witness_eval_fn,
            prec.compiled_circuit.num_requests_per_circuit,
            &oracle,
            &[],
            &prec.compiled_circuit.table_driver,
            0,
            worker,
            A::default(),
        );
        #[cfg(feature = "timing_logs")]
        println!(
            "Witness generation for delegation circuit type {} took {:?}",
            delegation_type,
            now.elapsed()
        );

        if crate::PRECHECK_SATISFIED {
            println!(
                "Will evaluate basic satisfiability checks for delegation circuit {}",
                delegation_type
            );

            assert!(check_satisfied(
                &prec.compiled_circuit.compiled_circuit,
                &witness_trace.exec_trace,
                witness_trace.num_witness_columns
            ));
        }

        // and prove
        let external_values = ExternalValues {
            challenges: external_challenges,
            aux_boundary_values: AuxArgumentsBoundaryValues::default(),
        };

        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        assert!(delegation_type < 1 << 12);
        let (_, proof) = prover::prover_stages::prove(
            &prec.compiled_circuit.compiled_circuit,
            &[],
            &external_values,
            witness_trace,
            &prec.setup,
            &prec.twiddles,
            &prec.lde_precomputations,
            0,
            Some(delegation_type as u16),
            prec.lde_factor,
            prec.tree_cap_size,
            crate::NUM_QUERIES,
            verifier_common::POW_BITS as u32,
            worker,
        );
        #[cfg(feature = "timing_logs")]
        println!(
            "Proving for delegation circuit type {} took {:?}",
            delegation_type,
            now.elapsed()
        );

        permutation_argument_grand_product.mul_assign(&proof.memory_grand_product_accumulator);
        delegation_argument_sum.sub_assign(&proof.delegation_argument_accumulator.unwrap());

        per_tree_set.push(proof.memory_tree_caps.clone());

        per_delegation_type_proofs.push(proof);
    }

    (per_delegation_type_proofs, per_tree_set)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bincode_deserialize_from_file;
    use crate::deserialize_from_file;
    use crate::risc_v_simulator::cycle::IMWithoutSignedMulDivIsaConfig;
    use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
    use std::alloc::Global;
    use std::io::Read;
    use std::path::Path;

    use crate::cs::one_row_compiler::CompiledCircuitArtifact;
    use common_constants::TimestampScalar;
    use prover::prover_stages::unrolled_prover::UnrolledModeProof;

    #[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
    pub struct UnrolledProgramProof {
        pub final_pc: u32,
        pub final_timestamp: TimestampScalar,
        pub compiled_circuit_families: BTreeMap<u8, CompiledCircuitArtifact<Mersenne31Field>>,
        pub circuit_families_proofs: BTreeMap<u8, Vec<UnrolledModeProof>>,
        pub compiled_inits_and_teardowns: CompiledCircuitArtifact<Mersenne31Field>,
        pub inits_and_teardowns_proofs: Vec<UnrolledModeProof>,
        pub delegation_proofs: BTreeMap<u32, Vec<Proof>>,
        pub register_final_values: [FinalRegisterValue; 32],
        pub end_params: [u32; 8],
        pub recursion_chain_preimage: Option<[u32; 16]>,
        pub recursion_chain_hash: Option<[u32; 8]>,
    }

    impl UnrolledProgramProof {
        pub fn flatten_into_responses(&self, allowed_delegation_circuits: &[u32]) -> Vec<u32> {
            let mut responses = Vec::with_capacity(32 + 32 * 2);

            assert_eq!(self.register_final_values.len(), 32);
            // registers
            for final_values in self.register_final_values.iter() {
                responses.push(final_values.value);
                let (low, high) = split_timestamp(final_values.last_access_timestamp);
                responses.push(low);
                responses.push(high);
            }

            // final PC and timestamp
            {
                responses.push(self.final_pc);
                let (low, high) = split_timestamp(self.final_timestamp);
                responses.push(low);
                responses.push(high);
            }

            // families ones
            for (family, proofs) in self.circuit_families_proofs.iter() {
                responses.push(proofs.len() as u32);
                for proof in proofs.iter() {
                    let t = verifier_common::proof_flattener::flatten_full_unrolled_proof(
                        proof,
                        &self.compiled_circuit_families[family],
                    );
                    responses.extend(t);
                }
            }

            // inits and teardowns
            {
                responses.push(self.inits_and_teardowns_proofs.len() as u32);
                for proof in self.inits_and_teardowns_proofs.iter() {
                    let t = verifier_common::proof_flattener::flatten_full_unrolled_proof(
                        proof,
                        &self.compiled_inits_and_teardowns,
                    );
                    responses.extend(t);
                }
            }

            // then for every allowed delegation circuit
            for delegation_type in allowed_delegation_circuits.iter() {
                if let Some(proofs) = self.delegation_proofs.get(&delegation_type) {
                    responses.push(proofs.len() as u32);
                    for proof in proofs.iter() {
                        let t = verifier_common::proof_flattener::flatten_full_proof(proof, 0);
                        responses.extend(t);
                    }
                } else {
                    responses.push(0);
                }
            }

            if let Some(preimage) = self.recursion_chain_preimage {
                responses.extend(preimage);
            }

            responses
        }
    }

    #[test]
    fn test_prove_unrolled_fibonacci() {
        let (_, binary_image) =
            setups::read_binary(&Path::new("../../examples/basic_fibonacci/app.bin"));
        let (_, text_section) =
            setups::read_binary(&Path::new("../../examples/basic_fibonacci/app.text"));

        // setups::pad_bytecode_for_proving(&mut binary);

        let worker = worker::Worker::new_with_num_threads(8);
        println!("Performing precomputations for circuit families");
        let families_precomps =
            setups::unrolled_circuits::get_unrolled_circuits_setups_for_machine_type::<
                IMWithoutSignedMulDivIsaConfig,
                _,
                _,
            >(&binary_image, &text_section, &worker);

        println!("Performing precomputations for inits and teardowns");
        let inits_and_teardowns_precomps =
            setups::unrolled_circuits::inits_and_teardowns_circuit_setup(
                &binary_image,
                &text_section,
                &worker,
            );

        println!("Performing precomputations for delegation circuits");
        let delegation_precomputations = setups::all_delegation_circuits_precomputations(&worker);

        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![15, 1]);

        let (
            main_proofs,
            inits_and_teardowns_proofs,
            delegation_proofs,
            register_final_state,
            (final_pc, final_timestamp),
        ) = prove_unrolled_execution::<_, IMWithoutSignedMulDivIsaConfig, Global, 5>(
            1 << 24,
            &binary_image,
            &text_section,
            non_determinism_source,
            &families_precomps,
            &inits_and_teardowns_precomps,
            &delegation_precomputations,
            1 << 32,
            &worker,
        );

        bincode_serialize_to_file(
            &(
                main_proofs,
                inits_and_teardowns_proofs,
                delegation_proofs,
                register_final_state,
                (final_pc, final_timestamp),
            ),
            "tmp_proof.bin",
        );
    }

    #[test]
    fn test_verify_simple_fib() {
        use setups::*;

        let t: (
            BTreeMap<u8, Vec<UnrolledModeProof>>,
            Vec<UnrolledModeProof>,
            Vec<(u32, Vec<Proof>)>,
            [FinalRegisterValue; 32],
            (u32, TimestampScalar),
        ) = bincode_deserialize_from_file("tmp_proof.bin");
        let (
            main_proofs,
            inits_and_teardowns_proofs,
            delegation_proofs,
            register_final_state,
            (final_pc, final_timestamp),
        ) = t;

        let (_, binary_image) =
            setups::read_binary(&Path::new("../../examples/basic_fibonacci/app.bin"));
        let (families, inits_and_teardowns) =
            setups::unrolled_circuits::get_unrolled_circuits_artifacts_for_machine_type::<
                IMWithoutSignedMulDivIsaConfig,
            >(&binary_image);

        // flatten and set iterator

        let program_proofs = UnrolledProgramProof {
            final_pc,
            final_timestamp,
            compiled_circuit_families: families,
            circuit_families_proofs: main_proofs,
            compiled_inits_and_teardowns: inits_and_teardowns,
            inits_and_teardowns_proofs,
            delegation_proofs: BTreeMap::from_iter(delegation_proofs.into_iter()),
            register_final_values: register_final_state,
            end_params: [0u32; 8],
            recursion_chain_hash: None,
            recursion_chain_preimage: None,
        };

        let responses = program_proofs
            .flatten_into_responses(IMWithoutSignedMulDivIsaConfig::ALLOWED_DELEGATION_CSRS);
        let t: (Vec<UnrolledCircuitSetupParams>, [MerkleTreeCap<CAP_SIZE>; NUM_COSETS]) = deserialize_from_file("../setups/42c88bf092af93acc4a3bf780b64dc98a36ba03b54d7acd886dbd9b3eff90285_42c88bf092af93acc4a3bf780b64dc98a36ba03b54d7acd886dbd9b3eff90285.json");
        let (setups, inits_and_teardowns_setup) = t;

        std::thread::Builder::new()
                .name("verifier thread".to_string())
                .stack_size(1 << 27)
                .spawn(move || {

                    let families_setups: Vec<_> = setups.iter().map(|el| &el.setup_caps).collect();

                    let it = responses.into_iter();
                    prover::nd_source_std::set_iterator(it);

                    #[allow(invalid_value)]
                    let _ = unsafe {
                        full_statement_verifier::unrolled_proof_statement::verify_full_statement_for_unrolled_circuits::<true, { setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS }>(
                            &families_setups,
                            full_statement_verifier::unrolled_proof_statement::FULL_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS,
                            (&inits_and_teardowns_setup, full_statement_verifier::unrolled_proof_statement::INITS_AND_TEARDOWNS_VERIFIER_PTR),
                            full_statement_verifier::BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS,
                        )
                    };
                })
                .expect("must spawn")
                .join()
                .expect("must verify");
    }
}
