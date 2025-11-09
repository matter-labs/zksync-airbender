use crate::bincode_serialize_to_file;
use crate::cs::cs::oracle::ExecutorFamilyDecoderData;
use crate::cs::machine::ops::unrolled::*;
use crate::u32_from_field_elems;
use crate::NonDeterminismCSRSource;
use crate::DUMP_WITNESS_VAR;
use common_constants::TimestampScalar;
use common_constants::INITIAL_TIMESTAMP;
use common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use common_constants::TIMESTAMP_STEP;
use prover::check_satisfied;
use prover::cs::utils::split_timestamp;
use prover::definitions::*;
use prover::fft::*;
use prover::field::*;
use prover::get_aux_boundary_data;
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
use prover::unrolled::UnifiedRiscvCircuitOracle;
use prover::witness_evaluator::unrolled::run_unrolled_machine_for_num_cycles_with_word_memory_ops_specialization;
use prover::worker;
use prover::ExecutorFamilyWitnessEvaluationAuxData;
use prover::ShuffleRamSetupAndTeardown;
use prover::VectorMemoryImplWithRom;
use prover::WitnessEvaluationData;
use prover::WitnessEvaluationDataForExecutionFamily;
use prover::DEFAULT_TRACE_PADDING_MULTIPLE;
use risc_v_simulator::cycle::IMStandardIsaConfigWithUnsignedMulDiv;
use risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation;
use risc_v_simulator::cycle::MachineConfig;
use risc_v_simulator::delegations::DelegationsCSRProcessor;
use risc_v_simulator::machine_mode_only_unrolled::DelegationCSRProcessor;
use riscv_transpiler::witness::delegation::bigint::BigintAbiDescription;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionAbiDescription;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5AbiDescription;
use riscv_transpiler::witness::DelegationAbiDescription;
use setups::DelegationCircuitPrecomputations;
use setups::UnrolledCircuitPrecomputations;
use setups::UnrolledCircuitWitnessEvalFn;
use std::alloc::Global;
use std::collections::BTreeMap;
use std::collections::HashMap;
use trace_and_split::commit_memory_tree_for_delegation_circuit_with_gpu_tracer;
use trace_and_split::commit_memory_tree_for_delegation_circuit_with_replayer_format;
use trace_and_split::commit_memory_tree_for_inits_and_teardowns_unrolled_circuit;
use trace_and_split::commit_memory_tree_for_unified_circuits;
use trace_and_split::commit_memory_tree_for_unrolled_mem_circuits;
use trace_and_split::commit_memory_tree_for_unrolled_nonmem_circuits;
use trace_and_split::fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits;
use trace_and_split::FinalRegisterValue;
use trace_and_split::ENTRY_POINT;

pub fn prove_unified_execution_with_replayer<
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
    unified_circuit_precomputation: &UnrolledCircuitPrecomputations<A, A>,
    delegation_circuits_precomputations: &[(u32, DelegationCircuitPrecomputations<A, A>)],
    ram_bound: usize,
    worker: &worker::Worker,
) -> (
    BTreeMap<u8, Vec<UnrolledModeProof>>,
    Vec<(u32, Vec<Proof>)>,
    [FinalRegisterValue; 32],
    (u32, TimestampScalar),
) {
    use prover::unrolled::run_unified_machine;

    const DEFAULT_SNAPSHOT_PERIOD: usize = 1 << 20;
    let max_snapshots = cycles_bound.div_ceil(DEFAULT_SNAPSHOT_PERIOD);

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
        unified_circuits,
        (blake_circuits, bigint_circuits, keccak_circuits),
        register_final_state,
        shuffle_ram_touched_addresses,
    ) = run_unified_machine::<C, A, ROM_BOUND_SECOND_WORD_BITS>(
        common_constants::INITIAL_PC,
        text_section,
        binary_image,
        max_snapshots,
        DEFAULT_SNAPSHOT_PERIOD,
        ram_bound,
        &mut non_determinism,
        unified_circuit_precomputation.trace_len - 1,
        delegation_chunk_sizes,
        worker,
    );

    println!(
        "Execution ended at PC = 0x{:08x} at timestamp {}",
        final_pc, final_timestamp
    );

    let should_dump_witness = std::env::var(DUMP_WITNESS_VAR)
        .map(|el| el.parse::<u32>().unwrap_or(0) == 1)
        .unwrap_or(false);

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    let mut memory_trees = vec![];

    // restructure inits/teardowns
    let num_inits_per_circuit = (unified_circuit_precomputation.trace_len - 1)
        * unified_circuit_precomputation
            .compiled_circuit
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .len();

    let total_input_len: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();

    use crate::tracers::oracles::chunk_lazy_init_and_teardown;

    let (num_trivial, inits_and_teardowns) = chunk_lazy_init_and_teardown::<A, _>(
        unified_circuits.len(),
        num_inits_per_circuit,
        &shuffle_ram_touched_addresses,
        &worker,
    );

    let lazy_init_padding = if num_trivial > 0 {
        vec![LazyInitAndTeardown::EMPTY; num_inits_per_circuit]
    } else {
        Vec::new()
    };

    let register_final_state = register_final_state.map(|el| FinalRegisterValue {
        value: el.current_value,
        last_access_timestamp: el.last_access_timestamp,
    });

    // commit memory trees
    {
        let mut family_caps = vec![];
        let precomputation = unified_circuit_precomputation;
        let UnrolledCircuitWitnessEvalFn::Unified { decoder_table, .. } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for (chunk_idx, chunk) in unified_circuits.iter().enumerate() {
            let inits_and_teardowns = if chunk_idx < num_trivial {
                &lazy_init_padding[..]
            } else {
                &inits_and_teardowns[chunk_idx - num_trivial].lazy_init_data
            };
            let caps = commit_memory_tree_for_unified_circuits(
                &precomputation.compiled_circuit,
                chunk,
                inits_and_teardowns,
                &precomputation.twiddles,
                &precomputation.lde_precomputations,
                decoder_table,
                worker,
            );

            family_caps.push(caps);
        }
        memory_trees.push((REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32, family_caps));
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
            for (idx, el) in delegation_circuits.iter().enumerate() {
                if should_dump_witness {
                    println!(
                        "Will serialize witness for delegation {} circuit {}",
                        delegation_type, idx
                    );
                    bincode_serialize_to_file(
                        &el[..].to_vec(), // realloc to global
                        &format!(
                            "delegation_{}_circuit_{}_oracle_witness.bin",
                            delegation_type, idx
                        ),
                    );
                    println!("Serialization is done");
                }

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
    #[cfg(feature = "timing_logs")]
    println!(
        "=== Commitment for {} delegation circuits memory trees took {:?}",
        delegation_memory_trees
            .iter()
            .map(|el| el.1.len())
            .sum::<usize>(),
        now.elapsed()
    );

    #[cfg(feature = "debug_logs")]
    println!("Will create FS transformation challenge for memory and delegation arguments");

    // commit memory challenges
    let all_challenges_seed =
        fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits(
            &register_final_state,
            final_pc,
            final_timestamp,
            &memory_trees,
            &[],
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
    {
        let mut family_caps = vec![];
        let mut family_proofs = vec![];

        let precomputation = unified_circuit_precomputation;
        let UnrolledCircuitWitnessEvalFn::Unified {
            decoder_table,
            witness_fn,
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for (idx, chunk) in unified_circuits.into_iter().enumerate() {
            if should_dump_witness {
                println!("Will serialize unified circuit witness for circuit {}", idx);
                bincode_serialize_to_file(
                    &chunk[..].to_vec(),
                    &format!("unified_circuit_{}_oracle_witness.bin", idx),
                );
                println!("Serialization is done");
            }

            let oracle = UnifiedRiscvCircuitOracle {
                inner: &chunk[..],
                decoder_table,
            };

            let inits_and_teardowns = if idx < num_trivial {
                &lazy_init_padding[..]
            } else {
                &inits_and_teardowns[idx - num_trivial].lazy_init_data
            };

            let now = std::time::Instant::now();
            let witness_trace = prover::unrolled::evaluate_witness_for_unified_executor::<_, A>(
                &precomputation.compiled_circuit,
                *witness_fn,
                inits_and_teardowns,
                precomputation.trace_len - 1,
                &oracle,
                &precomputation.table_driver,
                &worker,
                A::default(),
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Witness generation for unified circuit took {:?}",
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

            let aux_boundary_values = get_aux_boundary_data(
                &precomputation.compiled_circuit,
                precomputation.trace_len - 1,
                inits_and_teardowns,
            );

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
                    &aux_boundary_values,
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
            println!("Proving time for unified circuit is {:?}", now.elapsed());

            // {
            //     serialize_to_file(&proof, &format!("riscv_proof_{}", circuit_sequence));
            // }

            permutation_argument_grand_product
                .mul_assign(&proof.permutation_grand_product_accumulator);
            if let Some(delegation_argument_accumulator) = proof.delegation_argument_accumulator {
                delegation_argument_sum.add_assign(&delegation_argument_accumulator);
            }

            family_caps.push(proof.memory_tree_caps.clone());
            family_proofs.push(proof);
        }
        aux_memory_trees.push((REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32, family_caps));
        main_proofs.insert(REDUCED_MACHINE_CIRCUIT_FAMILY_IDX, family_proofs);
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

    assert_eq!(delegation_argument_sum, Mersenne31Quartic::ZERO);
    assert_eq!(permutation_argument_grand_product, Mersenne31Quartic::ONE);

    assert_eq!(&aux_memory_trees, &memory_trees);
    assert_eq!(&aux_delegation_memory_trees, &delegation_memory_trees);

    // compare challenge
    let aux_all_challenges_seed =
        fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits(
            &register_final_state,
            final_pc,
            final_timestamp,
            &aux_memory_trees,
            &[],
            &aux_delegation_memory_trees,
        );

    assert_eq!(aux_all_challenges_seed, all_challenges_seed);

    (
        main_proofs,
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
