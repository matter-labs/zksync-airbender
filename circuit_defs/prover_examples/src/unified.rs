use crate::unrolled::make_tracer_buffers;
use crate::unrolled::{
    prove_delegation_circuit, replay_delegation_circuit, run_unrolled_machine_in_full,
};
use common_constants::TimestampScalar;
use common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER;
use common_constants::BLAKE2S_DELEGATION_CSR_REGISTER;
use common_constants::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER;
use common_constants::INITIAL_PC;
use common_constants::INITIAL_TIMESTAMP;
use common_constants::KECCAK_SPECIAL5_CSR_REGISTER;
use common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use common_constants::ROM_WORD_SIZE;
use prover::cs::utils::split_timestamp;
use prover::definitions::produce_initial_permutation_product_contribution;
use prover::definitions::FinalRegisterValue;
use prover::definitions::*;
use prover::fft::*;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::baby_bear::ext4::BabyBearExt4;
use prover::field::*;
use prover::gkr::prover::prove_configured_with_gkr;
use prover::gkr::prover::GKRExternalChallenges;
use prover::gkr::prover::GKRProof;
use prover::gkr::witness_gen::family_circuits::evaluate_gkr_witness_for_executor_family;
use prover::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
use prover::merkle_trees::DefaultTreeConstructor;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::worker;
use riscv_transpiler::cycle::{MachineConfig, ReducedMachineWithDelegation};
use riscv_transpiler::vm::Counters;
use riscv_transpiler::vm::DelegationsAndUnifiedCounters;
use riscv_transpiler::vm::SimpleSnapshotter;
use riscv_transpiler::vm::SimpleTape;
use riscv_transpiler::vm::State;
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::delegation::bigint::BigintAbiDescription;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionAbiDescription;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionAbiDescription;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5AbiDescription;
use riscv_transpiler::witness::UnifiedDestinationHolder;
use setups::UnrolledCircuitSetupParams;
use setups::UnrolledCircuitWitnessEvalFn;
use std::alloc::Global;
use std::collections::BTreeMap;
use std::collections::HashMap;
use trace_and_split::commit_memory_tree_for_delegation_circuit;
use trace_and_split::commit_memory_tree_for_unified_circuits;
use trace_and_split::fs_transform_unified_for_permutation_argument;

type UnifiedProof = GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>;

/// Replay the captured execution into a single unified-circuit witness buffer.
/// Mirrors `replay_non_mem_circuit_family` from the unrolled example but emits
/// the unified tracing-data layout for the single reduced-machine circuit.
fn replay_unified_circuit<C: Counters>(
    initial_counters: C,
    snapshotter: &SimpleSnapshotter<
        C,
        { common_constants::ROM_SECOND_WORD_BITS },
        Vec<(u32, (u32, u32))>,
    >,
    tape: &SimpleTape,
    cycles_bound: usize,
    capacity_per_circuit: usize,
    expected_final_state: &State<C>,
    num_calls: usize,
) -> Vec<Vec<UnifiedOpcodeTracingDataWithTimestamp>> {
    use riscv_transpiler::replayer::ReplayerRam;
    use riscv_transpiler::replayer::ReplayerVM;
    use riscv_transpiler::vm::ReplayBuffer;

    let mut state = State::initial_with_counters(initial_counters);

    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());

    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    let mut buffers = make_tracer_buffers::<UnifiedOpcodeTracingDataWithTimestamp>(
        UnifiedOpcodeTracingDataWithTimestamp::default(),
        num_calls,
        capacity_per_circuit,
    );
    let mut buffer_ref_mut: Vec<_> = buffers.iter_mut().map(|el| &mut el[..]).collect();
    let mut tracer = UnifiedDestinationHolder {
        buffers: &mut buffer_ref_mut,
    };

    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state.registers, state.registers);
    assert_eq!(expected_final_state.pc, state.pc);
    assert_eq!(expected_final_state.timestamp, state.timestamp);

    dbg!(buffers.len());
    dbg!(buffers[0].len());

    buffers
}

/// Prove an execution with the *unified* reduced-machine circuit: a single GKR
/// circuit that folds every executor family plus its inline inits-and-teardowns,
/// alongside the delegation circuits. This is the unified-mode analogue of
/// [`crate::unrolled::prove_unrolled_execution_with_replayer`]; it follows the
/// same Fiat-Shamir flow (commit memory trees -> derive challenges -> prove) and
/// asserts that the global permutation grand-product closes to ONE.
pub fn prove_unified_execution_with_replayer<A: GoodAllocator>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &worker::Worker,
    security_level: SecurityLevel,
    permutation_argument_pow_bits: u32,
) -> (
    full_statement_verifier::program_proof::ProgramProof,
    BTreeMap<u32, UnrolledCircuitSetupParams>,
) {
    let mut program_proof = full_statement_verifier::program_proof::ProgramProof {
        riscv_proofs: BTreeMap::new(),
        compiled_riscv_circuits: BTreeMap::new(),
        inits_and_teardown_proofs: Vec::new(),
        inits_and_teardowns_circuit: None,
        delegation_proofs: BTreeMap::new(),
        compiled_delegation_circuits: BTreeMap::new(),
        register_final_values: Vec::new(),
        final_pc: 0,
        final_timestamp: 0,
        end_params: [0u32; 8],
        recursion_chain_hash: None,
        recursion_chain_preimage: None,
        pow_challenge: 0,
    };

    let mut risc_v_setup_params = BTreeMap::new();

    type C = ReducedMachineWithDelegation;

    assert!(
        ram_bound <= (1 << 30),
        "Large RAM sizes are not supported for now"
    );

    // Per-delegation circuit capacities (one circuit holds this many calls).
    let mut delegation_chunk_sizes = HashMap::new();
    fn get_delegation_chunk_size<C: circuit_common::DelegationCircuit<BabyBearField>>(
        dst: &mut HashMap<u16, usize>,
    ) {
        assert!(dst
            .insert(C::DELEGATION_TYPE_ID, 1 << C::DOMAIN_SIZE_LOG2)
            .is_none());
    }
    get_delegation_chunk_size::<setups::BigIntDelegationCircuit>(&mut delegation_chunk_sizes);
    get_delegation_chunk_size::<setups::Blake2sWithCompressionDelegationCircuit>(
        &mut delegation_chunk_sizes,
    );
    get_delegation_chunk_size::<setups::KeccakSpecial5DelegationCircuit>(
        &mut delegation_chunk_sizes,
    );
    get_delegation_chunk_size::<setups::Blake2sGFunctionDelegationCircuit>(
        &mut delegation_chunk_sizes,
    );

    // NOTE: same argument swap as the unrolled example: the VM driver consumes
    // (text_section_for_rom, bytecode) while the setups consume
    // (binary_image, text_section).
    let (
        (final_pc, final_timestamp),
        snapshotter,
        counters,
        ram,
        registers,
        tape,
        expected_final_state,
    ) = run_unrolled_machine_in_full::<C, DelegationsAndUnifiedCounters>(
        cycles_bound,
        text_section,
        binary_image,
        ram_bound,
        DelegationsAndUnifiedCounters::default(),
        non_determinism,
    );

    println!(
        "Execution ended at PC = 0x{:08x} at timestamp {}",
        final_pc, final_timestamp
    );
    println!("Final usage: {:?}", &counters);

    // The unified circuit handles all executor cycles in a single circuit.
    let num_unified_calls =
        counters.get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();

    // Replay the trace into the unified witness buffer and each delegation family.
    let unified_buffers = replay_unified_circuit::<DelegationsAndUnifiedCounters>(
        DelegationsAndUnifiedCounters::default(),
        &snapshotter,
        &tape,
        cycles_bound,
        1 << setups::unified_reduced_machine::TRACE_LEN_LOG2,
        &expected_final_state,
        num_unified_calls,
    );

    let blake_circuits = replay_delegation_circuit::<
        DelegationsAndUnifiedCounters,
        Blake2sRoundFunctionAbiDescription,
        _,
        _,
        _,
        _,
    >(
        DelegationsAndUnifiedCounters::default(),
        &snapshotter,
        &tape,
        cycles_bound,
        &expected_final_state,
        delegation_chunk_sizes[&(BLAKE2S_DELEGATION_CSR_REGISTER as u16)],
        counters,
        |c| c.blake_calls,
    );
    let bigint_circuits = replay_delegation_circuit::<
        DelegationsAndUnifiedCounters,
        BigintAbiDescription,
        _,
        _,
        _,
        _,
    >(
        DelegationsAndUnifiedCounters::default(),
        &snapshotter,
        &tape,
        cycles_bound,
        &expected_final_state,
        delegation_chunk_sizes[&(BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16)],
        counters,
        |c| c.bigint_calls,
    );
    let keccak_special5_circuits = replay_delegation_circuit::<
        DelegationsAndUnifiedCounters,
        KeccakSpecial5AbiDescription,
        _,
        _,
        _,
        _,
    >(
        DelegationsAndUnifiedCounters::default(),
        &snapshotter,
        &tape,
        cycles_bound,
        &expected_final_state,
        delegation_chunk_sizes[&(KECCAK_SPECIAL5_CSR_REGISTER as u16)],
        counters,
        |c| c.keccak_calls,
    );
    let blake_g_function_circuits = replay_delegation_circuit::<
        DelegationsAndUnifiedCounters,
        Blake2sGFunctionAbiDescription,
        _,
        _,
        _,
        _,
    >(
        DelegationsAndUnifiedCounters::default(),
        &snapshotter,
        &tape,
        cycles_bound,
        &expected_final_state,
        delegation_chunk_sizes[&(BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16)],
        counters,
        |c| c.blake_g_function_calls,
    );

    // Setups: a single unified circuit plus the delegation circuits.
    let unified_setup = setups::unified_reduced_machine_circuit_setup::<Global>(
        binary_image,
        text_section,
        use_caches,
        worker,
    );

    program_proof.compiled_riscv_circuits.insert(
        REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
        unified_setup.compiled_circuit.clone(),
    );

    let trace_len = unified_setup.trace_len;

    let num_circuits_to_prove = num_unified_calls.div_ceil(trace_len);
    assert_eq!(unified_buffers.len(), num_circuits_to_prove);

    println!(
        "{} RISC-V cycles are proven via {} unified circuit chunks",
        num_unified_calls, num_circuits_to_prove
    );
    let num_teardown_sets = unified_setup
        .compiled_circuit
        .memory_layout
        .teardown_sets
        .len();
    assert!(num_teardown_sets > 0);

    let blake_round_function_setup =
        setups::get_blake2_with_compression_circuit_setup(use_caches, worker);
    let bigint_setup = setups::get_bigint_with_control_circuit_setup(use_caches, worker);
    let keccak_special5_setup = setups::get_keccak_special5_circuit_setup(use_caches, worker);
    let blake_g_function_setup = setups::get_blake2_g_function_circuit_setup(use_caches, worker);

    for el in [
        &blake_round_function_setup,
        &bigint_setup,
        &keccak_special5_setup,
        &blake_g_function_setup,
    ] {
        program_proof
            .compiled_delegation_circuits
            .insert(el.delegation_type as u32, el.compiled_circuit.clone());
    }

    // for unified circuits we have non-trivial splitting of inits and teardowns - only last N circuits out of all
    // `num_circuits_to_prove` will contribute to the grand product, and so we need to compute N. In general it would
    // require us to scan all continuous `setups::unified_reduced_machine::TRACE_LEN_LOG2` * core::mem::size_of::<u32>() byte chunks
    // of RAM to check if any address in those is touched, but we assume to fully control the recursion program
    // (and it's the only one + may be few test ones that will run in such mode), so we know that we will not touch anything above
    // quite low upper bound (and we can update linker script to make this bound even lower)

    let inits_and_teardown_chunks = ram.collect_inits_and_teardowns_sets::<BabyBearField, Global>(
        worker,
        setups::unified_reduced_machine::TRACE_LEN_LOG2 as usize,
        num_teardown_sets,
        Some((1 << 27) / 4), // 128Mb
    );

    assert!(inits_and_teardown_chunks.len() <= num_circuits_to_prove);
    let num_dummy_inits_and_teardowns = num_circuits_to_prove - inits_and_teardown_chunks.len();

    let register_final_state = registers.map(|el| FinalRegisterValue {
        value: el.value,
        last_access_timestamp: el.timestamp,
    });
    program_proof.register_final_values = register_final_state.to_vec();
    program_proof.final_pc = final_pc;
    program_proof.final_timestamp = final_timestamp;

    let mut twiddles = HashMap::new();
    twiddles
        .entry(trace_len)
        .or_insert_with(|| Twiddles::new(trace_len, worker));

    let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);

    // Commit the unified memory tree (which embeds inits/teardowns).
    let mut memory_trees: Vec<(Vec<u32>, prover::merkle_trees::MerkleTreeCapVarLength)> = vec![];
    {
        let twiddles_for_size = &twiddles[&trace_len];
        let UnrolledCircuitWitnessEvalFn::Unified {
            witness_fn,
            decoder_table,
        } = unified_setup.witness_eval_fn.as_ref().unwrap()
        else {
            unreachable!()
        };

        for (i, unified_buffer) in unified_buffers.iter().enumerate() {
            let (top_bits, inits_and_teardowns) = if i >= num_dummy_inits_and_teardowns {
                inits_and_teardown_chunks[i - num_dummy_inits_and_teardowns].clone()
            } else {
                // create zeroes ones
                let mut inits_and_teardowns = Vec::with_capacity(num_teardown_sets);
                for _ in 0..num_teardown_sets {
                    let a = vec![
                        BabyBearField::ZERO;
                        1 << setups::unified_reduced_machine::TRACE_LEN_LOG2
                    ];
                    let b = vec![
                        BabyBearField::ZERO;
                        1 << setups::unified_reduced_machine::TRACE_LEN_LOG2
                    ];
                    let c = vec![
                        BabyBearField::ZERO;
                        1 << setups::unified_reduced_machine::TRACE_LEN_LOG2
                    ];
                    let d = vec![
                        BabyBearField::ZERO;
                        1 << setups::unified_reduced_machine::TRACE_LEN_LOG2
                    ];
                    inits_and_teardowns.push(([a, b], [c, d]));
                }

                (vec![0u32; num_teardown_sets], inits_and_teardowns)
            };
            let cap = commit_memory_tree_for_unified_circuits::<
                BabyBearField,
                DefaultTreeConstructor,
                Global,
                Global,
            >(
                &unified_setup.compiled_circuit,
                unified_buffer,
                inits_and_teardowns,
                text_section,
                twiddles_for_size,
                &prover_config,
                decoder_table,
                worker,
            );
            memory_trees.push((top_bits, cap));
        }
    }

    // Commit delegation memory trees.
    let mut delegation_memory_trees = std::collections::BTreeMap::new();
    {
        type DelegationDescription = Blake2sRoundFunctionAbiDescription;
        let delegation_type = <setups::Blake2sWithCompressionDelegationCircuit as circuit_common::DelegationCircuit<BabyBearField>>::DELEGATION_TYPE_ID;
        let delegation_circuits = &blake_circuits;
        let setup = &blake_round_function_setup;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let twiddles_for_size = twiddles
                .entry(trace_len)
                .or_insert_with(|| Twiddles::new(trace_len, worker));
            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit::<
                    BabyBearField,
                    DefaultTreeConstructor,
                    Global,
                    Global,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &setup.compiled_circuit,
                    el,
                    &*twiddles_for_size,
                    &prover_config,
                    worker,
                );
                per_tree_set.push(caps);
            }
            delegation_memory_trees.insert(delegation_type, per_tree_set);
        }
    }
    {
        type DelegationDescription = BigintAbiDescription;
        let delegation_type = <setups::BigIntDelegationCircuit as circuit_common::DelegationCircuit<
            BabyBearField,
        >>::DELEGATION_TYPE_ID;
        let delegation_circuits = &bigint_circuits;
        let setup = &bigint_setup;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let twiddles_for_size = twiddles
                .entry(trace_len)
                .or_insert_with(|| Twiddles::new(trace_len, worker));
            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit::<
                    BabyBearField,
                    DefaultTreeConstructor,
                    Global,
                    Global,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &setup.compiled_circuit,
                    el,
                    &*twiddles_for_size,
                    &prover_config,
                    worker,
                );
                per_tree_set.push(caps);
            }
            delegation_memory_trees.insert(delegation_type, per_tree_set);
        }
    }
    {
        type DelegationDescription = KeccakSpecial5AbiDescription;
        let delegation_type =
            <setups::KeccakSpecial5DelegationCircuit as circuit_common::DelegationCircuit<
                BabyBearField,
            >>::DELEGATION_TYPE_ID;
        let delegation_circuits = &keccak_special5_circuits;
        let setup = &keccak_special5_setup;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let twiddles_for_size = twiddles
                .entry(trace_len)
                .or_insert_with(|| Twiddles::new(trace_len, worker));
            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit::<
                    BabyBearField,
                    DefaultTreeConstructor,
                    Global,
                    Global,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &setup.compiled_circuit,
                    el,
                    &*twiddles_for_size,
                    &prover_config,
                    worker,
                );
                per_tree_set.push(caps);
            }
            delegation_memory_trees.insert(delegation_type, per_tree_set);
        }
    }
    {
        type DelegationDescription = Blake2sGFunctionAbiDescription;
        let delegation_type =
            <setups::Blake2sGFunctionDelegationCircuit as circuit_common::DelegationCircuit<
                BabyBearField,
            >>::DELEGATION_TYPE_ID;
        let delegation_circuits = &blake_g_function_circuits;
        let setup = &blake_g_function_setup;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let twiddles_for_size = twiddles
                .entry(trace_len)
                .or_insert_with(|| Twiddles::new(trace_len, worker));
            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit::<
                    BabyBearField,
                    DefaultTreeConstructor,
                    Global,
                    Global,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &setup.compiled_circuit,
                    el,
                    &*twiddles_for_size,
                    &prover_config,
                    worker,
                );
                per_tree_set.push(caps);
            }
            delegation_memory_trees.insert(delegation_type, per_tree_set);
        }
    }

    let delegation_memory_trees_vec: Vec<(u32, Vec<prover::merkle_trees::MerkleTreeCapVarLength>)> =
        delegation_memory_trees
            .iter()
            .map(|(k, v)| (*k as u32, v.clone()))
            .collect();

    // Fiat-Shamir over committed trees. Inits and teardowns are inline in the
    // unified circuit, so the dedicated i/t slot is empty.
    let all_challenges_seed = fs_transform_unified_for_permutation_argument::<true>(
        &register_final_state,
        final_pc,
        final_timestamp,
        &memory_trees,
        &delegation_memory_trees_vec,
    );

    let pow_challenge = if permutation_argument_pow_bits > 0 {
        Transcript::search_pow(&all_challenges_seed, permutation_argument_pow_bits, worker).1
    } else {
        0
    };
    program_proof.pow_challenge = pow_challenge;

    let external_challenges =
        GKRExternalChallenges::<BabyBearField, BabyBearExt4>::draw_from_transcript_seed(
            all_challenges_seed,
            permutation_argument_pow_bits as usize,
            pow_challenge,
        );

    let register_final_state_raw =
        register_final_state.map(|el| (el.value, split_timestamp(el.last_access_timestamp)));

    let mut permutation_argument_accumulator =
        produce_initial_permutation_product_contribution::<BabyBearField, BabyBearExt4>(
            &register_final_state_raw,
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            final_pc,
            split_timestamp(final_timestamp),
            &external_challenges,
        );

    let mut aux_memory_trees: Vec<(Vec<u32>, MerkleTreeCapVarLength)> = vec![];
    let mut delegation_proofs_count = 0;

    // Prove the unified circuit.
    let mut unified_proofs = vec![];
    {
        let twiddles_for_size = &twiddles[&trace_len];
        let setup_commitment = unified_setup.setup.commit::<DefaultTreeConstructor>(
            twiddles_for_size,
            prover_config.lde_factor,
            prover_config.whir_schedule.whir_steps_schedule[0],
            prover_config.cap_size,
            trace_len.trailing_zeros() as usize,
            worker,
        );

        risc_v_setup_params.insert(
            REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
            UnrolledCircuitSetupParams {
                family_idx: REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
                capacity: trace_len as u32,
                setup_caps: MerkleTreeCap {
                    cap: <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<
                        BabyBearField,
                    >>::get_cap(&setup_commitment.tree)
                    .cap
                    .try_into()
                    .unwrap(),
                },
            },
        );

        let UnrolledCircuitWitnessEvalFn::Unified {
            witness_fn,
            decoder_table,
        } = unified_setup.witness_eval_fn.as_ref().unwrap()
        else {
            unreachable!()
        };

        let mut inits_and_teardowns_it = inits_and_teardown_chunks.into_iter();

        for (i, unified_buffer) in unified_buffers.into_iter().enumerate() {
            let (top_bits, inits_and_teardowns) = if i >= num_dummy_inits_and_teardowns {
                inits_and_teardowns_it
                    .next()
                    .expect("next inits and teardowns")
            } else {
                // create zeroes ones
                let mut inits_and_teardowns = Vec::with_capacity(num_teardown_sets);
                for _ in 0..num_teardown_sets {
                    let a = vec![
                        BabyBearField::ZERO;
                        1 << setups::unified_reduced_machine::TRACE_LEN_LOG2
                    ];
                    let b = vec![
                        BabyBearField::ZERO;
                        1 << setups::unified_reduced_machine::TRACE_LEN_LOG2
                    ];
                    let c = vec![
                        BabyBearField::ZERO;
                        1 << setups::unified_reduced_machine::TRACE_LEN_LOG2
                    ];
                    let d = vec![
                        BabyBearField::ZERO;
                        1 << setups::unified_reduced_machine::TRACE_LEN_LOG2
                    ];
                    inits_and_teardowns.push(([a, b], [c, d]));
                }

                (vec![0u32; num_teardown_sets], inits_and_teardowns)
            };

            let oracle = UnifiedRiscvCircuitOracle {
                inner: &unified_buffer,
                decoder_table,
            };

            let witness_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
                &unified_setup.compiled_circuit,
                *witness_fn,
                trace_len,
                &oracle,
                &unified_setup.table_driver,
                worker,
                Some(inits_and_teardowns),
                Global,
                Global,
            );

            let now = std::time::Instant::now();
            let proof =
                prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &unified_setup.compiled_circuit,
                    &external_challenges,
                    witness_trace,
                    &unified_setup.setup,
                    &setup_commitment,
                    twiddles_for_size,
                    &prover_config,
                    top_bits.clone(),
                    trace_len,
                    worker,
                );
            println!("Proving time for unified circuit is {:?}", now.elapsed());

            program_proof
                .riscv_proofs
                .entry(REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32)
                .or_default()
                .push(proof.clone());

            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);

            aux_memory_trees.push((
                top_bits,
                proof.whir_proof.memory_commitment.commitment.cap.clone(),
            ));
            unified_proofs.push(proof);
        }

        assert!(inits_and_teardowns_it.next().is_none());
    }

    // Prove the delegation circuits.
    let mut aux_delegation_memory_trees = vec![];
    let mut delegation_proofs = vec![];
    let should_dump_witness = false;
    {
        let delegation_type = <setups::Blake2sWithCompressionDelegationCircuit as circuit_common::DelegationCircuit<BabyBearField>>::DELEGATION_TYPE_ID;
        let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(blake_round_function_setup.trace_len.trailing_zeros() as usize, security_level);
        if blake_circuits.is_empty() == false {
            let (proofs, per_tree_set) =
                prove_delegation_circuit::<Global, Blake2sRoundFunctionAbiDescription, _, _, _, _>(
                    &blake_circuits[..],
                    &external_challenges,
                    &blake_round_function_setup,
                    setups::blake2_with_compression_witness_eval_fn,
                    delegation_type as u16,
                    &mut permutation_argument_accumulator,
                    &mut delegation_proofs_count,
                    should_dump_witness,
                    &mut twiddles,
                    &prover_config,
                    worker,
                );
            program_proof
                .delegation_proofs
                .insert(delegation_type as u32, proofs.clone());
            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type, proofs));
        }
    }
    {
        let delegation_type = <setups::BigIntDelegationCircuit as circuit_common::DelegationCircuit<
            BabyBearField,
        >>::DELEGATION_TYPE_ID;
        let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(bigint_setup.trace_len.trailing_zeros() as usize, security_level);
        if bigint_circuits.is_empty() == false {
            let (proofs, per_tree_set) =
                prove_delegation_circuit::<Global, BigintAbiDescription, _, _, _, _>(
                    &bigint_circuits[..],
                    &external_challenges,
                    &bigint_setup,
                    setups::bigint_witness_eval_fn,
                    delegation_type as u16,
                    &mut permutation_argument_accumulator,
                    &mut delegation_proofs_count,
                    should_dump_witness,
                    &mut twiddles,
                    &prover_config,
                    worker,
                );
            program_proof
                .delegation_proofs
                .insert(delegation_type as u32, proofs.clone());

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type, proofs));
        }
    }
    {
        let delegation_type =
            <setups::KeccakSpecial5DelegationCircuit as circuit_common::DelegationCircuit<
                BabyBearField,
            >>::DELEGATION_TYPE_ID;
        let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(keccak_special5_setup.trace_len.trailing_zeros() as usize, security_level);
        if keccak_special5_circuits.is_empty() == false {
            let (proofs, per_tree_set) =
                prove_delegation_circuit::<Global, KeccakSpecial5AbiDescription, _, _, _, _>(
                    &keccak_special5_circuits[..],
                    &external_challenges,
                    &keccak_special5_setup,
                    setups::keccak_special5_witness_eval_fn,
                    delegation_type as u16,
                    &mut permutation_argument_accumulator,
                    &mut delegation_proofs_count,
                    should_dump_witness,
                    &mut twiddles,
                    &prover_config,
                    worker,
                );
            program_proof
                .delegation_proofs
                .insert(delegation_type as u32, proofs.clone());

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type, proofs));
        }
    }
    {
        let delegation_type =
            <setups::Blake2sGFunctionDelegationCircuit as circuit_common::DelegationCircuit<
                BabyBearField,
            >>::DELEGATION_TYPE_ID;
        let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(blake_g_function_setup.trace_len.trailing_zeros() as usize, security_level);
        if blake_g_function_circuits.is_empty() == false {
            let (proofs, per_tree_set) =
                prove_delegation_circuit::<Global, Blake2sGFunctionAbiDescription, _, _, _, _>(
                    &blake_g_function_circuits[..],
                    &external_challenges,
                    &blake_g_function_setup,
                    setups::blake2_g_function_witness_eval_fn,
                    delegation_type as u16,
                    &mut permutation_argument_accumulator,
                    &mut delegation_proofs_count,
                    should_dump_witness,
                    &mut twiddles,
                    &prover_config,
                    worker,
                );
            program_proof
                .delegation_proofs
                .insert(delegation_type as u32, proofs.clone());

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type, proofs));
        }
    }

    // Sanity: the memory trees committed before deriving challenges must match
    // the ones the prover re-derived, and the grand product must close to ONE.
    assert_eq!(&aux_memory_trees, &memory_trees);
    assert_eq!(&aux_delegation_memory_trees, &delegation_memory_trees_vec);

    let aux_all_challenges_seed = fs_transform_unified_for_permutation_argument::<true>(
        &register_final_state,
        final_pc,
        final_timestamp,
        &aux_memory_trees,
        &aux_delegation_memory_trees,
    );
    assert_eq!(aux_all_challenges_seed, all_challenges_seed);

    assert_eq!(permutation_argument_accumulator, BabyBearExt4::ONE);

    (program_proof, risc_v_setup_params)
}

#[cfg(test)]
pub(crate) mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::bincode_serialize_to_file;
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use std::alloc::Global;
    use std::path::Path;

    #[test]
    #[ignore = "manual heavy proving test"]
    #[serial_test::serial(prover_examples_proof_artifacts)]
    fn test_prove_unified_fibonacci() {
        skip_if_ci!();

        let use_caches = true;
        let (_, binary_image) =
            setups::read_and_pad_binary(&Path::new("../../examples/basic_fibonacci/app.bin"));
        let (_, text_section) =
            setups::read_and_pad_binary(&Path::new("../../examples/basic_fibonacci/app.text"));

        let worker = worker::Worker::new_with_num_threads(8);
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![15, 1]);

        let (program_proof, setups) = prove_unified_execution_with_replayer::<Global>(
            1 << 24,
            &binary_image,
            &text_section,
            use_caches,
            non_determinism_source,
            1 << 30,
            &worker,
            SecurityLevel::Sec80,
            0,
        );

        bincode_serialize_to_file(&program_proof, "tmp_unified_proof.bin");
        let setups: Vec<_> = setups.into_iter().map(|(_, v)| v).collect();
        bincode_serialize_to_file(&setups, "tmp_unified_setup.bin");
    }
}
