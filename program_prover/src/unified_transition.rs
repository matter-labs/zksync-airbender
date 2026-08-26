//! Delegation-free unified proving under `CommitmentMode::MergedMemoryAndWitness`
//! — the "transition"/feeder driver of the L1 recursion tail.
//!
//! Mirrors [`crate::unified::prove_unified_execution_with_replayer`] with three
//! deliberate differences:
//!
//! 1. NO precompiles: the traced program must make zero delegation calls
//!    (asserted on the run's counters). The special-opcodes full-statement
//!    verifiers hash inline, so the final recursion layers are pure unified
//!    circuits.
//! 2. The base commitment is the MERGED memory+witness tree
//!    ([`trace_and_split::commit_merged_tree_for_unified_circuits`] /
//!    `CommitmentMode::MergedMemoryAndWitness`): one Merkle path per round-0
//!    query instead of two, which is what makes verifying these proofs cheap
//!    enough for the L1 wrapper. Committing the merged tree before the
//!    permutation-argument Fiat-Shamir requires the FULL witness, so witness
//!    evaluation happens once for the commit and once inside proving.
//! 3. The unified circuit's [`ProverConfig`] is an EXPLICIT parameter (the
//!    high-LDE "L1 feeder" schedule), and the WHIR oracle storage policy is
//!    caller-chosen: RS/tree RECOMPUTATION on memory-constrained machines
//!    (the feeder LDE factors make materialized codewords large), fully
//!    in-memory on large boxes where recompute dominates the proving time.
//!
//! Proofs made here verify ONLY with the matching merged-mode generated
//! verifier (`.../unified_reduced_machine/sec_100_l1_feeder`).

use crate::unified::replay_unified_circuit;
use crate::unrolled::run_unrolled_machine_in_full;
use common_constants::INITIAL_PC;
use common_constants::INITIAL_TIMESTAMP;
use common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use prover::cs::utils::split_timestamp;
use prover::definitions::produce_initial_permutation_product_contribution;
use prover::definitions::FinalRegisterValue;
use prover::definitions::*;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::baby_bear::ext4::BabyBearExt4;
use prover::field::*;
use prover::gkr::prover::GKRExternalChallenges;
use prover::gkr::prover::{
    prove_configured_with_gkr_with_storage_and_backend, Backend, CommitmentMode, GKRBackend,
    TwiddleSetOps, WhirOracleStorage,
};
use prover::gkr::witness_gen::family_circuits::evaluate_gkr_witness_for_executor_family;
use prover::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use prover::merkle_trees::DefaultTreeConstructor;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::transcript::Blake2sTranscript;
use prover::worker;
use riscv_transpiler::cycle::ReducedMachineWithDelegation;
use riscv_transpiler::vm::Counters;
use riscv_transpiler::vm::DelegationsAndUnifiedCounters;
use setups::UnrolledCircuitSetupParams;
use setups::UnrolledCircuitWitnessEvalFn;
use std::alloc::Global;
use std::collections::BTreeMap;
use std::collections::HashMap;
use trace_and_split::commit_merged_tree_for_unified_circuits;
use trace_and_split::fs_transform_unified_for_permutation_argument;

/// Wall-clock breakdown of one [`prove_unified_transition_with_replayer_timed`]
/// run, so callers (the L1 compression driver) can report setup-commitment
/// work separately from proving work.
#[derive(Clone, Copy, Debug, Default)]
pub struct UnifiedTransitionTimings {
    /// Circuit setup construction (`unified_reduced_machine_circuit_setup`:
    /// compile/caches + table driver + setup hypercube evals).
    pub setup_ms: u128,
    /// Pre-challenge MERGED memory+witness tree commitments (all chunks).
    pub merged_tree_commit_ms: u128,
    /// The setup oracle commitment (`GKRSetup::commit`).
    pub setup_commit_ms: u128,
    /// GKR witness evaluation (all chunks).
    pub witness_eval_ms: u128,
    /// The `prove_configured_*` calls themselves (all chunks).
    pub prove_ms: u128,
}

/// Prove a delegation-free execution as unified circuits committed in
/// `MergedMemoryAndWitness` mode under an explicit (feeder) [`ProverConfig`],
/// with the RECOMPUTATION oracle storage policy (the memory-light default the
/// local research tests use). Panics if the traced program performed ANY
/// delegation call.
#[allow(clippy::too_many_arguments)]
pub fn prove_unified_transition_with_replayer<
    B: Backend<BabyBearField, BabyBearExt4>,
    GB: GKRBackend<BabyBearField, BabyBearExt4>,
>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &worker::Worker,
    security_level: SecurityLevel,
    permutation_argument_pow_bits: u32,
    unified_prover_config: &prover::gkr::prover_config::ProverConfig,
    backend: &B,
    gkr_backend: &GB,
) -> (
    full_statement_verifier::program_proof::ProgramProof,
    BTreeMap<u32, UnrolledCircuitSetupParams>,
) {
    let (proof, setup_params, _timings) = prove_unified_transition_with_replayer_timed(
        cycles_bound,
        binary_image,
        text_section,
        use_caches,
        non_determinism,
        ram_bound,
        worker,
        security_level,
        permutation_argument_pow_bits,
        unified_prover_config,
        WhirOracleStorage::fully_recompute(),
        backend,
        gkr_backend,
    );
    (proof, setup_params)
}

/// [`prove_unified_transition_with_replayer`] with an explicit WHIR oracle
/// storage policy, also returning the wall-clock breakdown of its phases.
#[allow(clippy::too_many_arguments)]
pub fn prove_unified_transition_with_replayer_timed<
    B: Backend<BabyBearField, BabyBearExt4>,
    GB: GKRBackend<BabyBearField, BabyBearExt4>,
>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &worker::Worker,
    security_level: SecurityLevel,
    permutation_argument_pow_bits: u32,
    unified_prover_config: &prover::gkr::prover_config::ProverConfig,
    whir_oracle_storage: WhirOracleStorage,
    backend: &B,
    gkr_backend: &GB,
) -> (
    full_statement_verifier::program_proof::ProgramProof,
    BTreeMap<u32, UnrolledCircuitSetupParams>,
    UnifiedTransitionTimings,
) {
    let mut timings = UnifiedTransitionTimings::default();
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
        num_it_circuits: None,
    };

    let mut risc_v_setup_params = BTreeMap::new();

    type C = ReducedMachineWithDelegation;

    assert!(
        ram_bound <= (1 << 30),
        "Large RAM sizes are not supported for now"
    );

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
        binary_image,
        text_section,
        ram_bound,
        DelegationsAndUnifiedCounters::default(),
        non_determinism,
    );

    println!(
        "Execution ended at PC = 0x{:08x} at timestamp {}",
        final_pc, final_timestamp
    );
    println!("Final usage: {:?}", &counters);

    // The transition layers are strictly delegation-free (the special-opcodes
    // verifiers hash inline) — a single delegation call would make the
    // permutation argument unsatisfiable here.
    assert_eq!(counters.blake_calls, 0, "no blake delegations allowed");
    assert_eq!(counters.bigint_calls, 0, "no bigint delegations allowed");
    assert_eq!(counters.keccak_calls, 0, "no keccak delegations allowed");
    assert_eq!(
        counters.blake_g_function_calls, 0,
        "no blake-g delegations allowed"
    );

    let num_unified_calls =
        counters.get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    let trace_len_log2 = <setups::unified_reduced_machine::UnifiedReducedMachineCircuit as circuit_common::RiscVCycleCircuit<BabyBearField, true>>::DOMAIN_SIZE_LOG2;

    let unified_buffers = replay_unified_circuit::<DelegationsAndUnifiedCounters>(
        DelegationsAndUnifiedCounters::default(),
        &snapshotter,
        &tape,
        cycles_bound,
        1 << trace_len_log2,
        &expected_final_state,
        num_unified_calls,
    );

    let setup_started = std::time::Instant::now();
    let unified_setup = setups::unified_reduced_machine_circuit_setup::<Global>(
        binary_image,
        text_section,
        use_caches,
        worker,
    );
    timings.setup_ms = setup_started.elapsed().as_millis();

    program_proof.compiled_riscv_circuits.insert(
        REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
        unified_setup.compiled_circuit.clone(),
    );

    let trace_len = unified_setup.trace_len;
    assert_eq!(
        unified_prover_config.trace_len_log2,
        trace_len.trailing_zeros() as usize
    );

    let num_circuits_to_prove = num_unified_calls.div_ceil(trace_len);
    assert_eq!(unified_buffers.len(), num_circuits_to_prove);

    println!(
        "{} RISC-V cycles are proven via {} unified circuit chunks (merged commitment)",
        num_unified_calls, num_circuits_to_prove
    );
    let num_teardown_sets = unified_setup
        .compiled_circuit
        .memory_layout
        .teardown_sets
        .len();
    assert!(num_teardown_sets > 0);

    let inits_and_teardown_chunks = ram.collect_inits_and_teardowns_sets::<BabyBearField, Global>(
        worker,
        trace_len_log2 as usize,
        num_teardown_sets,
        Some((1 << 27) / 4), // 128Mb
    );

    program_proof.num_it_circuits = Some(inits_and_teardown_chunks.len() as u32);

    assert!(inits_and_teardown_chunks.len() <= num_circuits_to_prove);
    let num_dummy_inits_and_teardowns = num_circuits_to_prove - inits_and_teardown_chunks.len();

    let register_final_state = registers.map(|el| FinalRegisterValue {
        value: el.value,
        last_access_timestamp: el.timestamp,
    });
    program_proof.register_final_values = register_final_state.to_vec();
    program_proof.final_pc = final_pc;
    program_proof.final_timestamp = final_timestamp;

    let mut twiddles: HashMap<usize, B::TwiddleSet> = HashMap::new();
    twiddles
        .entry(trace_len)
        .or_insert_with(|| backend.make_twiddles(trace_len, worker));

    let prover_config = unified_prover_config.clone();
    assert_eq!(prover_config.security_level, security_level);

    let zero_inits_and_teardowns = |num_sets: usize| -> (Vec<u32>, Vec<_>) {
        let mut inits_and_teardowns = Vec::with_capacity(num_sets);
        for _ in 0..num_sets {
            let a = vec![BabyBearField::ZERO; 1 << trace_len_log2];
            let b = vec![BabyBearField::ZERO; 1 << trace_len_log2];
            let c = vec![BabyBearField::ZERO; 1 << trace_len_log2];
            let d = vec![BabyBearField::ZERO; 1 << trace_len_log2];
            inits_and_teardowns.push(([a, b], [c, d]));
        }
        (vec![0u32; num_sets], inits_and_teardowns)
    };

    // Commit the MERGED memory+witness tree of every chunk before drawing the
    // permutation-argument challenges (the merged cap plays the "memory cap"
    // role of the separate-mode flow).
    let mut memory_trees: Vec<(Vec<u32>, MerkleTreeCapVarLength)> = vec![];
    let merged_commit_started = std::time::Instant::now();
    {
        let twiddles_for_size = &twiddles[&trace_len];
        for (i, unified_buffer) in unified_buffers.iter().enumerate() {
            let (top_bits, inits_and_teardowns) = if i >= num_dummy_inits_and_teardowns {
                inits_and_teardown_chunks[i - num_dummy_inits_and_teardowns].clone()
            } else {
                zero_inits_and_teardowns(num_teardown_sets)
            };
            let cap = commit_merged_tree_for_unified_circuits::<
                BabyBearExt4,
                DefaultTreeConstructor,
                Global,
                _,
            >(
                backend,
                &unified_setup,
                unified_buffer,
                inits_and_teardowns,
                twiddles_for_size,
                &prover_config,
                worker,
            );
            memory_trees.push((top_bits, cap));
        }
    }
    timings.merged_tree_commit_ms = merged_commit_started.elapsed().as_millis();

    // Fiat-Shamir over the committed merged trees; no delegation circuits.
    let all_challenges_seed = fs_transform_unified_for_permutation_argument::<true>(
        &register_final_state,
        final_pc,
        final_timestamp,
        &memory_trees,
        &[],
    );

    let pow_challenge = if permutation_argument_pow_bits > 0 {
        Blake2sTranscript::<true>::search_pow(
            &all_challenges_seed,
            permutation_argument_pow_bits,
            worker,
        )
        .1
    } else {
        0
    };
    program_proof.pow_challenge = pow_challenge;

    let external_challenges =
        GKRExternalChallenges::<BabyBearField, BabyBearExt4>::draw_from_blake_transcript_seed(
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

    // Prove every unified chunk in MERGED mode under the feeder config, with
    // RS codewords and trees served per the caller's storage policy
    // (recompute on memory-constrained machines, in-memory on large ones).
    {
        let twiddles_for_size = &twiddles[&trace_len];
        // GKRSetup::commit runs on the naive backend internally and consumes
        // only the plain radix-2 tables (not performance-sensitive).
        let setup_commit_started = std::time::Instant::now();
        let setup_commitment = unified_setup.setup.commit::<DefaultTreeConstructor>(
            twiddles_for_size.plain(),
            prover_config.lde_factor,
            prover_config.whir_schedule.whir_steps_schedule[0],
            prover_config.cap_size,
            trace_len.trailing_zeros() as usize,
            worker,
        );
        timings.setup_commit_ms = setup_commit_started.elapsed().as_millis();

        risc_v_setup_params.insert(
            REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
            UnrolledCircuitSetupParams::from_setup_tree_cap(
                REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
                trace_len as u32,
                setup_commitment.get_cap(),
            ),
        );

        let Some(UnrolledCircuitWitnessEvalFn::Unified {
            witness_fn,
            decoder_table,
        }) = unified_setup.witness_eval_fn.as_ref()
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
                zero_inits_and_teardowns(num_teardown_sets)
            };

            let oracle = UnifiedRiscvCircuitOracle {
                inner: &unified_buffer,
                decoder_table,
            };

            let witness_eval_started = std::time::Instant::now();
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
            timings.witness_eval_ms += witness_eval_started.elapsed().as_millis();

            let now = std::time::Instant::now();
            let proof = prove_configured_with_gkr_with_storage_and_backend::<
                BabyBearField,
                BabyBearExt4,
                DefaultTreeConstructor,
                Blake2sTranscript,
                _,
                _,
            >(
                &unified_setup.compiled_circuit,
                &external_challenges,
                witness_trace,
                &unified_setup.setup,
                &setup_commitment,
                twiddles_for_size,
                &prover_config,
                CommitmentMode::MergedMemoryAndWitness,
                whir_oracle_storage,
                top_bits.clone(),
                trace_len,
                backend,
                gkr_backend,
                worker,
            );
            timings.prove_ms += now.elapsed().as_millis();
            println!(
                "Proving time for unified transition circuit is {:?}",
                now.elapsed()
            );

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
        }

        assert!(inits_and_teardowns_it.next().is_none());
    }

    // The merged caps committed before drawing challenges must match the ones
    // the prover re-derived, the re-derived FS seed must match, and the global
    // permutation grand-product must close to ONE.
    assert_eq!(&aux_memory_trees, &memory_trees);

    let aux_all_challenges_seed = fs_transform_unified_for_permutation_argument::<true>(
        &register_final_state,
        final_pc,
        final_timestamp,
        &aux_memory_trees,
        &[],
    );
    assert_eq!(aux_all_challenges_seed, all_challenges_seed);

    assert_eq!(permutation_argument_accumulator, BabyBearExt4::ONE);

    println!(
        "[timing] transition: circuit setup {}s | merged tree commits {}s | setup commit {}s | \
         witness eval {}s | proving {}s",
        timings.setup_ms / 1000,
        timings.merged_tree_commit_ms / 1000,
        timings.setup_commit_ms / 1000,
        timings.witness_eval_ms / 1000,
        timings.prove_ms / 1000,
    );

    (program_proof, risc_v_setup_params, timings)
}

/// [`prove_unified_transition_with_replayer_timed`] for large machines: the
/// pre-challenge merged commitments KEEP their evaluated witness traces and
/// in-memory merged oracles (via
/// [`trace_and_split::commit_merged_tree_and_witness_for_unified_circuits`]),
/// and the proving loop CONSUMES them through
/// `prove_configured_with_gkr_merged_with_precommitted_oracle` — so witness
/// evaluation and the merged commitment happen exactly once per chunk instead
/// of twice. Implies the fully in-memory oracle storage policy; all chunks'
/// oracles are held in RAM simultaneously (~(mem+wit columns) * trace_len *
/// lde_factor field elements each).
///
/// In the returned timings `merged_tree_commit_ms` covers the combined
/// witness-evaluation + commitment pass (`witness_eval_ms` stays 0 — there is
/// no separate evaluation any more).
#[allow(clippy::too_many_arguments)]
pub fn prove_unified_transition_with_replayer_precommitted_timed<
    B: Backend<BabyBearField, BabyBearExt4>,
    GB: GKRBackend<BabyBearField, BabyBearExt4>,
>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &worker::Worker,
    security_level: SecurityLevel,
    permutation_argument_pow_bits: u32,
    unified_prover_config: &prover::gkr::prover_config::ProverConfig,
    // WHIR oracle storage for the proofs; the base source must be
    // `RsCodewordSource::InMemory` (the whole point of this path is consuming
    // the precommitted in-memory merged oracles), the intermediate-oracle
    // mode is the caller's choice.
    storage: WhirOracleStorage,
    backend: &B,
    gkr_backend: &GB,
) -> (
    full_statement_verifier::program_proof::ProgramProof,
    BTreeMap<u32, UnrolledCircuitSetupParams>,
    UnifiedTransitionTimings,
) {
    use prover::gkr::prover::prove_configured_with_gkr_merged_with_precommitted_oracle;
    use prover::gkr::whir::ColumnMajorBaseOracleForLDE;
    use prover::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
    use trace_and_split::commit_merged_tree_and_witness_for_unified_circuits;

    let mut timings = UnifiedTransitionTimings::default();
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
        num_it_circuits: None,
    };

    let mut risc_v_setup_params = BTreeMap::new();

    type C = ReducedMachineWithDelegation;

    assert!(
        ram_bound <= (1 << 30),
        "Large RAM sizes are not supported for now"
    );

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
        binary_image,
        text_section,
        ram_bound,
        DelegationsAndUnifiedCounters::default(),
        non_determinism,
    );

    println!(
        "Execution ended at PC = 0x{:08x} at timestamp {}",
        final_pc, final_timestamp
    );
    println!("Final usage: {:?}", &counters);

    // The transition layers are strictly delegation-free (the special-opcodes
    // verifiers hash inline) — a single delegation call would make the
    // permutation argument unsatisfiable here.
    assert_eq!(counters.blake_calls, 0, "no blake delegations allowed");
    assert_eq!(counters.bigint_calls, 0, "no bigint delegations allowed");
    assert_eq!(counters.keccak_calls, 0, "no keccak delegations allowed");
    assert_eq!(
        counters.blake_g_function_calls, 0,
        "no blake-g delegations allowed"
    );

    let num_unified_calls =
        counters.get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    let trace_len_log2 = <setups::unified_reduced_machine::UnifiedReducedMachineCircuit as circuit_common::RiscVCycleCircuit<BabyBearField, true>>::DOMAIN_SIZE_LOG2;

    let unified_buffers = replay_unified_circuit::<DelegationsAndUnifiedCounters>(
        DelegationsAndUnifiedCounters::default(),
        &snapshotter,
        &tape,
        cycles_bound,
        1 << trace_len_log2,
        &expected_final_state,
        num_unified_calls,
    );

    let setup_started = std::time::Instant::now();
    let unified_setup = setups::unified_reduced_machine_circuit_setup::<Global>(
        binary_image,
        text_section,
        use_caches,
        worker,
    );
    timings.setup_ms = setup_started.elapsed().as_millis();

    program_proof.compiled_riscv_circuits.insert(
        REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
        unified_setup.compiled_circuit.clone(),
    );

    let trace_len = unified_setup.trace_len;
    assert_eq!(
        unified_prover_config.trace_len_log2,
        trace_len.trailing_zeros() as usize
    );

    let num_circuits_to_prove = num_unified_calls.div_ceil(trace_len);
    assert_eq!(unified_buffers.len(), num_circuits_to_prove);

    println!(
        "{} RISC-V cycles are proven via {} unified circuit chunks (merged commitment, precommitted oracles)",
        num_unified_calls, num_circuits_to_prove
    );
    let num_teardown_sets = unified_setup
        .compiled_circuit
        .memory_layout
        .teardown_sets
        .len();
    assert!(num_teardown_sets > 0);

    let inits_and_teardown_chunks = ram.collect_inits_and_teardowns_sets::<BabyBearField, Global>(
        worker,
        trace_len_log2 as usize,
        num_teardown_sets,
        Some((1 << 27) / 4), // 128Mb
    );

    program_proof.num_it_circuits = Some(inits_and_teardown_chunks.len() as u32);

    assert!(inits_and_teardown_chunks.len() <= num_circuits_to_prove);
    let num_dummy_inits_and_teardowns = num_circuits_to_prove - inits_and_teardown_chunks.len();

    let register_final_state = registers.map(|el| FinalRegisterValue {
        value: el.value,
        last_access_timestamp: el.timestamp,
    });
    program_proof.register_final_values = register_final_state.to_vec();
    program_proof.final_pc = final_pc;
    program_proof.final_timestamp = final_timestamp;

    let mut twiddles: HashMap<usize, B::TwiddleSet> = HashMap::new();
    twiddles
        .entry(trace_len)
        .or_insert_with(|| backend.make_twiddles(trace_len, worker));

    let prover_config = unified_prover_config.clone();
    assert_eq!(prover_config.security_level, security_level);

    let zero_inits_and_teardowns = |num_sets: usize| -> (Vec<u32>, Vec<_>) {
        let mut inits_and_teardowns = Vec::with_capacity(num_sets);
        for _ in 0..num_sets {
            let a = vec![BabyBearField::ZERO; 1 << trace_len_log2];
            let b = vec![BabyBearField::ZERO; 1 << trace_len_log2];
            let c = vec![BabyBearField::ZERO; 1 << trace_len_log2];
            let d = vec![BabyBearField::ZERO; 1 << trace_len_log2];
            inits_and_teardowns.push(([a, b], [c, d]));
        }
        (vec![0u32; num_sets], inits_and_teardowns)
    };

    // Commit the MERGED memory+witness tree of every chunk before drawing the
    // permutation-argument challenges, KEEPING the evaluated witness and the
    // committed in-memory oracle for the proving loop below (this is the whole
    // point of this variant: no second witness evaluation, no re-commitment).
    let mut memory_trees: Vec<(Vec<u32>, MerkleTreeCapVarLength)> = vec![];
    let mut precommitted: Vec<(
        Vec<u32>,
        GKRFullWitnessTrace<BabyBearField, Global, Global>,
        ColumnMajorBaseOracleForLDE<BabyBearField, DefaultTreeConstructor>,
    )> = Vec::with_capacity(num_circuits_to_prove);
    let merged_commit_started = std::time::Instant::now();
    {
        let twiddles_for_size = &twiddles[&trace_len];
        let mut inits_and_teardowns_it = inits_and_teardown_chunks.into_iter();
        for (i, unified_buffer) in unified_buffers.iter().enumerate() {
            let (top_bits, inits_and_teardowns) = if i >= num_dummy_inits_and_teardowns {
                inits_and_teardowns_it
                    .next()
                    .expect("next inits and teardowns")
            } else {
                zero_inits_and_teardowns(num_teardown_sets)
            };
            let (witness_trace, merged_oracle) =
                commit_merged_tree_and_witness_for_unified_circuits::<
                    BabyBearExt4,
                    DefaultTreeConstructor,
                    Global,
                    _,
                >(
                    backend,
                    &unified_setup,
                    unified_buffer,
                    inits_and_teardowns,
                    twiddles_for_size,
                    &prover_config,
                    worker,
                );
            memory_trees.push((top_bits.clone(), merged_oracle.get_cap()));
            precommitted.push((top_bits, witness_trace, merged_oracle));
        }
        assert!(inits_and_teardowns_it.next().is_none());
    }
    timings.merged_tree_commit_ms = merged_commit_started.elapsed().as_millis();

    // Fiat-Shamir over the committed merged trees; no delegation circuits.
    let all_challenges_seed = fs_transform_unified_for_permutation_argument::<true>(
        &register_final_state,
        final_pc,
        final_timestamp,
        &memory_trees,
        &[],
    );

    let pow_challenge = if permutation_argument_pow_bits > 0 {
        Blake2sTranscript::<true>::search_pow(
            &all_challenges_seed,
            permutation_argument_pow_bits,
            worker,
        )
        .1
    } else {
        0
    };
    program_proof.pow_challenge = pow_challenge;

    let external_challenges =
        GKRExternalChallenges::<BabyBearField, BabyBearExt4>::draw_from_blake_transcript_seed(
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

    // Prove every unified chunk in MERGED mode, consuming the precommitted
    // witness trace and merged oracle of each chunk (no cloning).
    {
        let twiddles_for_size = &twiddles[&trace_len];
        // GKRSetup::commit runs on the naive backend internally and consumes
        // only the plain radix-2 tables (not performance-sensitive).
        let setup_commit_started = std::time::Instant::now();
        let setup_commitment = unified_setup.setup.commit::<DefaultTreeConstructor>(
            twiddles_for_size.plain(),
            prover_config.lde_factor,
            prover_config.whir_schedule.whir_steps_schedule[0],
            prover_config.cap_size,
            trace_len.trailing_zeros() as usize,
            worker,
        );
        timings.setup_commit_ms = setup_commit_started.elapsed().as_millis();

        risc_v_setup_params.insert(
            REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
            UnrolledCircuitSetupParams::from_setup_tree_cap(
                REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32,
                trace_len as u32,
                setup_commitment.get_cap(),
            ),
        );

        for (top_bits, witness_trace, merged_oracle) in precommitted.into_iter() {
            let now = std::time::Instant::now();
            let proof = prove_configured_with_gkr_merged_with_precommitted_oracle::<
                BabyBearField,
                BabyBearExt4,
                DefaultTreeConstructor,
                Blake2sTranscript,
                _,
                _,
            >(
                &unified_setup.compiled_circuit,
                &external_challenges,
                witness_trace,
                merged_oracle,
                &unified_setup.setup,
                &setup_commitment,
                twiddles_for_size,
                &prover_config,
                CommitmentMode::MergedMemoryAndWitness,
                storage,
                top_bits.clone(),
                trace_len,
                backend,
                gkr_backend,
                worker,
            );
            timings.prove_ms += now.elapsed().as_millis();
            println!(
                "Proving time for unified transition circuit is {:?}",
                now.elapsed()
            );

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
        }
    }

    // The merged caps committed before drawing challenges must match the ones
    // the prover carried through, the re-derived FS seed must match, and the
    // global permutation grand-product must close to ONE.
    assert_eq!(&aux_memory_trees, &memory_trees);

    let aux_all_challenges_seed = fs_transform_unified_for_permutation_argument::<true>(
        &register_final_state,
        final_pc,
        final_timestamp,
        &aux_memory_trees,
        &[],
    );
    assert_eq!(aux_all_challenges_seed, all_challenges_seed);

    assert_eq!(permutation_argument_accumulator, BabyBearExt4::ONE);

    println!(
        "[timing] transition (precommitted): circuit setup {}s | witness eval + merged tree \
         commits {}s | setup commit {}s | proving {}s",
        timings.setup_ms / 1000,
        timings.merged_tree_commit_ms / 1000,
        timings.setup_commit_ms / 1000,
        timings.prove_ms / 1000,
    );

    (program_proof, risc_v_setup_params, timings)
}
