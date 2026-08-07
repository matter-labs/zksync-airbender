//! Packed-commitment exploration test.
//!
//! Runs the plain `basic_fibonacci` program (reduced machine, no oracles, no
//! precompiles) and TRIES to prove one unified-circuit instance with the packed
//! commitment mode
//! [`CommitmentMode::MergedAndPackedMemoryAndWitness`](crate::gkr::prover::CommitmentMode).
//!
//! Notes vs the full `unified_circuit.rs` flow:
//!   * precompiles are DISABLED at preprocessing — the supported-CSR set passed to
//!     `process_binary_into_separate_tables_ext` contains only the non-determinism
//!     CSR (no delegation CSRs), so no delegation family is produced;
//!   * external challenges are the hardcoded ones (no Fiat-Shamir memory transcript);
//!   * the twiddles handed to the proof function are of the UNIFIED CIRCUIT SIZE
//!     `<< pack_log2` (the packed commitment interpolates over the enlarged domain),
//!     while the setup commitment uses ordinary trace-sized twiddles.

use super::orchestration::common::{
    run_vm_and_capture, ProgramConfig, VmRunOutput, NUM_CYCLES_PER_CHUNK,
};
use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::definitions::FinalRegisterValue;
use crate::definitions::SecurityLevel;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::CommitmentMode;
use crate::gkr::prover::WhirSchedule;
use crate::gkr::prover_config::ProverConfig;
use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use crate::gkr::witness_gen::family_circuits::{
    build_unified_table_driver, evaluate_gkr_witness_for_executor_family, GKRFullWitnessTrace,
};
use crate::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;
use crate::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use crate::merkle_trees::DefaultTreeConstructor;
use crate::tests::gkr::bincode_serialize_to_file;
use crate::tests::gkr::orchestration::common::dummy_external_challenges;
use crate::tests::gkr::serialize_to_file;
use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use cs::gkr_circuits::{
    process_binary_into_separate_tables_ext, ExecutorFamilyDecoderData, OpcodeFamilyDecoder,
    UnifiedReducedMachineDecoder,
};
use cs::tables::TableDriver;
use fft::Twiddles;
use field::{PrimeField, Proth120};
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{Counters, DelegationsAndUnifiedCounters, ReplayBuffer};
use riscv_transpiler::witness::data_structs::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::UnifiedDestinationHolder;
use std::alloc::Global;
use transcript::{Blake2sTranscript, Keccak256Transcript};
use worker::Worker;

/// `basic_fibonacci`: computes the 10th fibonacci number, uses no oracles and no
/// delegations (reduced-machine ASM), so nothing exercises a precompile CSR.
fn basic_fibonacci_config() -> ProgramConfig {
    ProgramConfig {
        binary_path: "../examples/basic_fibonacci/app.bin".to_string(),
        text_section_path: "../examples/basic_fibonacci/app.text".to_string(),
        // no non-determinism oracle reads
        non_determinism_reads: vec![],
        cycles_bound: 1 << 20,
        ram_bound_bytes: 1 << 30,
    }
}

/// `circuit_tester`: some hand crafted program for testing, uses no oracles and no
/// delegations (reduced-machine ASM), so nothing exercises a precompile CSR.
fn circuit_tester_config() -> ProgramConfig {
    ProgramConfig {
        binary_path: "../examples/circuit_tester/app.bin".to_string(),
        text_section_path: "../examples/circuit_tester/app.text".to_string(),
        // no non-determinism oracle reads
        non_determinism_reads: vec![],
        cycles_bound: 1 << 20,
        ram_bound_bytes: 1 << 30,
    }
}

const TRACE_LEN_LOG2: usize = 22;

/// Load the serialized `CommitmentMode` aux data and build the transcript prefix the packed
/// prover now prepends before the top-bits/caps: the 32 register final states as
/// (value, ts_low, ts_high) u32 triples, then (final_pc, final_ts_low, final_ts_high).
/// Returns (prefix_u32, register_final_state, final_pc, final_timestamp, external_pow_bits).
fn load_boundary_transcript_prefix() -> (
    Vec<u32>,
    [crate::definitions::FinalRegisterValue; 32],
    u32,
    common_constants::TimestampScalar,
    u32,
) {
    use crate::cs::definitions::split_timestamp;
    let aux: CommitmentMode = {
        let src =
            std::fs::File::open("unified_circuit_proof_proth120_commitment_mod_aux_data.json")
                .expect("aux data — run gkr_unified_packed_commitment_basic_fibonacci first");
        serde_json::from_reader(src).expect("deserialize CommitmentMode aux data")
    };
    let CommitmentMode::MergedAndPackedMemoryAndWitness {
        register_final_state,
        final_pc,
        final_timestamp,
        external_challenges_pow_bits,
        ..
    } = aux
    else {
        panic!("aux data must be MergedAndPackedMemoryAndWitness");
    };
    let mut prefix = Vec::with_capacity(32 * 3 + 3);
    for reg in register_final_state.iter() {
        let (ts_low, ts_high) = split_timestamp(reg.last_access_timestamp);
        prefix.push(reg.value);
        prefix.push(ts_low);
        prefix.push(ts_high);
    }
    let (final_ts_low, final_ts_high) = split_timestamp(final_timestamp);
    prefix.push(final_pc);
    prefix.push(final_ts_low);
    prefix.push(final_ts_high);
    (
        prefix,
        register_final_state,
        final_pc,
        final_timestamp,
        external_challenges_pow_bits,
    )
}

#[test]
fn gkr_unified_packed_commitment_basic_fibonacci() {
    let worker = Worker::new_with_num_threads(8);
    let level = SecurityLevel::Sec100;
    // With `pack_log2 = 4` the 2^22 base trace is packed into a single 2^26-variate
    // multilinear per column — exactly the `message_log2 = 26` of the EVM-production
    // WHIR config (`generate_whir_input_for_evm_production`), whose parameters we
    // reuse below.
    let pack_log2 = 4usize;
    let external_challenges_pow_bits = 20u32;

    // 1. Run the plain program (reduced machine, no precompiles).
    // let config = basic_fibonacci_config();
    let config = circuit_tester_config();
    let vm = run_vm_and_capture::<DelegationsAndUnifiedCounters, ReducedMachineDecoderConfig>(
        &config, &worker,
    );
    println!("Finished at PC = 0x{:08x}", vm.final_pc());

    // 2. Load the unified reduced-machine circuit.
    let unified_circuit: GKRCircuitArtifact<Proth120> = {
        let src = std::fs::File::open(
            "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
        )
        .expect("unified circuit layout");
        serde_json::from_reader(src).expect("deserialize unified circuit")
    };
    let num_teardown_sets = unified_circuit.memory_layout.teardown_sets.len();
    let num_calls = vm
        .counters
        .get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    assert!(num_calls <= (1 << TRACE_LEN_LOG2));

    // 3. Build the unified witness trace with precompiles disabled at preprocessing.
    let (full_trace, table_driver, decoder_table, top_bits) =
        build_unified_trace_without_precompiles(
            &vm,
            super::unified_reduced_machine_proth120::witness_eval_fn,
            &unified_circuit,
            num_teardown_sets,
            1 << TRACE_LEN_LOG2,
            &worker,
        );

    // ── DIAGNOSTIC: witness-level permutation self-check (family_circuits.rs style) ──
    // Extract the state (PC/ts) and shuffle-RAM permutation sets straight from the built
    // witness + the register/PC boundary, and check they reduce to identity. If they do,
    // the witness is consistent and any prover self-check divergence is in the accumulator
    // arithmetic, not the trace itself.
    {
        use crate::gkr::witness_gen::family_circuits::GKRMemoryOnlyWitnessTrace;
        use common_constants::{TimestampScalar, INITIAL_PC};
        use cs::definitions::INITIAL_TIMESTAMP;
        use std::collections::BTreeSet;

        let memory_trace = GKRMemoryOnlyWitnessTrace {
            column_major_trace: full_trace.column_major_memory_trace.clone(),
        };
        let register_final_state = vm.register_final_state();
        let final_pc = vm.final_pc();
        let final_timestamp = vm.final_timestamp();
        let flattened_inits_and_teardowns: Vec<_> = vm
            .shuffle_ram_touched_addresses
            .iter()
            .flatten()
            .cloned()
            .collect();

        let mut write_set = BTreeSet::<(u32, TimestampScalar)>::new();
        let mut read_set = BTreeSet::<(u32, TimestampScalar)>::new();
        write_set.insert((INITIAL_PC, INITIAL_TIMESTAMP));
        read_set.insert((final_pc, final_timestamp));

        let mut memory_write_set = BTreeSet::<(bool, u32, TimestampScalar, u32)>::new();
        let mut memory_read_set = BTreeSet::<(bool, u32, TimestampScalar, u32)>::new();
        let mut delegation_write_set = BTreeSet::<(bool, u32, TimestampScalar)>::new();
        for i in 0..32 {
            memory_write_set.insert((true, i as u32, 0, 0));
            memory_read_set.insert((
                true,
                i as u32,
                register_final_state[i].last_access_timestamp,
                register_final_state[i].current_value,
            ));
        }

        super::parse_state_permutation_elements_from_full_trace(
            &unified_circuit,
            &memory_trace,
            &mut write_set,
            &mut read_set,
        );
        super::parse_shuffle_ram_accesses_from_full_trace(
            &unified_circuit,
            &memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_write_set,
        );

        let state_ok = write_set == read_set;
        let init_diff: Vec<_> = memory_read_set
            .difference(&memory_write_set)
            .cloned()
            .collect();
        let teardown_diff: Vec<_> = memory_write_set
            .difference(&memory_read_set)
            .cloned()
            .collect();
        let mem_init_ok = init_diff
            .iter()
            .all(|(is_reg, _, ts, val)| !*is_reg && *ts == 0 && *val == 0);
        println!(
            "[witness-check] STATE write==read: {state_ok}   |w|={} |r|={}",
            write_set.len(),
            read_set.len()
        );
        println!(
            "[witness-check] MEMORY init_diff={} teardown_diff={} flattened_it={}  inits_all(mem,ts=0,val=0)={mem_init_ok}",
            init_diff.len(),
            teardown_diff.len(),
            flattened_inits_and_teardowns.len()
        );
        println!(
            "[witness-check] DELEGATION write_set len={}",
            delegation_write_set.len()
        );
        if !state_ok {
            let w_only: Vec<_> = write_set.difference(&read_set).take(8).cloned().collect();
            let r_only: Vec<_> = read_set.difference(&write_set).take(8).cloned().collect();
            println!("[witness-check] STATE write-only (first 8): {:?}", w_only);
            println!("[witness-check] STATE read-only  (first 8): {:?}", r_only);
        }
        if teardown_diff.len() <= 8 {
            println!("[witness-check] MEMORY teardown_diff: {:?}", teardown_diff);
        }
        assert!(state_ok, "witness state permutation is NOT identity");
        assert_eq!(
            init_diff.len(),
            teardown_diff.len(),
            "witness memory permutation unbalanced"
        );
        assert!(
            mem_init_ok,
            "witness memory inits are not (mem, ts=0, val=0)"
        );
        println!("[witness-check] witness permutation is IDENTITY — proceeding to prove");
    }

    println!("Preparing data for proving");
    // 4. Prover config for a 2^22 base trace, but with the WHIR schedule taken from
    //    the EVM-production generator (`generate_whir_input_for_evm_production`,
    //    message 2^26). Because `pack_log2 = 4` enlarges each column to 2^26 the
    //    packed polynomials match that message size exactly, so the same folds /
    //    queries / lde_factors / pow schedule applies. base LDE 2^5 => 2^31 codeword.
    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let prover_config = ProverConfig {
        lde_factor: 1 << 5, // base LDE factor 32 (base_lde_log2 = 5)
        cap_size: 8,
        // round-0 values-per-leaf = 2^whir_steps_schedule[0] = 2^2
        base_oracles_values_per_leaf: 1 << 2,
        // final poly has 2^(26 - 22) = 2^4 monomials
        sumcheck_explicit_output_size_log_2: 4,
        security_level: level,
        whir_schedule: WhirSchedule {
            base_lde_factor: 1 << 5,
            cap_size: 8,
            whir_steps_schedule: vec![2, 4, 4, 4, 4, 4],
            whir_queries_schedule: vec![17, 12, 8, 6, 5, 4],
            whir_steps_lde_factors: vec![1 << 7, 1 << 11, 1 << 15, 1 << 19, 1 << 23],
            whir_pow_schedule: vec![30, 30, 27, 25, 21, 24],
        },
    };

    println!("Computing setup");
    // The proof function's twiddles are of unified circuit size * (1 << pack_log2):
    // the packed commitment interpolates the merged/packed polynomials over the
    // enlarged domain.
    let packed_twiddles: Twiddles<Proth120, Global> =
        Twiddles::new(trace_len << pack_log2, &worker);

    // 5. Construct the setup and obtain an ON-DISK commitment for it: the packed
    //    RS codewords + Merkle tree are computed once via `commit_packed` and cached
    //    on disk; this and subsequent runs read them back lazily through
    //    `SetupCommitment::OnDisk` (so the setup never has to sit in RAM while
    //    proving). Delete the `*.rscw`/`*.tree` cache files to force a recompute.
    use crate::gkr::prover::{
        prove_configured_with_gkr_with_storage, SetupCommitment, WhirOracleStorage,
    };
    use crate::gkr::whir::coset_commit::serialize_packed_base_commitment_split_to_disk;
    use crate::gkr::whir::rs_on_disk::{coset_file_path, OnDiskRsCodewords};
    use crate::merkle_trees::on_disk::{top_tree_file_path, OnDiskTreeLayout};
    use crate::merkle_trees::{ColumnMajorMerkleTreeConstructor, RSQueriable};

    let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &unified_circuit);

    // On-disk setup with the "second" (per-coset subtree) tree layout: the packed
    // setup is prepared coset-by-coset — each coset's RS codewords and its cap-size-1
    // subtree are streamed to disk, then a small top-tree over the subtree roots — so
    // the ~2^31 codeword and its tree never have to be materialized whole. This and
    // later runs read them back lazily via mmap. Delete the cache files to recompute.
    let setup_disk_prefix = "test_proofs/unified_setup_proth120_ondisk";
    let lde_factor = prover_config.lde_factor;
    let values_per_leaf = prover_config.base_oracles_values_per_leaf;
    let setup_coset_paths: Vec<_> = (0..lde_factor)
        .map(|i| coset_file_path(setup_disk_prefix, i))
        .collect();
    let setup_on_disk_present = top_tree_file_path(setup_disk_prefix).exists()
        && setup_coset_paths.iter().all(|p| p.exists());

    if !setup_on_disk_present {
        println!("On-disk setup not present; preparing coset-by-coset (split tree) and caching");
        let inputs: Vec<&[Proth120]> = setup.hypercube_evals.iter().map(|el| &el[..]).collect();
        serialize_packed_base_commitment_split_to_disk::<Proth120, Keccak256MerkleTreeWithCap>(
            &inputs,
            &packed_twiddles,
            lde_factor,
            values_per_leaf.trailing_zeros() as usize,
            prover_config.cap_size,
            TRACE_LEN_LOG2,
            pack_log2,
            setup_disk_prefix,
            &worker,
        )
        .expect("cache split setup to disk");
    } else {
        println!("Reusing cached on-disk setup at prefix {setup_disk_prefix}");
    }

    // Open the on-disk setup: RS codewords + the split (per-coset subtree) tree, all
    // memory-mapped and read lazily.
    let setup_rs =
        OnDiskRsCodewords::<Proth120>::open(setup_coset_paths).expect("open on-disk setup RS");
    let setup_coset_size_log2 = RSQueriable::coset_size_log2(&setup_rs);
    let setup_disk_tree = <Keccak256MerkleTreeWithCap as ColumnMajorMerkleTreeConstructor<
        Proth120,
    >>::open_disk_artifacts(
        setup_disk_prefix,
        OnDiskTreeLayout::CosetSubtrees,
        lde_factor,
    );

    let setup_commitment = SetupCommitment::OnDisk {
        rs: Box::new(setup_rs),
        tree: setup_disk_tree,
        values_per_leaf,
        coset_size_log2: setup_coset_size_log2,
    };

    // 6. Prove one unified circuit instance with the packed commitment mode.
    let external_challenges = dummy_external_challenges::<Proth120, Proth120>();

    let commitment_mode = CommitmentMode::MergedAndPackedMemoryAndWitness {
        pack_log2,
        external_challenges_pow_bits,
        final_pc: vm.final_pc(),
        final_timestamp: vm.final_timestamp(),
        register_final_state: vm.register_final_state().map(|el| FinalRegisterValue {
            value: el.current_value,
            last_access_timestamp: el.last_access_timestamp,
        }),
    };

    println!("Trying to prove (unified, packed commitment, pack_log2 = {pack_log2})");
    println!("  memory/witness RS codewords: Recompute; setup: on-disk");
    let now = std::time::Instant::now();
    let proof = prove_configured_with_gkr_with_storage::<
        Proth120,
        Proth120,
        Keccak256MerkleTreeWithCap,
        Keccak256Transcript,
    >(
        &unified_circuit,
        &external_challenges,
        full_trace,
        &setup,
        &setup_commitment,
        &packed_twiddles,
        &prover_config,
        commitment_mode,
        WhirOracleStorage::fully_recompute(),
        top_bits,
        trace_len,
        &worker,
    );
    println!("Packed unified proving time is {:?}", now.elapsed());

    serialize_to_file(&proof, "unified_circuit_proof_proth120.json");
    serialize_to_file(
        &commitment_mode,
        "unified_circuit_proof_proth120_commitment_mod_aux_data.json",
    );
}

/// STEP 1 of the EVM GKR verifier: reproduce the `MergedAndPackedMemoryAndWitness`
/// Fiat-Shamir transcript purely from the serialized proof + circuit, and check the
/// derived challenges (nonce + `GKRExternalChallenges`) match what the prover stored.
///
/// This is the exact recipe the Solidity `transcript_init` must implement, and it
/// prints the reference values (seed / nonce / challenge coefficients) that the EVM
/// side is validated against. Fast: no proving, just deserialize + keccak.
#[test]
fn validate_packed_transcript_recipe() {
    use crate::gkr::prover::transcript_utils::draw_random_field_els_with_pow;
    use crate::gkr::prover::utils::flatten_merkle_caps_iter_into;
    use crate::gkr::prover::GKRProof;
    use crate::gkr::prover_config::pow_bits;
    use transcript::Transcript;

    fn hex32(b: &[u8; 32]) -> String {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }

    let worker = Worker::new_with_num_threads(4);

    let unified_circuit: GKRCircuitArtifact<Proth120> = {
        let src = std::fs::File::open(
            "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
        )
        .expect("unified circuit layout");
        serde_json::from_reader(src).expect("deserialize unified circuit")
    };

    let proof: GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap> = {
        let src = std::fs::File::open("unified_circuit_proof_proth120.json")
            .expect("run gkr_unified_packed_commitment_basic_fibonacci first");
        serde_json::from_reader(src).expect("deserialize proof")
    };

    // --- rebuild `transcript_input` exactly like the packed arm of the prover ---
    let (boundary_prefix, _register_final_state, _final_pc, _final_timestamp, external_pow_bits) =
        load_boundary_transcript_prefix();
    let mut transcript_input: Vec<u32> = vec![];
    // 0) register final states (value, ts_low, ts_high) x32, then (final_pc, final_ts_low, high)
    transcript_input.extend_from_slice(&boundary_prefix);
    // 1) circuit sequence / delegation top bits
    transcript_input.extend_from_slice(&proof.inits_and_teardowns_top_bits[..]);
    // 2) setup cap (present for this circuit: the setup has generic-lookup columns)
    let setup_cap = proof.whir_proof.setup_commitment.commitment.cap.clone();
    assert!(!setup_cap.cap.is_empty(), "expected a non-empty setup cap");
    flatten_merkle_caps_iter_into(Some(setup_cap).into_iter(), &mut transcript_input);
    // 3) merged (memory+witness) packed-commitment cap
    let merged_cap = proof.whir_proof.memory_commitment.commitment.cap.clone();
    flatten_merkle_caps_iter_into(Some(merged_cap).into_iter(), &mut transcript_input);

    // --- keccak seed + PoW-gated challenge draw ---
    let mut seed = <Keccak256Transcript as Transcript<Proth120, Proth120>>::commit_initial_u32(
        &transcript_input,
    );
    println!(
        "[transcript] initial seed after commit = 0x{}",
        hex32(&seed.0)
    );

    // The seed is exactly keccak256 of `transcript_input` as little-endian u32 bytes.
    // Emit that preimage as the EVM fixture (the Solidity `transcript_init` keccaks it),
    // and sanity-check our byte reconstruction matches `commit_initial_u32`.
    {
        use sha3::{Digest, Keccak256};
        let preimage: Vec<u8> = transcript_input
            .iter()
            .flat_map(|w| w.to_le_bytes())
            .collect();
        let computed = Keccak256::digest(&preimage);
        assert_eq!(
            &computed[..],
            &seed.0[..],
            "preimage keccak must equal commit_initial_u32 seed"
        );
        let hex: String = preimage.iter().map(|b| format!("{b:02x}")).collect();
        let out = "../verifier_evm/debug_data/gkr_step1_preimage.hex";
        std::fs::write(out, &hex).expect("write step1 preimage fixture");
        println!(
            "[transcript] wrote {} preimage bytes to {out}",
            preimage.len()
        );
    }

    let lookup_pow_bits = pow_bits::lookup_challenges_pow_bits(
        SecurityLevel::Sec100.security_bits(),
        pow_bits::lookup_identity_degree(&unified_circuit),
    );
    // prover draws external challenges with pow = max(lookup_pow_bits, external_pow_bits=20)
    let pow_bits_used = core::cmp::max(lookup_pow_bits, external_pow_bits);
    println!("[transcript] lookup pow_bits = {pow_bits_used}");

    const TOTAL: usize = 7; // GKRExternalChallenges::TOTAL_CHALLENGES
    let (nonce, challenges) = draw_random_field_els_with_pow::<
        Proth120,
        Proth120,
        Keccak256Transcript,
    >(&mut seed, TOTAL + 2, pow_bits_used, &worker);

    println!("[transcript] pow nonce = {nonce}");
    for (i, c) in challenges.iter().enumerate() {
        println!("[transcript] challenge[{i}] = 0x{:032x}", c.to_u128());
    }

    // --- assertions against the values the prover baked into the proof ---
    assert_eq!(
        nonce, proof.lookup_challenges_pow_nonce,
        "pow nonce diverged from proof"
    );
    let derived = crate::definitions::GKRExternalChallenges::<Proth120, Proth120>::from_slice(
        &challenges[..TOTAL],
    );
    assert_eq!(
        derived, proof.external_challenges,
        "derived GKRExternalChallenges diverged from proof"
    );
    println!("[transcript] OK: nonce + GKRExternalChallenges match the proof");
}

/// STEP 2a (dimension-reducing ENTRY): continue the transcript past STEP 1, absorb
/// the circuit output evaluations, draw the (eval_point, batching) challenges, and
/// compute the 10 initial sumcheck claims by evaluating the proof's output polys at
/// eval_point. This reproduces the "combine circuit outputs" entry to the GKR
/// dimension-reducing layers, and emits the reference values for the Solidity.
#[test]
fn capture_gkr_dim_reduce_reference() {
    use crate::gkr::prover::transcript_utils::{
        commit_field_els, draw_random_field_els, draw_random_field_els_with_pow,
    };
    use crate::gkr::prover::utils::flatten_merkle_caps_iter_into;
    use crate::gkr::prover::GKRProof;
    use crate::gkr::prover_config::pow_bits;
    use crate::gkr::sumcheck::eq_poly::{evaluate_with_precomputed_eq_ext, make_eq_poly_in_full};
    use transcript::Transcript;

    let worker = Worker::new_with_num_threads(4);
    let unified_circuit: GKRCircuitArtifact<Proth120> = {
        let src = std::fs::File::open(
            "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
        )
        .unwrap();
        serde_json::from_reader(src).unwrap()
    };
    let proof: GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap> = {
        let src = std::fs::File::open("unified_circuit_proof_proth120.json").unwrap();
        serde_json::from_reader(src).unwrap()
    };

    // --- replay STEP 1 to reach the post-external-challenges seed ---
    let (boundary_prefix, _rfs, _fpc, _fts, external_pow_bits) = load_boundary_transcript_prefix();
    let mut transcript_input: Vec<u32> = vec![];
    transcript_input.extend_from_slice(&boundary_prefix);
    transcript_input.extend_from_slice(&proof.inits_and_teardowns_top_bits[..]);
    flatten_merkle_caps_iter_into(
        Some(proof.whir_proof.setup_commitment.commitment.cap.clone()).into_iter(),
        &mut transcript_input,
    );
    flatten_merkle_caps_iter_into(
        Some(proof.whir_proof.memory_commitment.commitment.cap.clone()).into_iter(),
        &mut transcript_input,
    );
    let mut seed = <Keccak256Transcript as Transcript<Proth120, Proth120>>::commit_initial_u32(
        &transcript_input,
    );
    let pow = core::cmp::max(
        pow_bits::lookup_challenges_pow_bits(
            SecurityLevel::Sec100.security_bits(),
            pow_bits::lookup_identity_degree(&unified_circuit),
        ),
        external_pow_bits,
    );
    let _ = draw_random_field_els_with_pow::<Proth120, Proth120, Keccak256Transcript>(
        &mut seed, 9, pow, &worker,
    );

    // --- GKR entry: absorb output evals, draw eval_point(4) + batching(1) ---
    let mut evals_flattened: Vec<Proth120> = vec![];
    for (_out_ty, vals) in proof.final_explicit_evaluations.iter() {
        evals_flattened.extend_from_slice(&vals[0]);
        evals_flattened.extend_from_slice(&vals[1]);
    }
    println!(
        "[dimreduce] output polys flattened = {} elems",
        evals_flattened.len()
    );
    commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &evals_flattened);

    let final_trace_size_log_2 = proof.final_explicit_evaluations
        [proof.final_explicit_evaluations.keys().next().unwrap()][0]
        .len()
        .trailing_zeros() as usize;
    let num_challenges = final_trace_size_log_2 + 1;
    let mut challenges =
        draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, num_challenges);
    let batching = challenges.pop().unwrap();
    let eval_point = challenges;
    println!("[dimreduce] final_trace_size_log_2 = {final_trace_size_log_2}");
    println!("[dimreduce] seed after eval-point draws = 0x{}", {
        let b: [u8; 32] = seed.0;
        b.iter().map(|x| format!("{x:02x}")).collect::<String>()
    });
    for (i, e) in eval_point.iter().enumerate() {
        println!("[dimreduce] eval_point[{i}] = 0x{:032x}", e.to_u128());
    }
    println!("[dimreduce] batching = 0x{:032x}", batching.to_u128());

    // --- initial 10 claims: outputs evaluated at eval_point via eq ---
    let eq_layers = make_eq_poly_in_full::<Proth120>(&eval_point, &worker);
    let eq = eq_layers.last().unwrap();
    let mut claims: Vec<Proth120> = vec![];
    for (_out_ty, vals) in proof.final_explicit_evaluations.iter() {
        claims.push(evaluate_with_precomputed_eq_ext::<Proth120>(
            &vals[0],
            &eq[..],
        ));
        claims.push(evaluate_with_precomputed_eq_ext::<Proth120>(
            &vals[1],
            &eq[..],
        ));
    }
    for (i, c) in claims.iter().enumerate() {
        println!("[dimreduce] initial_claim[{i}] = 0x{:032x}", c.to_u128());
    }
    assert_eq!(claims.len(), 10);

    // Emit the output-eval blob for the EVM fixture: each field element as its
    // 16-byte big-endian u128 (exactly how `commit_field_els`/absorb_field feeds it).
    {
        let mut blob: Vec<u8> = Vec::with_capacity(evals_flattened.len() * 16);
        for e in evals_flattened.iter() {
            blob.extend_from_slice(&e.to_u128().to_be_bytes());
        }
        let hex: String = blob.iter().map(|b| format!("{b:02x}")).collect();
        std::fs::write(
            "../verifier_evm/debug_data/gkr_step2_output_evals.hex",
            &hex,
        )
        .unwrap();
        println!("[dimreduce] wrote {} output-eval bytes", blob.len());
    }
    println!("[dimreduce] OK: reproduced GKR-entry transcript + initial claims");
}

/// Validates the NO-INVERSION permutation identity check that the EVM verifier uses:
/// accumulate read-set and write-set products separately (from the GKR output polys +
/// the register/PC boundary), then require equality — instead of the prover's
/// grand-product/inverse form. Confirms both the algebra and the exact calldata
/// output-index mapping the Solidity verifier reads (BTreeMap<OutputType> order:
/// PermutationProduct -> outputs [0,1], InitsAndTeardownsProduct -> outputs [8,9]).
#[test]
fn verify_permutation_identity_no_inversion() {
    use crate::cs::definitions::split_timestamp;
    use crate::cs::definitions::OutputType;
    use crate::definitions::produce_initial_permutation_product_separate_contributions;
    use crate::gkr::prover::GKRProof;
    use ::field::Field;
    use common_constants::{INITIAL_PC, INITIAL_TIMESTAMP};
    type E = Proth120;

    let proof: GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap> = {
        let src = std::fs::File::open("unified_circuit_proof_proth120.json")
            .expect("run gkr_unified_packed_commitment_basic_fibonacci first");
        serde_json::from_reader(src).expect("deserialize proof")
    };
    let (_prefix, register_final_state, final_pc, final_timestamp, _pow) =
        load_boundary_transcript_prefix();

    let prod = |els: &[E]| {
        let mut r = E::ONE;
        for e in els.iter() {
            r.mul_assign(e);
        }
        r
    };

    // --- output-poly products, addressed the way the EVM verifier reads calldata ---
    // Serialized order = BTreeMap<OutputType>.iter(), each key emits vals[0] then vals[1].
    let mut flat: Vec<E> = vec![];
    for (_ot, vals) in proof.final_explicit_evaluations.iter() {
        flat.push(prod(&vals[0]));
        flat.push(prod(&vals[1]));
    }
    assert_eq!(flat.len(), 10, "expected 10 output polys");
    // Solidity indices (must match the calldata layout the verifier consumes):
    let read_poly = flat[0]; // PermutationProduct.vals[0] = read
    let write_poly = flat[1]; // PermutationProduct.vals[1] = write
    let teardown_poly = flat[8]; // InitsAndTeardownsProduct.vals[0] = teardown
    let init_poly = flat[9]; // InitsAndTeardownsProduct.vals[1] = init

    // Cross-check the fixed indices against map access (guards the ordering assumption).
    let perm = proof
        .final_explicit_evaluations
        .get(&OutputType::PermutationProduct)
        .expect("PermutationProduct present");
    let it = proof
        .final_explicit_evaluations
        .get(&OutputType::InitsAndTeardownsProduct)
        .expect("InitsAndTeardownsProduct present");
    assert_eq!(read_poly, prod(&perm[0]), "output[0] must be Perm.read");
    assert_eq!(write_poly, prod(&perm[1]), "output[1] must be Perm.write");
    assert_eq!(
        teardown_poly,
        prod(&it[0]),
        "output[8] must be I&T.teardown"
    );
    assert_eq!(init_poly, prod(&it[1]), "output[9] must be I&T.init");

    // --- register/PC boundary contributions (read_bnd, write_bnd) ---
    let register_final_data: [(u32, (u32, u32)); 32] = core::array::from_fn(|i| {
        (
            register_final_state[i].value,
            split_timestamp(register_final_state[i].last_access_timestamp),
        )
    });
    let (read_bnd, write_bnd) =
        produce_initial_permutation_product_separate_contributions::<Proth120, Proth120>(
            &register_final_data,
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            final_pc,
            split_timestamp(final_timestamp),
            &proof.external_challenges,
        );

    // --- no-inversion identity: read side product == write side product ---
    let mut read_product = read_poly;
    read_product.mul_assign(&teardown_poly);
    read_product.mul_assign(&read_bnd);
    let mut write_product = write_poly;
    write_product.mul_assign(&init_poly);
    write_product.mul_assign(&write_bnd);

    println!(
        "[perm-id] read_product =0x{:032x}\n[perm-id] write_product=0x{:032x}",
        read_product.to_u128(),
        write_product.to_u128()
    );
    assert_eq!(
        read_product, write_product,
        "no-inversion permutation identity must hold: read_poly*teardown*read_bnd == write_poly*init*write_bnd"
    );
}

/// Output address for the single-output GKR relation variants (compute_claim kind 1).
/// Returns None for constraint gates (kind 0) and dual-output lookups (kind 2).
fn single_output(
    rel: &crate::cs::gkr_compiler::NoFieldGKRRelation<Proth120>,
) -> Option<&crate::cs::definitions::GKRAddress> {
    use crate::cs::gkr_compiler::NoFieldGKRRelation as R;
    match rel {
        R::CopyInBaseField { output, .. }
        | R::CopyInExtensionField { output, .. }
        | R::MaskIntoIdentityProduct { output, .. }
        | R::TrivialProduct { output, .. }
        | R::InitialGrandProductFromCaches { output, .. }
        | R::UnbalancedGrandProductWithCache { output, .. }
        | R::MaterializeGrandProductTermExpression { output, .. }
        | R::InitialGrandProductWithoutCaches { output, .. }
        | R::MaterializeSingleLookupInput { output, .. }
        | R::MaterializedVectorLookupInput { output, .. }
        | R::InitsOrTeardownsInitialPair { output, .. }
        | R::LinearBaseFieldRelation { output, .. }
        | R::MaxQuadratic { output, .. } => Some(output),
        _ => None,
    }
}

/// Output pair for the dual-output (lookup, compute_claim kind 2) relation variants.
fn dual_outputs(
    rel: &crate::cs::gkr_compiler::NoFieldGKRRelation<Proth120>,
) -> Option<&[crate::cs::definitions::GKRAddress; 2]> {
    use crate::cs::gkr_compiler::NoFieldGKRRelation as R;
    match rel {
        R::AggregateLookupRationalPair { output, .. }
        | R::LookupPairFromBaseInputs { output, .. }
        | R::LookupPairFromMaterializedBaseInputs { output, .. }
        | R::LookupUnbalancedPairWithMaterializedBaseInputs { output, .. }
        | R::LookupFromMaterializedBaseInputWithSetup { output, .. }
        | R::LookupPairFromVectorInputs { output, .. }
        | R::LookupPairFromMaterializedVectorInputs { output, .. }
        | R::LookupPairFromCachedVectorInputs { output, .. }
        | R::LookupUnbalancedPairWithMaterializedVectorInputs { output, .. }
        | R::LookupUnbalancedPairWithVectorInputs { output, .. }
        | R::LookupWithCachedDensAndSetup { output, .. }
        | R::LookupWithDensAndSetupExpressions { output, .. }
        | R::LookupFromVectorInputWithSetup { output, .. }
        | R::LookupFromMaterializedVectorInputWithSetup { output, .. } => Some(output),
        _ => None,
    }
}

/// Per-gate final-step `g` accumulator for a standard circuit layer, mirroring the
/// generator's `layer_N_final_step_accumulator` (simple gates share a running batch).
/// Only the relation types needed so far are implemented; extend as layers are added.
#[allow(clippy::too_many_arguments)]
fn circuit_layer_g(
    gates: &[&crate::cs::gkr_compiler::GateArtifacts<Proth120>],
    evals: &[Proth120],
    input_sorted: &[crate::cs::definitions::GKRAddress],
    batching: Proth120,
    lookup_additive: Proth120,
    lin_challenges: &[Proth120],
    perm_additive: Proth120,
    top_bits: &[u32],
    addr_shift: u32,
    addr_to_idx: &impl Fn(
        &crate::cs::definitions::GKRAddress,
        &[crate::cs::definitions::GKRAddress],
    ) -> usize,
) -> Proth120 {
    use crate::cs::definitions::GKRAddress;
    use crate::cs::gkr_compiler::InitsOrTeardownsTimestampAndValue as ITV;
    use crate::cs::gkr_compiler::NoFieldGKRRelation as R;
    use ::field::Field;
    type E = Proth120;
    let mul = |a: &E, b: &E| {
        let mut t = *a;
        t.mul_assign(b);
        t
    };
    let ev = |addr: &crate::cs::definitions::GKRAddress| evals[addr_to_idx(addr, input_sorted)];
    let mut acc = E::ZERO;
    let mut cb = E::ONE;
    for g in gates {
        match &g.enforced_relation {
            R::CopyInBaseField { input, .. } | R::CopyInExtensionField { input, .. } => {
                let bc = cb;
                cb.mul_assign(&batching);
                acc.add_assign(&mul(&bc, &ev(input)));
            }
            R::MaskIntoIdentityProduct { input, mask, .. } => {
                // val = (input - 1)*mask + 1
                let bc = cb;
                cb.mul_assign(&batching);
                let mut val = ev(input);
                val.sub_assign(&E::ONE);
                val.mul_assign(&ev(mask));
                val.add_assign(&E::ONE);
                acc.add_assign(&mul(&bc, &val));
            }
            R::TrivialProduct { input, .. } | R::InitialGrandProductFromCaches { input, .. } => {
                // val = evals[i0] * evals[i1]
                let bc = cb;
                cb.mul_assign(&batching);
                acc.add_assign(&mul(&bc, &mul(&ev(&input[0]), &ev(&input[1]))));
            }
            R::AggregateLookupRationalPair { input, .. } => {
                // a/b + c/d -> (num = a*d + c*b, den = b*d)
                let a = ev(&input[0][0]);
                let b = ev(&input[0][1]);
                let c = ev(&input[1][0]);
                let d = ev(&input[1][1]);
                let bc0 = cb;
                cb.mul_assign(&batching);
                let bc1 = cb;
                cb.mul_assign(&batching);
                let mut num = mul(&a, &d);
                num.add_assign(&mul(&c, &b));
                let den = mul(&b, &d);
                acc.add_assign(&mul(&bc0, &num));
                acc.add_assign(&mul(&bc1, &den));
            }
            R::LookupPairFromMaterializedVectorInputs { input, .. }
            | R::LookupPairFromMaterializedBaseInputs { input, .. } => {
                // LookupInitialPair: bg=b+γ, dg=d+γ; num=bg+dg, den=bg*dg
                let mut bg = ev(&input[0]);
                bg.add_assign(&lookup_additive);
                let mut dg = ev(&input[1]);
                dg.add_assign(&lookup_additive);
                let bc0 = cb;
                cb.mul_assign(&batching);
                let bc1 = cb;
                cb.mul_assign(&batching);
                let mut num = bg;
                num.add_assign(&dg);
                let den = mul(&bg, &dg);
                acc.add_assign(&mul(&bc0, &num));
                acc.add_assign(&mul(&bc1, &den));
            }
            R::LookupFromMaterializedBaseInputWithSetup { input, setup, .. } => {
                // LookupWithSetup: bg=input+γ, dg=setup1+γ; num=dg - setup0*bg, den=bg*dg
                let mut bg = ev(input);
                bg.add_assign(&lookup_additive);
                let mut dg = ev(&setup[1]);
                dg.add_assign(&lookup_additive);
                let mut cbv = ev(&setup[0]);
                cbv.mul_assign(&bg);
                let bc0 = cb;
                cb.mul_assign(&batching);
                let bc1 = cb;
                cb.mul_assign(&batching);
                let mut num = dg;
                num.sub_assign(&cbv);
                let den = mul(&bg, &dg);
                acc.add_assign(&mul(&bc0, &num));
                acc.add_assign(&mul(&bc1, &den));
            }
            R::LookupWithCachedDensAndSetup { input, setup, .. } => {
                // LookupInitialWithCachedDenominators:
                //   num = a*(d+γ) - c*(b+γ), den = (b+γ)(d+γ)
                let a = ev(&input[0]);
                let mut b_cd = ev(&input[1]);
                b_cd.add_assign(&lookup_additive);
                let c = ev(&setup[0]);
                let mut d_cd = ev(&setup[1]);
                d_cd.add_assign(&lookup_additive);
                let bc0 = cb;
                cb.mul_assign(&batching);
                let bc1 = cb;
                cb.mul_assign(&batching);
                let mut num = mul(&a, &d_cd);
                num.sub_assign(&mul(&c, &b_cd));
                let den = mul(&b_cd, &d_cd);
                acc.add_assign(&mul(&bc0, &num));
                acc.add_assign(&mul(&bc1, &den));
            }
            R::LookupUnbalancedPairWithMaterializedBaseInputs {
                input, remainder, ..
            }
            | R::LookupUnbalancedPairWithMaterializedVectorInputs {
                input, remainder, ..
            } => {
                // LookupUnbalanced: r=remainder+γ; num=a*r+b, den=b*r
                let a = ev(&input[0]);
                let b = ev(&input[1]);
                let mut r = ev(remainder);
                r.add_assign(&lookup_additive);
                let bc0 = cb;
                cb.mul_assign(&batching);
                let bc1 = cb;
                cb.mul_assign(&batching);
                let mut num = mul(&a, &r);
                num.add_assign(&b);
                let den = mul(&b, &r);
                acc.add_assign(&mul(&bc0, &num));
                acc.add_assign(&mul(&bc1, &den));
            }
            R::EnforceSingleMaxQuadraticConstraint { input, .. }
            | R::MaxQuadratic { input, .. } => {
                // val = constant + Σ_a evals[a]·(Σ coeff·evals[b]) + Σ coeff·evals[addr]
                let bc = cb;
                cb.mul_assign(&batching);
                let mut val = input.constant;
                for (addr_a, inner_terms) in input.quadratic_terms.iter() {
                    let mut inner = E::ZERO;
                    for (coeff, addr_b) in inner_terms.iter() {
                        inner.add_assign(&mul(coeff, &ev(addr_b)));
                    }
                    val.add_assign(&mul(&ev(addr_a), &inner));
                }
                for (coeff, addr) in input.linear_terms.iter() {
                    val.add_assign(&mul(coeff, &ev(addr)));
                }
                acc.add_assign(&mul(&bc, &val));
            }
            R::InitsOrTeardownsInitialPair {
                timestamp_and_value,
                setup,
                set_idxes,
                ..
            } => {
                // val = lhs * rhs; each side is a permutation-argument linear combination
                // over (constant 1, address low/high[+set window], and for teardown ts/value).
                let bc = cb;
                cb.mul_assign(&batching);
                let side = |set_idx: usize, is_lhs: bool| -> E {
                    let mut result = perm_additive;
                    result.add_assign(&E::ONE); // ram_constant = 1
                                                // address low
                    let mut t = lin_challenges[0];
                    t.mul_assign(&ev(&setup[0]));
                    result.add_assign(&t);
                    // address high (+ set window)
                    let mut addr_hi = ev(&setup[1]);
                    let set_bits = top_bits[set_idx] << addr_shift;
                    if set_bits != 0 {
                        addr_hi.add_assign(
                            &<Proth120 as ::field::PrimeField>::from_u32_with_reduction(set_bits),
                        );
                    }
                    let mut t = lin_challenges[1];
                    t.mul_assign(&addr_hi);
                    result.add_assign(&t);
                    // teardown: timestamp + value terms
                    if let ITV::Teardown {
                        lhs_timestamp,
                        lhs_value,
                        rhs_timestamp,
                        rhs_value,
                    } = timestamp_and_value
                    {
                        let (ts, value) = if is_lhs {
                            (lhs_timestamp, lhs_value)
                        } else {
                            (rhs_timestamp, rhs_value)
                        };
                        for (chal_idx, col) in
                            [(2usize, ts[0]), (3, ts[1]), (4, value[0]), (5, value[1])]
                        {
                            let mut t = lin_challenges[chal_idx];
                            t.mul_assign(&ev(&GKRAddress::BaseLayerMemory(col)));
                            result.add_assign(&t);
                        }
                    }
                    result
                };
                let lhs = side(set_idxes[0], true);
                let rhs = side(set_idxes[1], false);
                acc.add_assign(&mul(&bc, &mul(&lhs, &rhs)));
            }
            other => panic!("circuit_layer_g: unhandled relation {other:?}"),
        }
    }
    acc
}

/// STEP 2b: a full Rust verifier-mirror of the GKR DIMENSION-REDUCING layers,
/// mirroring the native (verifier_generator) logic exactly, run against the real
/// proof. If every per-round sumcheck check and per-layer final-step check passes,
/// the recipe (which the Solidity will implement) is confirmed. Also captures the
/// per-layer claim/challenge reference.
#[test]
fn verify_dim_reduce_layers() {
    use crate::gkr::prover::transcript_utils::{
        commit_field_els, draw_random_field_els, draw_random_field_els_with_pow,
    };
    use crate::gkr::prover::utils::flatten_merkle_caps_iter_into;
    use crate::gkr::prover::GKRProof;
    use crate::gkr::prover_config::pow_bits;
    use crate::gkr::sumcheck::eq_poly::{evaluate_with_precomputed_eq_ext, make_eq_poly_in_full};
    use ::field::Field;
    use transcript::Transcript;

    type E = Proth120;
    let worker = Worker::new_with_num_threads(4);
    let unified_circuit: GKRCircuitArtifact<Proth120> = serde_json::from_reader(
        std::fs::File::open(
            "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
        )
        .unwrap(),
    )
    .unwrap();
    let proof: GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap> = serde_json::from_reader(
        std::fs::File::open("unified_circuit_proof_proth120.json").unwrap(),
    )
    .unwrap();

    // ---- replay transcript through the GKR entry (STEP 1 + STEP 2a) ----
    let (boundary_prefix, _rfs, _fpc, _fts, external_pow_bits) = load_boundary_transcript_prefix();
    let mut ti: Vec<u32> = vec![];
    ti.extend_from_slice(&boundary_prefix);
    ti.extend_from_slice(&proof.inits_and_teardowns_top_bits[..]);
    flatten_merkle_caps_iter_into(
        Some(proof.whir_proof.setup_commitment.commitment.cap.clone()).into_iter(),
        &mut ti,
    );
    flatten_merkle_caps_iter_into(
        Some(proof.whir_proof.memory_commitment.commitment.cap.clone()).into_iter(),
        &mut ti,
    );
    let mut seed = <Keccak256Transcript as Transcript<Proth120, Proth120>>::commit_initial_u32(&ti);
    let pow = core::cmp::max(
        pow_bits::lookup_challenges_pow_bits(
            SecurityLevel::Sec100.security_bits(),
            pow_bits::lookup_identity_degree(&unified_circuit),
        ),
        external_pow_bits,
    );
    let (_entry_nonce, entry_challenges) =
        draw_random_field_els_with_pow::<Proth120, Proth120, Keccak256Transcript>(
            &mut seed, 9, pow, &worker,
        );
    // [0..6] perm-linearization, [6] perm additive, [7] lookup_alpha, [8] lookup_additive_part
    let lookup_alpha = entry_challenges[7];
    let lookup_additive = entry_challenges[8];
    let mut evals_flat: Vec<E> = vec![];
    for (_t, v) in proof.final_explicit_evaluations.iter() {
        evals_flat.extend_from_slice(&v[0]);
        evals_flat.extend_from_slice(&v[1]);
    }
    commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &evals_flat);
    let final_trace_size_log_2 = proof.final_explicit_evaluations.values().next().unwrap()[0]
        .len()
        .trailing_zeros() as usize;
    let mut chs = draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(
        &mut seed,
        final_trace_size_log_2 + 1,
    );
    let mut batching = chs.pop().unwrap();
    let mut point = chs; // eval_point (final_trace_size_log_2 coords)
    let eq = make_eq_poly_in_full::<E>(&point, &worker)
        .last()
        .unwrap()
        .clone();
    let mut claims: Vec<E> = vec![];
    for (_t, v) in proof.final_explicit_evaluations.iter() {
        claims.push(evaluate_with_precomputed_eq_ext::<E>(&v[0], &eq[..]));
        claims.push(evaluate_with_precomputed_eq_ext::<E>(&v[1], &eq[..]));
    }
    assert_eq!(claims.len(), 10);

    // helpers
    let sum01 = |c: &[E; 4]| {
        let mut s = c[0];
        s.add_assign(&c[0]);
        s.add_assign(&c[1]);
        s.add_assign(&c[2]);
        s.add_assign(&c[3]);
        s
    };
    let horner = |c: &[E; 4], r: &E| {
        let mut v = c[3];
        v.mul_assign(r);
        v.add_assign(&c[2]);
        v.mul_assign(r);
        v.add_assign(&c[1]);
        v.mul_assign(r);
        v.add_assign(&c[0]);
        v
    };
    let eqrp = |r: &E, p: &E| {
        let mut omr = E::ONE;
        omr.sub_assign(r);
        let mut omp = E::ONE;
        omp.sub_assign(p);
        let mut t = omr;
        t.mul_assign(&omp);
        let mut rp = *r;
        rp.mul_assign(p);
        t.add_assign(&rp);
        t
    };
    let mul = |a: &E, b: &E| {
        let mut t = *a;
        t.mul_assign(b);
        t
    };

    let num_standard_layers = unified_circuit.layers.len();
    println!("[dimreduce-verify] num_standard_layers = {num_standard_layers}");
    println!("[dimreduce-verify] global_output_map (iteration order):");
    for (ot, addrs) in unified_circuit.global_output_map.iter() {
        println!("    {ot:?}: {addrs:?}");
    }

    // ---- dim-reducing layers 21..=4 (processed output->base) ----
    let dim_layers: Vec<usize> = proof
        .sumcheck_intermediate_values
        .keys()
        .copied()
        .filter(|l| proof.sumcheck_intermediate_values[l].sumcheck_num_rounds < 22)
        .collect();
    let mut blob: Vec<u8> = vec![]; // per layer: rounds*[c0..c3] then 10*[lsb0,lsb1], all BE16
    let push_e = |blob: &mut Vec<u8>, e: &E| blob.extend_from_slice(&e.to_u128().to_be_bytes());
    for &layer in dim_layers.iter().rev() {
        {
            let siv = &proof.sumcheck_intermediate_values[&layer];
            for c in siv.internal_round_coefficients.iter() {
                for e in c.iter() {
                    push_e(&mut blob, e);
                }
            }
            for v in siv.final_step_evaluations.values() {
                push_e(&mut blob, &v[0]);
                push_e(&mut blob, &v[1]);
            }
        }
        let siv = &proof.sumcheck_intermediate_values[&layer];
        let folding_steps = siv.sumcheck_num_rounds;
        assert_eq!(
            folding_steps,
            point.len(),
            "layer {layer} folding_steps vs point"
        );

        // initial claim = RLC(claims, batching)
        let mut claim = E::ZERO;
        let mut cb = E::ONE;
        for c in claims.iter() {
            claim.add_assign(&mul(&cb, c));
            cb.mul_assign(&batching);
        }

        // sumcheck rounds
        let mut eq_prefactor = E::ONE;
        let mut new_point: Vec<E> = Vec::with_capacity(folding_steps + 1);
        for round in 0..folding_steps {
            let c = siv.internal_round_coefficients[round];
            let mut s = sum01(&c);
            s.mul_assign(&eq_prefactor);
            assert_eq!(s, claim, "dim layer {layer} round {round} sumcheck check");
            commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &c);
            let r =
                draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, 1)[0];
            claim = horner(&c, &r);
            eq_prefactor = eqrp(&r, &point[round]);
            new_point.push(r);
        }
        let final_claim = claim;
        let final_eq = eq_prefactor;

        // LSB lines (final_step_evaluations) in sorted-address order = 10 outputs
        let lsb_sorted: Vec<[E; 2]> = siv
            .final_step_evaluations
            .values()
            .map(|v| [v[0], v[1]])
            .collect();
        assert_eq!(lsb_sorted.len(), 10, "layer {layer} expects 10 LSB lines");

        // Reorder into LOGICAL (OutputType-group) order. Cascade layers use identity;
        // the boundary layer (= num_standard_layers) takes the circuit's global_output_map,
        // whose addresses sort differently, so apply the global_output_map permutation.
        let lsb: Vec<[E; 2]> = if layer == num_standard_layers {
            let sorted_keys: Vec<_> = siv.final_step_evaluations.keys().copied().collect();
            unified_circuit
                .global_output_map
                .values()
                .flatten()
                .map(|a| lsb_sorted[sorted_keys.iter().position(|k| k == a).unwrap()])
                .collect()
        } else {
            lsb_sorted.clone()
        };

        // final-step accumulator g: products for [0,1] and [8,9]; lookups for (2,3),(4,5),(6,7)
        let mut g = E::ZERO;
        let mut cb = E::ONE;
        let mut acc_prod = |g: &mut E, cb: &mut E, l: &[E; 2]| {
            let mut t = mul(cb, &mul(&l[0], &l[1]));
            g.add_assign(&t);
            let _ = &mut t;
            cb.mul_assign(&batching);
        };
        acc_prod(&mut g, &mut cb, &lsb[0]);
        acc_prod(&mut g, &mut cb, &lsb[1]);
        for (ni, di) in [(2usize, 3usize), (4, 5), (6, 7)] {
            let v0 = &lsb[ni];
            let v1 = &lsb[di];
            let mut num = mul(&v0[0], &v1[1]);
            num.add_assign(&mul(&v0[1], &v1[0]));
            let den = mul(&v1[0], &v1[1]);
            g.add_assign(&mul(&cb, &num));
            cb.mul_assign(&batching);
            g.add_assign(&mul(&cb, &den));
            cb.mul_assign(&batching);
        }
        acc_prod(&mut g, &mut cb, &lsb[8]);
        acc_prod(&mut g, &mut cb, &lsb[9]);

        let rhs = mul(&g, &final_eq);
        if rhs != final_claim {
            println!(
                "[dimreduce-verify] layer {layer} FINAL-STEP MISMATCH: keys = {:?}",
                siv.final_step_evaluations.keys().collect::<Vec<_>>()
            );
            println!(
                "    final_claim=0x{:032x} g=0x{:032x} final_eq=0x{:032x} rhs=0x{:032x}",
                final_claim.to_u128(),
                g.to_u128(),
                final_eq.to_u128(),
                rhs.to_u128()
            );
        }
        assert_eq!(rhs, final_claim, "dim layer {layer} final-step check");

        // absorb LSB lines in SORTED (transcript) order, draw r_last + next_batching
        let lsb_flat: Vec<E> = lsb_sorted.iter().flat_map(|l| [l[0], l[1]]).collect();
        commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &lsb_flat);
        let two = draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, 2);
        let (r_last, next_batching) = (two[0], two[1]);
        new_point.push(r_last);

        // next-layer claims = LSB interpolated at r_last in SORTED input-address order
        // (matches the generator: `eval_buf` order; the boundary permutation applies only to g).
        claims = lsb_sorted
            .iter()
            .map(|l| {
                let mut d = l[1];
                d.sub_assign(&l[0]);
                d.mul_assign(&r_last);
                d.add_assign(&l[0]);
                d
            })
            .collect();
        point = new_point;
        batching = next_batching;
    }

    println!(
        "[dimreduce-verify] OK: all dimension-reducing layers verified; point now has {} coords, batching=0x{:032x}",
        point.len(),
        batching.to_u128()
    );
    println!(
        "[dimreduce-verify] seed after dim-reducing = 0x{}",
        seed.0
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    );

    // ================= STEP 3: standard CIRCUIT layers (config_idx 3,2,1,0) =================
    // Same per-layer shape as dim-reducing: initial claim via per-gate `descs` RLC, then the
    // FULL 22 monomial sumcheck rounds, then a per-gate `g` accumulator, final-step check
    // `g*eq==claim`, absorb the at-point evals, draw next_batching, next claims = evals directly.
    use crate::cs::definitions::GKRAddress;
    use crate::cs::gkr_compiler::NoFieldGKRRelation as R;
    let addr_to_idx = |addr: &GKRAddress, sorted: &[GKRAddress]| -> usize {
        sorted
            .iter()
            .position(|x| x == addr)
            .expect("addr in sorted set")
    };
    let address_high_bits_shift: u32 = if !proof.inits_and_teardowns_top_bits.is_empty() {
        crate::gkr::high_bits_offset_for_inits_and_teardowns::<2>(unified_circuit.trace_len)
    } else {
        0
    };
    let mut layer0_merged: std::collections::BTreeMap<GKRAddress, E> = Default::default();
    let mut circuit_blob: Vec<u8> = vec![]; // per circuit layer: coeffs then group-offset evals (BE16)
    for config_idx in (0..num_standard_layers).rev() {
        let layer = &unified_circuit.layers[config_idx];
        let siv = &proof.sumcheck_intermediate_values[&config_idx];
        let folding_steps = siv.sumcheck_num_rounds;
        assert_eq!(
            folding_steps,
            point.len(),
            "circuit layer {config_idx} folding_steps vs point"
        );

        let gates: Vec<_> = layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
            .collect();

        // output_sorted_addrs = sorted unique gate outputs
        let mut out_set: std::collections::BTreeSet<GKRAddress> = Default::default();
        for g in &gates {
            match &g.enforced_relation {
                R::EnforceSingleMaxQuadraticConstraint { .. }
                | R::EnforceConstraintsMaxQuadratic { .. } => {}
                rel => {
                    if let Some(out) = dual_outputs(rel) {
                        out_set.insert(out[0]);
                        out_set.insert(out[1]);
                    } else {
                        out_set.insert(*single_output(rel).expect("single-output gate"));
                    }
                }
            }
        }
        let output_sorted: Vec<GKRAddress> = out_set.into_iter().collect();

        // input at-point evals (sorted by address) + their addresses
        let input_sorted: Vec<GKRAddress> = siv.final_step_evaluations.keys().copied().collect();
        let evals: Vec<E> = siv.final_step_evaluations.values().map(|v| v[0]).collect();

        // ---- collect this layer's CALLDATA (gkr.sol stream order): the folding-round coeffs
        // (22 rounds * [c0..c3], BE16) then the at-point evals in GROUP-OFFSET order (BE16).
        // Cached/VirtualSetup are computed on the verifier heap, so they're NOT in calldata. ----
        {
            for c in siv.internal_round_coefficients.iter() {
                for e in c.iter() {
                    circuit_blob.extend_from_slice(&e.to_u128().to_be_bytes());
                }
            }
            let num_mem = unified_circuit.memory_layout.total_width;
            let num_wit = unified_circuit.witness_layout.total_width;
            let group_idx = |addr: &GKRAddress| -> Option<usize> {
                match addr {
                    GKRAddress::InnerLayer { layer, offset }
                        if *layer == config_idx && config_idx > 0 =>
                    {
                        Some(*offset)
                    }
                    GKRAddress::BaseLayerMemory(o) if config_idx == 0 => Some(*o),
                    GKRAddress::BaseLayerWitness(o) if config_idx == 0 => Some(num_mem + *o),
                    GKRAddress::Setup(o) if config_idx == 0 => Some(num_mem + num_wit + *o),
                    _ => None, // Cached / VirtualSetup: computed on heap, not in calldata
                }
            };
            let mut by_idx: std::collections::BTreeMap<usize, E> = Default::default();
            for (addr, val) in siv.final_step_evaluations.iter() {
                if let Some(idx) = group_idx(addr) {
                    by_idx.insert(idx, val[0]);
                }
            }
            // Also serialize the caching-relation extra evals: they are InnerLayer inputs the
            // caches depend on but that live outside final_step_evaluations, and previously left
            // 0-fill gaps in the calldata (offsets 8..47 for layer1). The verifier reads them by
            // group offset just like any other InnerLayer input.
            for (addr, val) in siv.extra_evaluations_from_caching_relations.iter() {
                if let Some(idx) = group_idx(addr) {
                    by_idx.insert(idx, *val);
                }
            }
            let n = by_idx.keys().max().map(|m| m + 1).unwrap_or(0);
            for i in 0..n {
                let v = by_idx.get(&i).copied().unwrap_or(E::ZERO);
                circuit_blob.extend_from_slice(&v.to_u128().to_be_bytes());
            }
        }

        // ---- initial claim = compute_claim(prev_claims, descs) ----
        // descs in gate order; kind 0 = constraint (skip 1 batch), 1 = single out, 2 = dual out.
        let mut claim = E::ZERO;
        let mut cb = E::ONE;
        for g in &gates {
            match &g.enforced_relation {
                R::EnforceSingleMaxQuadraticConstraint { .. }
                | R::EnforceConstraintsMaxQuadratic { .. } => {
                    cb.mul_assign(&batching); // constraint: skip one slot
                }
                rel => {
                    if let Some(out) = dual_outputs(rel) {
                        let o0 = addr_to_idx(&out[0], &output_sorted);
                        let o1 = addr_to_idx(&out[1], &output_sorted);
                        claim.add_assign(&mul(&cb, &claims[o0]));
                        cb.mul_assign(&batching);
                        claim.add_assign(&mul(&cb, &claims[o1]));
                        cb.mul_assign(&batching);
                    } else {
                        let o0 = addr_to_idx(single_output(rel).unwrap(), &output_sorted);
                        claim.add_assign(&mul(&cb, &claims[o0]));
                        cb.mul_assign(&batching);
                    }
                }
            }
        }

        println!(
            "[layer-dbg] layer {config_idx} seed=0x{}",
            seed.0
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        );
        println!(
            "[layer-dbg] layer {config_idx} initial_claim=0x{:032x}  batching=0x{:032x}  round0_c=[{:032x},{:032x},{:032x},{:032x}]",
            claim.to_u128(), batching.to_u128(),
            siv.internal_round_coefficients[0][0].to_u128(),
            siv.internal_round_coefficients[0][1].to_u128(),
            siv.internal_round_coefficients[0][2].to_u128(),
            siv.internal_round_coefficients[0][3].to_u128(),
        );
        // ---- 22 monomial sumcheck rounds (same loop as dim-reducing) ----
        let mut eq_prefactor = E::ONE;
        let mut new_point: Vec<E> = Vec::with_capacity(folding_steps);
        for round in 0..folding_steps {
            let c = siv.internal_round_coefficients[round];
            let mut s = sum01(&c);
            s.mul_assign(&eq_prefactor);
            assert_eq!(
                s, claim,
                "circuit layer {config_idx} round {round} sumcheck check"
            );
            let cflat: Vec<E> = c.to_vec();
            commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &cflat);
            let r =
                draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, 1)[0];
            claim = horner(&c, &r);
            eq_prefactor = eqrp(&r, &point[round]);
            new_point.push(r);
        }
        let final_claim = claim;
        let final_eq = eq_prefactor;

        // ---- per-gate g accumulator (simple gates share a running batch) ----
        let g = circuit_layer_g(
            &gates,
            &evals,
            &input_sorted,
            batching,
            lookup_additive,
            &entry_challenges[0..6],
            entry_challenges[6],
            &proof.inits_and_teardowns_top_bits,
            address_high_bits_shift,
            &addr_to_idx,
        );
        let rhs = mul(&g, &final_eq);
        if rhs != final_claim {
            println!(
                "[circuit-verify] layer {config_idx} FINAL-STEP MISMATCH: final_claim=0x{:032x} g=0x{:032x} final_eq=0x{:032x} rhs=0x{:032x}",
                final_claim.to_u128(), g.to_u128(), final_eq.to_u128(), rhs.to_u128()
            );
        }
        assert_eq!(
            rhs, final_claim,
            "circuit layer {config_idx} final-step check"
        );

        // ---- absorb at-point evals (sorted order), draw next_batching ----
        commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &evals);
        let next_batching =
            draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, 1)[0];

        // cached relations: absorb the extra evals (address-sorted), then next-layer claims =
        // merge(at-point evals, extra evals) in address-sorted order (matches the prover, which
        // absorbs extras AFTER drawing next_batching).
        let extra = &siv.extra_evaluations_from_caching_relations;
        if !extra.is_empty() {
            let extra_vals: Vec<E> = extra.values().copied().collect();
            commit_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, &extra_vals);
        }
        let mut merged: std::collections::BTreeMap<GKRAddress, E> = Default::default();
        for (k, v) in siv.final_step_evaluations.iter() {
            merged.insert(*k, v[0]);
        }
        for (k, v) in extra.iter() {
            merged.insert(*k, *v);
        }
        claims = merged.values().copied().collect();
        if config_idx == 0 {
            layer0_merged = merged.clone();
        }

        // ---- cache-relation consistency: each cached (virtual) poly's at-point eval must
        // equal the linear/vector-lookup combination of its dependency at-point evals. ----
        {
            use crate::cs::definitions::gkr::RamWordRepresentation as Val;
            use crate::cs::gkr_compiler::NoFieldGKRCacheRelation as CR;
            use crate::cs::gkr_compiler::{
                CompiledAddressSpaceRelationStrict as ASpace, CompiledAddressStrict as Addr,
                CompiledMemoryTimestamp as Ts,
            };
            let fu = |x: u32| <Proth120 as ::field::PrimeField>::from_u32_with_reduction(x);
            let target_addrs: Vec<GKRAddress> = merged.keys().copied().collect();
            let claim_at = |addr: &GKRAddress| -> E {
                claims[target_addrs
                    .iter()
                    .position(|a| a == addr)
                    .expect("cache dep in target_addrs")]
            };
            let mut n_checked = 0usize;
            for (cached_addr, relation) in layer.cached_relations.iter() {
                let cached = claim_at(cached_addr);
                match relation {
                    CR::SingleColumnLookup { relation: rel, .. } => {
                        let mut expected = rel.input.constant;
                        for (coeff, addr) in rel.input.linear_terms.iter() {
                            expected.add_assign(&mul(coeff, &claim_at(addr)));
                        }
                        assert_eq!(
                            expected, cached,
                            "layer {config_idx} single-column cache relation for {cached_addr:?}"
                        );
                        n_checked += 1;
                    }
                    CR::VectorizedLookup(rel) => {
                        let mut expected = E::ZERO;
                        let mut ap = E::ONE;
                        for col in rel.columns.iter() {
                            let mut col_val = col.constant;
                            for (coeff, addr) in col.linear_terms.iter() {
                                col_val.add_assign(&mul(coeff, &claim_at(addr)));
                            }
                            expected.add_assign(&mul(&col_val, &ap));
                            ap.mul_assign(&lookup_alpha);
                        }
                        assert_eq!(
                            expected, cached,
                            "layer {config_idx} vector cache relation for {cached_addr:?}"
                        );
                        n_checked += 1;
                    }
                    CR::VectorizedLookupSetup(setup_addrs) => {
                        let mut expected = E::ZERO;
                        let mut ap = E::ONE;
                        for addr in setup_addrs.iter() {
                            expected.add_assign(&mul(&claim_at(addr), &ap));
                            ap.mul_assign(&lookup_alpha);
                        }
                        assert_eq!(
                            expected, cached,
                            "layer {config_idx} vector-setup cache relation for {cached_addr:?}"
                        );
                        n_checked += 1;
                    }
                    CR::MemoryTuple(rel) => {
                        // Tie the cached memory-tuple poly to its memory-column at-point evals
                        // via the permutation challenges (same expression as eval_memory_expr).
                        // NOTE: the verifier-generator SKIPS this check — see report; it is
                        // required for the InitialGrandProductFromCaches path to be sound.
                        let lin = &entry_challenges[0..6];
                        let mem = |off: usize| claim_at(&GKRAddress::BaseLayerMemory(off));
                        let mut result = entry_challenges[6]; // permutation additive part
                        match rel.address_space {
                            ASpace::Constant(c) => {
                                result.add_assign(&fu(c));
                            }
                            ASpace::IsRam(off) => {
                                result.add_assign(&mem(off));
                            }
                            ASpace::IsRegister(off) => {
                                let mut t = E::ONE;
                                t.sub_assign(&mem(off));
                                result.add_assign(&t);
                            }
                        }
                        match &rel.address {
                            Addr::ConstantU16(c) => {
                                result.add_assign(&mul(&lin[0], &fu(*c as u32)));
                            }
                            Addr::Constant(c) => {
                                result.add_assign(&mul(&lin[0], &fu(*c)));
                            }
                            Addr::U16Space(off) => {
                                result.add_assign(&mul(&lin[0], &mem(*off)));
                            }
                            Addr::U32Space([low, high]) => {
                                result.add_assign(&mul(&lin[0], &mem(*low)));
                                result.add_assign(&mul(&lin[1], &mem(*high)));
                            }
                            Addr::U32SpaceSpecialIndirect {
                                low_base,
                                low_dynamic_offset,
                                low_offset,
                                high,
                            } => {
                                let mut low = mem(*low_base);
                                low.add_assign(&fu(*low_offset));
                                if let Some((c, off)) = low_dynamic_offset {
                                    low.add_assign(&mul(&mem(*off), &fu(*c as u32)));
                                }
                                result.add_assign(&mul(&lin[0], &low));
                                result.add_assign(&mul(&lin[1], &mem(*high)));
                            }
                            Addr::U32SpaceGeneric(..) => {
                                panic!("U32SpaceGeneric memory tuple not supported")
                            }
                        }
                        match rel.timestamp {
                            Ts::Zero => {}
                            Ts::Normal(ts) => {
                                let mut ts_low = mem(ts[0]);
                                ts_low.add_assign(&fu(rel.timestamp_offset));
                                result.add_assign(&mul(&lin[2], &ts_low));
                                result.add_assign(&mul(&lin[3], &mem(ts[1])));
                            }
                        }
                        match rel.value {
                            Val::Zero => {}
                            Val::U16Limbs(v) => {
                                result.add_assign(&mul(&lin[4], &mem(v[0])));
                                result.add_assign(&mul(&lin[5], &mem(v[1])));
                            }
                            Val::U8Limbs(v) => {
                                for (ci, lo, hi) in [(4usize, v[0], v[1]), (5, v[2], v[3])] {
                                    let mut combined = mem(hi);
                                    combined.mul_assign(&fu(1 << 8));
                                    combined.add_assign(&mem(lo));
                                    result.add_assign(&mul(&lin[ci], &combined));
                                }
                            }
                        }
                        assert_eq!(
                            result, cached,
                            "layer {config_idx} memory-tuple cache relation for {cached_addr:?}"
                        );
                        n_checked += 1;
                    }
                }
            }
            if !layer.cached_relations.is_empty() {
                println!(
                    "[circuit-verify]   layer {config_idx} cache relations checked: {n_checked}/{}",
                    layer.cached_relations.len()
                );
            }
        }

        // ---- layer-0 virtual-setup closed-form checks: the VirtualSetup polys
        // (range-check-16/timestamp, inits/teardowns low/high) have a closed-form multilinear
        // evaluation at the folding point that must match their sent at-point eval. ----
        if config_idx == 0 {
            use crate::cs::definitions::VirtualSetupPoly as VSP;
            let n = new_point.len();
            let pt = &new_point;
            let dbl = |x: &mut E| {
                let c = *x;
                x.add_assign(&c);
            };
            let target_addrs: Vec<GKRAddress> = merged.keys().copied().collect();
            let claim_at = |addr: &GKRAddress| -> Option<E> {
                target_addrs
                    .iter()
                    .position(|a| a == addr)
                    .map(|i| claims[i])
            };
            // range check: (Σ_{k<bits} 2^k·pt[n-1-k]) · Π_{k=bits..n} (1 - pt[n-1-k])
            let range_check = |bits: usize| -> E {
                let mut result = E::ZERO;
                let mut prefactor = E::ONE;
                for k in 0..bits {
                    let mut t = pt[n - 1 - k];
                    t.mul_assign(&prefactor);
                    result.add_assign(&t);
                    dbl(&mut prefactor);
                }
                for k in bits..n {
                    let mut t = E::ONE;
                    t.sub_assign(&pt[n - 1 - k]);
                    result.mul_assign(&t);
                }
                result
            };
            let mut n_vs = 0usize;
            for (poly, bits) in [
                (VSP::RangeCheck16Bits, 16usize),
                (VSP::RangeCheckTimestamp, 19),
            ] {
                if let Some(cached) = claim_at(&GKRAddress::VirtualSetup(poly)) {
                    assert_eq!(range_check(bits), cached, "layer 0 virtual-setup {poly:?}");
                    n_vs += 1;
                }
            }
            // inits/teardowns: word_bits = 2, take_count = 16 - word_bits = 14.
            let word_bits = unified_circuit
                .memory_layout
                .inits_and_teardowns_word_bits
                .unwrap_or(2) as usize;
            let take_count = 16 - word_bits;
            let lo = claim_at(&GKRAddress::VirtualSetup(VSP::InitsAndTeardownsLow));
            let hi = claim_at(&GKRAddress::VirtualSetup(VSP::InitsAndTeardownsHigh));
            if lo.is_some() || hi.is_some() {
                // low half = Σ_{k<take_count} 2^{word_bits+k}·pt[n-1-k]
                let mut low_eval = E::ZERO;
                let mut prefactor = E::ONE;
                for _ in 0..word_bits {
                    dbl(&mut prefactor);
                }
                for k in 0..take_count {
                    let mut t = pt[n - 1 - k];
                    t.mul_assign(&prefactor);
                    low_eval.add_assign(&t);
                    dbl(&mut prefactor);
                }
                // high half = Σ_{k<n-take_count} 2^k·pt[n-1-take_count-k]
                let mut high_eval = E::ZERO;
                let mut prefactor = E::ONE;
                for k in 0..(n - take_count) {
                    let mut t = pt[n - 1 - take_count - k];
                    t.mul_assign(&prefactor);
                    high_eval.add_assign(&t);
                    dbl(&mut prefactor);
                }
                assert_eq!(
                    low_eval,
                    lo.unwrap(),
                    "layer 0 virtual-setup InitsAndTeardownsLow"
                );
                assert_eq!(
                    high_eval,
                    hi.unwrap(),
                    "layer 0 virtual-setup InitsAndTeardownsHigh"
                );
                n_vs += 2;
            }
            println!("[circuit-verify]   layer 0 virtual-setup checks: {n_vs}");
        }

        point = new_point;
        batching = next_batching;
        println!(
            "[circuit-verify] layer {config_idx} OK ({} gates, {} inputs, {} extra)",
            gates.len(),
            input_sorted.len(),
            extra.len()
        );
    }

    println!(
        "[circuit-verify] all circuit layers verified; seed = 0x{}",
        seed.0
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    );

    // ===== STEP 4: GKR→WHIR handoff — packed-commitment claims merge + WHIR batching =====
    // Mirrors prover/src/gkr/prover/mod.rs (MergedAndPackedMemoryAndWitness, lines 875-961).
    {
        let pack_log2 = 4usize; // this proof's pack_log2
        let base_layer_z = point.clone(); // 22-coord layer-0 folding point
        let get = |addr: GKRAddress| -> E {
            *layer0_merged.get(&addr).expect("base-layer claim present")
        };
        let num_mem = unified_circuit.memory_layout.total_width;
        let num_wit = unified_circuit.witness_layout.total_width;
        let num_setup = unified_circuit.generic_lookup_tables_width;
        // mem ++ wit claims (column order), and setup claims
        let mut mem_wit: Vec<E> = (0..num_mem)
            .map(|i| get(GKRAddress::BaseLayerMemory(i)))
            .collect();
        mem_wit.extend((0..num_wit).map(|i| get(GKRAddress::BaseLayerWitness(i))));
        let setup_claims: Vec<E> = (0..num_setup).map(|i| get(GKRAddress::Setup(i))).collect();

        // draw extra_coordinates (pack_log2), then merge
        let extra =
            draw_random_field_els::<Proth120, Proth120, Keccak256Transcript>(&mut seed, pack_log2);
        let merge = |input: &[E], extra: &[E]| -> Vec<E> {
            let pl = extra.len();
            let mut result = vec![];
            for chunk in input.chunks(1 << pl) {
                let mut v: Vec<E> = chunk.to_vec();
                v.resize(1 << pl, E::ZERO);
                for r in extra.iter().rev() {
                    let mut buf = Vec::with_capacity(v.len() / 2);
                    for pair in v.chunks(2) {
                        // canonical interpolation a + (b-a)*r
                        let mut t = pair[1];
                        t.sub_assign(&pair[0]);
                        t.mul_assign(r);
                        t.add_assign(&pair[0]);
                        buf.push(t);
                    }
                    v = buf;
                }
                result.push(v[0]);
            }
            result
        };
        let merged_mw = merge(&mem_wit, &extra);
        let merged_setup = merge(&setup_claims, &extra);

        // extended WHIR point = extra || base_layer_z (26 coords)
        let mut whir_point = extra.clone();
        whir_point.extend_from_slice(&base_layer_z);

        // draw WHIR batching challenge (1 el, PoW-gated); validate nonce vs the proof
        let pow = pow_bits::batched_proximity_check_pow_bits(
            SecurityLevel::Sec100.security_bits(),
            unified_circuit.trace_len.trailing_zeros() as usize,
            5, // base_lde_factor = 1<<5 (this proof's whir schedule)
            pow_bits::total_base_oracle_columns(&unified_circuit),
        );
        let (nonce, wbc) = draw_random_field_els_with_pow::<Proth120, Proth120, Keccak256Transcript>(
            &mut seed, 1, pow, &worker,
        );
        assert_eq!(
            nonce, proof.batched_proximity_check_pow_nonce,
            "WHIR batching PoW nonce must match the proof — confirms the handoff transcript"
        );
        let whir_batching = wbc[0];

        // batched opening value = Σ claim_i · batching^i over (mem_wit merged ++ setup merged)
        let mut batched = E::ZERO;
        let mut b = E::ONE;
        for c in merged_mw.iter().chain(merged_setup.iter()) {
            batched.add_assign(&mul(&b, c));
            b.mul_assign(&whir_batching);
        }

        println!(
            "[whir-handoff] pack_log2={pack_log2} extra={} mem_wit={}->{} setup={}->{} whir_point={} coords",
            extra.len(),
            mem_wit.len(),
            merged_mw.len(),
            setup_claims.len(),
            merged_setup.len(),
            whir_point.len()
        );
        println!(
            "[whir-handoff] whir_batching_pow_bits={pow} nonce={nonce} (matches proof) whir_batching=0x{:032x}",
            whir_batching.to_u128()
        );
        println!(
            "[whir-handoff] batched_opening_value=0x{:032x}",
            batched.to_u128()
        );
        // The seed WHIR starts from IS the GKR verifier's transcript state at the handoff
        // (this test runs the full GKR verifier in simulation). Save it to a file so the WHIR
        // fixture's preimage [seed:32] is authoritatively the GKR verifier's output — no guessing.
        let seed_hex: String = seed.0.iter().map(|b| format!("{b:02x}")).collect();
        std::fs::write(
            "../verifier_evm/debug_data/gkr_whir_handoff_seed.hex",
            &seed_hex,
        )
        .unwrap();
        println!("[whir-handoff] seed after batching draw = 0x{seed_hex}  (saved to gkr_whir_handoff_seed.hex)");

        // ---- serialize the WHIR verifier calldata from the REAL proof.whir_proof ----
        // Format = whir.sol VARIANT 4 (proth120_evm_gen::run_generation): preimage
        // [seed:32][batching:16][opening:16][z:26*16][witCap:CAP*32][setupCap:CAP*32]
        // then the proof stream. Base oracles: BCAP0 = merged mem+wit (memory_commitment,
        // 7 cols), BCAP1 = setup (setup_commitment, 1 col).
        {
            let wp = &proof.whir_proof;
            let folds = [2usize, 4, 4, 4, 4, 4];
            let queries = [17usize, 12, 8, 6, 5, 4];
            let num_rounds = folds.len();
            let be16 = |e: E| e.to_u128().to_be_bytes();
            let dig32 = |d: &[u32; 8]| -> [u8; 32] {
                let mut o = [0u8; 32];
                for i in 0..8 {
                    o[4 * i..4 * i + 4].copy_from_slice(&d[i].to_be_bytes());
                }
                o
            };
            let mut cd: Vec<u8> = vec![];
            // preimage
            cd.extend_from_slice(&seed.0);
            cd.extend_from_slice(&be16(whir_batching));
            cd.extend_from_slice(&be16(batched));
            for e in whir_point.iter() {
                cd.extend_from_slice(&be16(*e));
            }
            for d in wp.memory_commitment.commitment.cap.cap.iter() {
                cd.extend_from_slice(&dig32(d));
            }
            for d in wp.setup_commitment.commitment.cap.cap.iter() {
                cd.extend_from_slice(&dig32(d));
            }
            let plen = cd.len();
            // proof stream
            let push_leaf = |cd: &mut Vec<u8>, vals: &[E], path: &[[u32; 8]]| {
                for v in vals.iter() {
                    cd.extend_from_slice(&be16(*v));
                }
                for d in path.iter() {
                    cd.extend_from_slice(&dig32(d));
                }
            };
            let push_base = |cd: &mut Vec<u8>, vals: &[E], path: &[[u32; 8]], nc: usize| {
                let vp = vals.len() / nc;
                for c in 0..nc {
                    for o in 0..vp {
                        cd.extend_from_slice(&be16(vals[o * nc + c]));
                    }
                }
                for d in path.iter() {
                    cd.extend_from_slice(&dig32(d));
                }
            };
            let mut sc = 0usize;
            for r in 0..num_rounds {
                for _ in 0..folds[r] {
                    let sp = &wp.sumcheck_polys[sc];
                    sc += 1;
                    cd.extend_from_slice(&be16(sp[0]));
                    cd.extend_from_slice(&be16(sp[1]));
                    cd.extend_from_slice(&be16(sp[2]));
                }
                if r < num_rounds - 1 {
                    for d in wp.intermediate_whir_oracles[r].commitment.cap.cap.iter() {
                        cd.extend_from_slice(&dig32(d));
                    }
                    cd.extend_from_slice(&be16(wp.ood_samples[r]));
                    cd.extend_from_slice(&wp.pow_nonces[r].to_be_bytes());
                    for qq in 0..queries[r] {
                        if r == 0 {
                            let mq = &wp.memory_commitment.queries[qq];
                            push_base(
                                &mut cd,
                                &mq.leaf_values_concatenated,
                                &mq.path,
                                wp.memory_commitment.num_columns,
                            );
                            let sq = &wp.setup_commitment.queries[qq];
                            push_base(
                                &mut cd,
                                &sq.leaf_values_concatenated,
                                &sq.path,
                                wp.setup_commitment.num_columns,
                            );
                        } else {
                            let q = &wp.intermediate_whir_oracles[r - 1].queries[qq];
                            push_leaf(&mut cd, &q.leaf_values_concatenated, &q.path);
                        }
                    }
                } else {
                    for m in wp.final_monomials.iter() {
                        cd.extend_from_slice(&be16(*m));
                    }
                    cd.extend_from_slice(&wp.pow_nonces[r].to_be_bytes());
                    for qq in 0..queries[r] {
                        let q = &wp.intermediate_whir_oracles[num_rounds - 2].queries[qq];
                        push_leaf(&mut cd, &q.leaf_values_concatenated, &q.path);
                    }
                }
            }
            let hx: String = cd.iter().map(|b| format!("{b:02x}")).collect();
            std::fs::write(
                "../verifier_evm/debug_data/proth120_whir_calldata_from_proof.hex",
                &hx,
            )
            .unwrap();
            println!(
                "[whir-handoff] wrote WHIR calldata from real proof: {} bytes (preimage plen={}, {} cols mem / {} setup)",
                cd.len(), plen, wp.memory_commitment.num_columns, wp.setup_commitment.num_columns
            );
        }
    }

    // Emit the dim-reducing proof-data blob (processing order 21..=4): per layer,
    // folding_steps*[c0..c3] then 10*[lsb0,lsb1], all field els BE16. Consumed by the
    // Solidity dim-reducing verifier's forge test.
    let hex: String = blob.iter().map(|b| format!("{b:02x}")).collect();
    let path = "../verifier_evm/debug_data/gkr_dimreduce_data.hex";
    std::fs::write(path, &hex).unwrap();
    println!(
        "[dimreduce-verify] wrote {} bytes of proof data to {path}",
        blob.len()
    );

    // ===== CALLDATA SERIALIZER: assemble the full GKR-verifier calldata =====
    // gkr.sol stream order: preimage(520) ‖ output-evals(2560) ‖ dim-reduce blob(20160) ‖
    // per-circuit-layer (coeffs ‖ group-offset evals). This is exactly what the ported
    // gkr.sol reads (transcript_init ‖ gkr_init ‖ gkr_compress ‖ gkr_circuit).
    let td = "../verifier_evm/debug_data";
    let read_fixture = |name: &str| -> Vec<u8> {
        let h = std::fs::read_to_string(format!("{td}/{name}")).unwrap();
        (0..h.trim().len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&h.trim()[i..i + 2], 16).unwrap())
            .collect()
    };
    let mut calldata: Vec<u8> = vec![];
    calldata.extend_from_slice(&read_fixture("gkr_step1_preimage.hex")); // transcript preimage (916 B)
                                                                         // external-challenge PoW nonce (8 B BE): the verifier folds keccak(seed || nonce_be8) and
                                                                         // checks the top `pow_bits` bits are zero. Comes right after the preimage.
    calldata.extend_from_slice(&proof.lookup_challenges_pow_nonce.to_be_bytes());
    calldata.extend_from_slice(&read_fixture("gkr_step2_output_evals.hex")); // GKR entry outputs
    calldata.extend_from_slice(&blob); // dim-reducing data
    calldata.extend_from_slice(&circuit_blob); // circuit layers (coeffs + group-offset evals)
                                               // WHIR-batching PoW nonce (8 B BE) at the calldata tail: emit_gkr_mark folds
                                               // keccak(handoff_seed || nonce_be8), checks the top 11 bits are zero, then draws the
                                               // WHIR batching challenge. The verifier reads it at calldatasize()-8.
    calldata.extend_from_slice(&proof.batched_proximity_check_pow_nonce.to_be_bytes());
    let calldata_hex: String = calldata.iter().map(|b| format!("{b:02x}")).collect();
    std::fs::write(format!("{td}/gkr_full_calldata.hex"), &calldata_hex).unwrap();
    println!(
        "[calldata] wrote full GKR calldata: {} bytes (preimage 916 + nonce 8 + outputs 2560 + dimreduce {} + circuit {})",
        calldata.len(),
        blob.len(),
        circuit_blob.len()
    );
}

/// Dump the GKR proof's layer/round structure so I can port the dimension-reducing
/// (and later same-sized) layer verification to Solidity against a concrete layout.
#[test]
fn inspect_packed_proof_structure() {
    use crate::gkr::prover::GKRProof;

    let proof: GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap> = {
        let src = std::fs::File::open("unified_circuit_proof_proth120.json")
            .expect("run gkr_unified_packed_commitment_basic_fibonacci first");
        serde_json::from_reader(src).expect("deserialize proof")
    };

    println!(
        "[proof] inits_and_teardowns_top_bits = {:?}",
        proof.inits_and_teardowns_top_bits
    );
    println!(
        "[proof] lookup_challenges_pow_nonce = {}",
        proof.lookup_challenges_pow_nonce
    );
    println!(
        "[proof] batched_proximity_check_pow_nonce = {}",
        proof.batched_proximity_check_pow_nonce
    );
    println!(
        "[proof] grand_product_accumulator_computed = 0x{:032x}",
        proof.grand_product_accumulator_computed.to_u128()
    );

    println!(
        "[proof] final_explicit_evaluations ({} outputs):",
        proof.final_explicit_evaluations.len()
    );
    for (out_ty, vals) in proof.final_explicit_evaluations.iter() {
        println!(
            "    {out_ty:?}: [{}, {}] elems",
            vals[0].len(),
            vals[1].len()
        );
    }

    println!(
        "[proof] sumcheck_intermediate_values: {} layers (keys {:?})",
        proof.sumcheck_intermediate_values.len(),
        proof
            .sumcheck_intermediate_values
            .keys()
            .collect::<Vec<_>>()
    );
    for (layer, v) in proof.sumcheck_intermediate_values.iter() {
        println!(
            "    layer {layer}: num_rounds={} round_coeffs=[E;4]x{} final_step_evals={}(keys {:?}) extra_cache_evals={}",
            v.sumcheck_num_rounds,
            v.internal_round_coefficients.len(),
            v.final_step_evaluations.len(),
            v.final_step_evaluations.keys().take(4).collect::<Vec<_>>(),
            v.extra_evaluations_from_caching_relations.len(),
        );
    }

    let w = &proof.whir_proof;
    println!(
        "[proof] whir: setup_cap={} mem_cap={} wit_cap={} intermediate_oracles={} ood={} sumcheck_polys={} final_monomials={}",
        w.setup_commitment.commitment.cap.cap.len(),
        w.memory_commitment.commitment.cap.cap.len(),
        w.witness_commitment.commitment.cap.cap.len(),
        w.intermediate_whir_oracles.len(),
        w.ood_samples.len(),
        w.sumcheck_polys.len(),
        w.final_monomials.len(),
    );
}

/// Per-layer relation-type histogram for the standard (circuit) GKR layers, to scope
/// the Solidity per-gate code-generation for STEP 3.
#[test]
fn inspect_circuit_layer_relations() {
    let unified_circuit: GKRCircuitArtifact<Proth120> = serde_json::from_reader(
        std::fs::File::open(
            "../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
        )
        .unwrap(),
    )
    .unwrap();
    println!(
        "[relations] {} standard layers",
        unified_circuit.layers.len()
    );
    for (li, layer) in unified_circuit.layers.iter().enumerate() {
        let gates: Vec<_> = layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
            .collect();
        let mut hist: std::collections::BTreeMap<String, usize> = Default::default();
        for g in &gates {
            let dbg = format!("{:?}", g.enforced_relation);
            let name = dbg
                .split([' ', '{', '('])
                .next()
                .unwrap_or(&dbg)
                .to_string();
            *hist.entry(name).or_default() += 1;
        }
        println!(
            "  layer {li}: {} gates ({} plain + {} external), {} cached relations",
            gates.len(),
            layer.gates.len(),
            layer.gates_with_external_connections.len(),
            layer.cached_relations.len(),
        );
        for (name, n) in &hist {
            println!("      {n:>4}  {name}");
        }
    }
}

/// Inlined analogue of `orchestration::unified::build_unified_full_trace`, but with
/// the delegation CSRs removed from the preprocessing supported-CSR set (precompiles
/// disabled at preprocessing) and without the optional memory-consistency cross-check.
fn build_unified_trace_without_precompiles<C, F: PrimeField>(
    vm: &VmRunOutput<C>,
    witness_eval_fn_ptr: fn(&mut ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, F>),
    unified_circuit: &GKRCircuitArtifact<F>,
    num_teardown_sets: usize,
    cycles_per_chunks: usize,
    worker: &Worker,
) -> (
    GKRFullWitnessTrace<F, Global, Global>,
    TableDriver<F>,
    Vec<Option<ExecutorFamilyDecoderData>>,
    Vec<u32>,
)
where
    C: Counters + Copy + Default + PartialEq + std::fmt::Debug,
{
    let num_calls = vm
        .counters
        .get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>();
    println!("Replaying {} cycles for witness data", num_calls);
    // Replay the captured trace into the unified destination holder.
    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut replay_ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![UnifiedOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = UnifiedDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut replay_ram,
        &vm.tape,
        &mut (),
        vm.cycles_bound,
        &mut tracer,
    );
    assert_eq!(vm.expected_final_state(), state);

    // Preprocessing WITHOUT any delegation CSRs => no precompiles.
    println!("Creating decoder table");
    let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> = vec![Box::new(UnifiedReducedMachineDecoder)];
    const SUPPORTED_CSRS: &[u16] = &[common_constants::NON_DETERMINISM_CSR as u16];
    let mut preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        ReducedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &decoders,
        common_constants::ROM_WORD_SIZE,
        SUPPORTED_CSRS,
    );
    let decoder_table = preprocessing_data
        .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .expect("UnifiedReducedMachineDecoder must produce a family-128 entry");

    bincode_serialize_to_file(&buffer, "unified_proth120_witness.bin");

    let oracle = UnifiedRiscvCircuitOracle {
        inner: &buffer,
        decoder_table: &decoder_table,
    };
    let unified_table_driver = build_unified_table_driver::<F>(&vm.binary);

    println!("Collecting inits and teardowns");

    // // Inits/teardown columns sized to the unified circuit's set count.
    // let mut inits_and_teardowns = Vec::with_capacity(num_teardown_sets);
    // for _ in 0..num_teardown_sets {
    //     let a = Vec::with_capacity(1 << TRACE_LEN_LOG2);
    //     let b = Vec::with_capacity(1 << TRACE_LEN_LOG2);
    //     let c = Vec::with_capacity(1 << TRACE_LEN_LOG2);
    //     let d = Vec::with_capacity(1 << TRACE_LEN_LOG2);
    //     inits_and_teardowns.push(([a, b], [c, d]));
    // }
    // vm.ram.collect_inits_and_teardowns_into_columns::<F, _>(
    //     worker,
    //     TRACE_LEN_LOG2,
    //     0,
    //     &mut inits_and_teardowns,
    // );

    // we should collect carefully here, as regions will not be continuous
    let max_ram_touch = vm
        .shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.iter().map(|el| el.0).max().unwrap_or(0))
        .max()
        .expect("max address touched");
    assert_eq!(max_ram_touch % 4, 0);
    let mut inits_and_teardowns = vm.ram.collect_inits_and_teardowns_sets::<F, Global>(
        worker,
        TRACE_LEN_LOG2,
        num_teardown_sets,
        Some(((max_ram_touch as usize) + 4) / 4),
    );
    assert_eq!(inits_and_teardowns.len(), 1);
    let (top_bits, inits_and_teardowns_chunks) = inits_and_teardowns
        .drain(..1)
        .next()
        .expect("inits and teardowns");
    assert_eq!(top_bits.len(), num_teardown_sets);

    println!("Calculating full witness trace");

    let full_trace = evaluate_gkr_witness_for_executor_family::<F, _, _, _>(
        unified_circuit,
        witness_eval_fn_ptr,
        cycles_per_chunks,
        &oracle,
        &unified_table_driver,
        worker,
        Some(inits_and_teardowns_chunks),
        Global,
        Global,
    );

    (full_trace, unified_table_driver, decoder_table, top_bits)
}
