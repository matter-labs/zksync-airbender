#![cfg(all(feature = "verifiers", feature = "proof_utils"))]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use common_constants::{BLAKE2S_DELEGATION_CSR_REGISTER, REDUCED_MACHINE_CIRCUIT_FAMILY_IDX};
use full_statement_verifier::program_proof::ProgramProof;
use prover::definitions::SoundnessMode;
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::DefaultTreeConstructor;
use prover::tests::gkr::orchestration::canonical_fixtures::{
    capture_canonical_inputs, compression_pair_external_challenges, CanonicalBoundary,
    CanonicalCircuit,
};
use prover::worker::Worker;
use verifier_common::errors::DebugErrorCreator;
use verifier_common::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use verifier_common::prover::definitions::{MerkleTreeCap, DEFAULT_CAP_SIZE};
use verifier_common::BlakeMode;

type Proof = GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>;

const REDUCED_ROUNDS: bool = true;

struct CanonicalBundle {
    unified_proof: Proof,
    compression_proof: Proof,
    boundary: CanonicalBoundary,
    unified_setup_cap: MerkleTreeCap<DEFAULT_CAP_SIZE>,
    pow_challenge: u64,
}

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_owned()
}

fn load_bundle(mode: SoundnessMode) -> CanonicalBundle {
    let root = root();
    let load = |circuit: CanonicalCircuit| -> Proof {
        let proof: Proof = proof_fixtures::read_file(circuit.proof_path(&root, mode));
        assert_eq!(
            proof.whir_proof.whir_schedule,
            circuit.prover_config(&root, mode).whir_schedule
        );
        proof
    };
    let unified_proof = load(CanonicalCircuit::UnifiedReducedMachine);
    let compression_proof = load(CanonicalCircuit::Blake2WithExtendedControl);
    let worker = Worker::new_with_num_threads(8);
    let inputs = capture_canonical_inputs(&root, CanonicalCircuit::UnifiedReducedMachine, &worker);
    let top_bits = &inputs.inits_and_teardowns.as_ref().unwrap().top_bits;
    assert_eq!(*top_bits, unified_proof.inits_and_teardowns_top_bits);
    let challenges = compression_pair_external_challenges(
        &inputs.boundary,
        top_bits,
        &unified_proof.whir_proof.memory_commitment.commitment.cap,
        &compression_proof
            .whir_proof
            .memory_commitment
            .commitment
            .cap,
        &worker,
    );
    for proof in [&unified_proof, &compression_proof] {
        assert_eq!(
            serde_json::to_value(challenges.external_challenges).unwrap(),
            serde_json::to_value(proof.external_challenges).unwrap(),
            "canonical pair must bind the replayed boundary",
        );
    }
    assert_eq!(
        challenges.pow_bits as usize,
        full_statement_verifier::MEMORY_DELEGATION_POW_BITS
    );
    let unified_setup_cap = MerkleTreeCap {
        cap: unified_proof
            .whir_proof
            .setup_commitment
            .commitment
            .cap
            .cap
            .clone()
            .try_into()
            .unwrap(),
    };
    CanonicalBundle {
        unified_proof,
        compression_proof,
        boundary: inputs.boundary,
        unified_setup_cap,
        pow_challenge: challenges.pow_challenge,
    }
}

fn assemble(bundle: CanonicalBundle) -> (ProgramProof, MerkleTreeCap<DEFAULT_CAP_SIZE>) {
    assemble_with(bundle, 1, 1)
}

fn assemble_with(
    bundle: CanonicalBundle,
    num_instances: usize,
    num_it_circuits: u32,
) -> (ProgramProof, MerkleTreeCap<DEFAULT_CAP_SIZE>) {
    let root = root();
    let family = REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32;
    let proof = ProgramProof {
        riscv_proofs: BTreeMap::from([(family, vec![bundle.unified_proof; num_instances])]),
        compiled_riscv_circuits: BTreeMap::from([(
            family,
            CanonicalCircuit::UnifiedReducedMachine.compiled_circuit(&root),
        )]),
        inits_and_teardown_proofs: vec![],
        inits_and_teardowns_circuit: None,
        delegation_proofs: BTreeMap::from([(
            BLAKE2S_DELEGATION_CSR_REGISTER,
            vec![bundle.compression_proof],
        )]),
        compiled_delegation_circuits: BTreeMap::from([(
            BLAKE2S_DELEGATION_CSR_REGISTER,
            CanonicalCircuit::Blake2WithExtendedControl.compiled_circuit(&root),
        )]),
        register_final_values: bundle.boundary.registers.to_vec(),
        final_pc: bundle.boundary.final_pc,
        final_timestamp: bundle.boundary.final_timestamp,
        end_params: [0u32; 8],
        recursion_chain_preimage: None,
        recursion_chain_hash: None,
        pow_challenge: bundle.pow_challenge,
        num_it_circuits: Some(num_it_circuits),
    };
    (proof, bundle.unified_setup_cap)
}

/// The guest's input stream: the setup-cap VK, then the proof flattened for the blake
/// implementation of the verifier that will read it (the native verifier is
/// `verifier_common::BLAKE_MODE`; the RISC-V FSV binary is a blake2_with_compression build, so
/// its query openings are full Merkle paths, not multiproofs).
fn build_stream(
    proof: &ProgramProof,
    setup_cap: &MerkleTreeCap<{ DEFAULT_CAP_SIZE }>,
    blake: BlakeMode,
) -> Vec<u32> {
    let mut responses = MerkleTreeCap::flatten_single(setup_cap).to_vec();
    responses.extend(proof.flatten_unified_for_verification(blake));
    responses
}

fn run_unified_base_layer(mode: SoundnessMode, responses: Vec<u32>) -> Result<[u32; 16], ()> {
    std::thread::Builder::new()
        .name("fsv unified verifier".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            let mut src = responses.into_iter();
            match mode {
                SoundnessMode::PessimisticConjecture => full_statement_verifier::pessimistic_conjecture::verify_unified_circuit_base_layer::<_, DebugErrorCreator, REDUCED_ROUNDS>(&mut src),
                SoundnessMode::EthproofsSoundnessCalc => full_statement_verifier::ethproofs_soundcalc::verify_unified_circuit_base_layer::<_, DebugErrorCreator, REDUCED_ROUNDS>(&mut src),
            }
        })
        .expect("spawn verifier thread")
        .join()
        // a panic (failed internal assertion) joins as Err → treat as rejection
        .map_err(|_| ())
        // an ErrorCreator error is also a rejection
        .and_then(|r| r.map_err(|_| ()))
}

#[test]
fn unified_base_layer_accepts_valid_proof() {
    for &mode in SoundnessMode::ALL {
        let (proof, setup_cap) = assemble(load_bundle(mode));
        let responses = build_stream(&proof, &setup_cap, verifier_common::BLAKE_MODE);
        let result = run_unified_base_layer(mode, responses);
        assert!(result.is_ok(), "valid unified base-layer proof must verify");
    }
}

#[test]
fn unified_base_layer_rejects_corrupted_stream() {
    for &mode in SoundnessMode::ALL {
        let (proof, setup_cap) = assemble(load_bundle(mode));
        let responses = build_stream(&proof, &setup_cap, verifier_common::BLAKE_MODE);

        // Corrupt a word inside the proof body, past the setup-cap VK prefix.
        let prefix_len = MerkleTreeCap::flatten_single(&setup_cap).len();
        let mut corrupted = responses.clone();
        assert!(
            corrupted.len() > prefix_len,
            "stream must contain a proof body"
        );
        let idx = prefix_len + (corrupted.len() - prefix_len) / 2;
        corrupted[idx] ^= 0x5555_5555;

        let result = run_unified_base_layer(mode, corrupted);
        assert!(result.is_err(), "corrupted unified stream must be rejected");
    }
}

#[test]
fn rejects_corrupted_setup_cap() {
    for &mode in SoundnessMode::ALL {
        let (proof, setup_cap) = assemble(load_bundle(mode));
        let prefix_len = MerkleTreeCap::flatten_single(&setup_cap).len();
        let mut corrupted = build_stream(&proof, &setup_cap, verifier_common::BLAKE_MODE);
        assert!(prefix_len > 0, "setup-cap prefix must be non-empty");
        corrupted[prefix_len / 2] ^= 0x5555_5555;

        let result = run_unified_base_layer(mode, corrupted);
        assert!(result.is_err(), "corrupted setup-cap VK must be rejected");
    }
}

#[test]
fn rejects_tampered_final_register_state() {
    for &mode in SoundnessMode::ALL {
        let (proof, setup_cap) = assemble(load_bundle(mode));
        let prefix_len = MerkleTreeCap::flatten_single(&setup_cap).len();
        let mut corrupted = build_stream(&proof, &setup_cap, verifier_common::BLAKE_MODE);
        corrupted[prefix_len + 3] ^= 0x5555_5555;

        let result = run_unified_base_layer(mode, corrupted);
        assert!(
            result.is_err(),
            "tampered final register state must be rejected (Fiat-Shamir binding)"
        );
    }
}

#[test]
fn rejects_num_it_circuits_zero() {
    for &mode in SoundnessMode::ALL {
        let (proof, setup_cap) = assemble_with(load_bundle(mode), 1, 0);
        let result = run_unified_base_layer(
            mode,
            build_stream(&proof, &setup_cap, verifier_common::BLAKE_MODE),
        );
        assert!(result.is_err(), "num_it_circuits = 0 must be rejected");
    }
}

#[test]
fn rejects_num_it_circuits_exceeds_num_circuits() {
    for &mode in SoundnessMode::ALL {
        let (proof, setup_cap) = assemble_with(load_bundle(mode), 1, 2);
        let result = run_unified_base_layer(
            mode,
            build_stream(&proof, &setup_cap, verifier_common::BLAKE_MODE),
        );
        assert!(
            result.is_err(),
            "num_it_circuits > num_circuits must be rejected"
        );
    }
}

#[test]
fn rejects_duplicated_multi_instance() {
    for &mode in SoundnessMode::ALL {
        let (proof, setup_cap) = assemble_with(load_bundle(mode), 2, 2);
        let result = run_unified_base_layer(
            mode,
            build_stream(&proof, &setup_cap, verifier_common::BLAKE_MODE),
        );
        assert!(
            result.is_err(),
            "a duplicated 2-instance proof must be rejected"
        );
    }
}

fn fsv_elf_path() -> String {
    format!(
        "{}/../tools/gkr_verifier/full_statement_verifiers/fsv_unified_base_layer_sec_100.elf",
        env!("CARGO_MANIFEST_DIR"),
    )
}

#[allow(dead_code)]
fn load_binary_section(path: &str) -> Vec<u32> {
    let bytes = std::fs::read(path).unwrap_or_else(|_| {
        panic!("Missing {path} — run `cd tools/gkr_verifier && ./dump_bin.sh` (or gkr_test.sh `binaries`)")
    });
    assert!(
        bytes.len().is_multiple_of(4),
        "binary section not word-aligned"
    );
    bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect()
}

#[test]
#[ignore = "requires the committed FSV RISC-V binary"]
fn unified_base_layer_transpiler_accepts_valid_proof() {
    let mode = SoundnessMode::DEFAULT;
    use common_constants::rom::ROM_SECOND_WORD_BITS;
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::ir::simple_instruction_set::*;
    use riscv_transpiler::ir::ReducedMachineDecoderConfig;
    use riscv_transpiler::vm::*;
    use verifier_common::field::baby_bear::base::BabyBearField;

    let (proof, setup_cap) = assemble(load_bundle(mode));
    // The FSV binary reads the whole stream itself (setup-cap VK first, then the flattened proof
    // which already carries the external challenges) — no separate external-challenges prefix.
    let oracle_responses = build_stream(&proof, &setup_cap, BlakeMode::Compression);
    let expected_output = run_unified_base_layer(
        mode,
        build_stream(&proof, &setup_cap, verifier_common::BLAKE_MODE),
    )
    .expect("fixture must verify natively before the transpiler run");

    let elf_path = fsv_elf_path();
    assert!(
        std::path::Path::new(&elf_path).exists(),
        "Missing {elf_path} — run `cd tools/gkr_verifier && ./dump_bin.sh fsv_unified_base_layer_sec_100` (or gkr_test.sh `binaries`)"
    );
    let (binary, text_section) =
        riscv_transpiler::elf::load_legacy_program(std::path::Path::new(&elf_path));

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);

    let cycles_bound = 1 << 24;
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<
        DelegationsAndFamiliesCounters,
        { ROM_SECOND_WORD_BITS },
    >::new_with_cycle_limit(cycles_bound, state);
    let mut non_determinism = QuasiUARTSource::new_with_reads(oracle_responses);

    let finished = VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, BabyBearField>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(
        finished,
        "FSV transpiler run did not finish (PC stuck or cycle bound reached)"
    );

    let actual_output: [u32; 16] = std::array::from_fn(|i| state.registers[10 + i].value);
    assert_eq!(
        actual_output, expected_output,
        "FSV transpiler must preserve the verified output and recursion hash"
    );

    let exact_cycles =
        (state.timestamp - common_constants::INITIAL_TIMESTAMP) / common_constants::TIMESTAMP_STEP;
    println!("FSV unified base layer: finished in {exact_cycles} transpiler cycles");
}
