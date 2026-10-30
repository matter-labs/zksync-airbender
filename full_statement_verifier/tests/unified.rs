#![cfg(all(feature = "verifiers", feature = "proof_utils"))]

use std::collections::BTreeMap;

use common_constants::{
    BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, BLAKE2S_DELEGATION_CSR_REGISTER,
    BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER,
    REDUCED_MACHINE_CIRCUIT_FAMILY_IDX,
};
use full_statement_verifier::pessimistic_conjecture::verify_unified_circuit_base_layer;
use full_statement_verifier::program_proof::ProgramProof;
use verifier_common::cs::gkr_compiler::GKRCircuitArtifact;
use verifier_common::errors::DebugErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::prover::definitions::{MerkleTreeCap, DEFAULT_CAP_SIZE};
use verifier_common::prover::fsv_fixture::UnifiedBaseLayerComponents;
use verifier_common::BlakeMode;

fn load_compiled_circuit(name: &str) -> GKRCircuitArtifact<BabyBearField> {
    let path = format!(
        "{}/../cs/compiled_circuits/{name}_layout_gkr.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let file =
        std::fs::File::open(&path).unwrap_or_else(|e| panic!("open compiled circuit {path}: {e}"));
    serde_json::from_reader(std::io::BufReader::new(file)).expect("deserialize compiled circuit")
}

fn delegation_circuit_name(csr: u32) -> &'static str {
    match csr {
        BLAKE2S_DELEGATION_CSR_REGISTER => "blake2_with_extended_control",
        BIGINT_OPS_WITH_CONTROL_CSR_REGISTER => "bigint_with_extended_control",
        KECCAK_SPECIAL5_CSR_REGISTER => "keccak_special5",
        BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER => "blake2_g_function",
        other => panic!("unknown delegation csr {other}"),
    }
}

/// Must match the variant the fixture was proven with.
const REDUCED_ROUNDS: bool = true;

const FIXTURE_PATH: &str = "tests/fixtures/unified_base_layer_fixture_sec_100.json";

fn load_bundle() -> UnifiedBaseLayerComponents {
    let file = std::fs::File::open(FIXTURE_PATH).unwrap_or_else(|e| {
        panic!("open fixture {FIXTURE_PATH}: {e} (generate it via the prover step)")
    });
    let bundle: UnifiedBaseLayerComponents = serde_json::from_reader(std::io::BufReader::new(file))
        .expect("deserialize unified fixture bundle");
    for delegation in &bundle.delegations {
        assert!(
            full_statement_verifier::definitions::DELEGATION_TYPES
                .contains(&delegation.delegation_csr),
            "fixture contains delegation CSR {:#x} unsupported by the FSV registry",
            delegation.delegation_csr,
        );
    }
    // The prover harness mirrors the PoW-bits derivation (it cannot depend on verifier_common);
    // catch any drift here with a clear message instead of a transcript PoW panic.
    assert_eq!(
        bundle.pow_bits as usize,
        full_statement_verifier::MEMORY_DELEGATION_POW_BITS,
        "fixture was drawn with a different memory/delegation PoW than the FSV expects; \
         update the prover harness's `memory_delegation_pow_bits`"
    );
    bundle
}

fn assemble(
    bundle: UnifiedBaseLayerComponents,
) -> (ProgramProof, MerkleTreeCap<{ DEFAULT_CAP_SIZE }>) {
    assemble_with(bundle, 1, 1)
}

fn assemble_with(
    bundle: UnifiedBaseLayerComponents,
    num_instances: usize,
    num_it_circuits: u32,
) -> (ProgramProof, MerkleTreeCap<{ DEFAULT_CAP_SIZE }>) {
    let reduced_machine_idx = REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as u32;

    let instances = vec![bundle.unified_proof; num_instances];
    let mut riscv_proofs = BTreeMap::new();
    riscv_proofs.insert(reduced_machine_idx, instances);
    let mut compiled_riscv_circuits = BTreeMap::new();
    compiled_riscv_circuits.insert(
        reduced_machine_idx,
        load_compiled_circuit("unified_reduced_machine"),
    );

    let mut delegation_proofs = BTreeMap::new();
    let mut compiled_delegation_circuits = BTreeMap::new();
    for d in bundle.delegations {
        compiled_delegation_circuits.insert(
            d.delegation_csr,
            load_compiled_circuit(delegation_circuit_name(d.delegation_csr)),
        );
        delegation_proofs.insert(d.delegation_csr, vec![d.proof]);
    }

    let proof = ProgramProof {
        riscv_proofs,
        compiled_riscv_circuits,
        inits_and_teardown_proofs: vec![],
        inits_and_teardowns_circuit: None,
        delegation_proofs,
        compiled_delegation_circuits,
        register_final_values: bundle.register_final_values,
        final_pc: bundle.final_pc,
        final_timestamp: bundle.final_timestamp,
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

fn run_unified_base_layer(responses: Vec<u32>) -> Result<[u32; 16], ()> {
    std::thread::Builder::new()
        .name("fsv unified verifier".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            let mut src = responses.into_iter();
            verify_unified_circuit_base_layer::<_, DebugErrorCreator, REDUCED_ROUNDS>(&mut src)
        })
        .expect("spawn verifier thread")
        .join()
        // a panic (failed internal assertion) joins as Err → treat as rejection
        .map_err(|_| ())
        // an ErrorCreator error is also a rejection
        .and_then(|r| r.map_err(|_| ()))
}

#[test]
#[ignore = "requires generated unified base-layer fixture (run the prover step)"]
fn unified_base_layer_accepts_valid_proof() {
    let (proof, setup_cap) = assemble(load_bundle());
    let responses = build_stream(&proof, &setup_cap, verifier_common::BLAKE_MODE);
    let result = run_unified_base_layer(responses);
    assert!(result.is_ok(), "valid unified base-layer proof must verify");
}

#[test]
#[ignore = "requires generated unified base-layer fixture (run the prover step)"]
fn unified_base_layer_rejects_corrupted_stream() {
    let (proof, setup_cap) = assemble(load_bundle());
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

    let result = run_unified_base_layer(corrupted);
    assert!(result.is_err(), "corrupted unified stream must be rejected");
}

#[test]
#[ignore = "requires generated unified base-layer fixture (run the prover step)"]
fn rejects_corrupted_setup_cap() {
    let (proof, setup_cap) = assemble(load_bundle());
    let prefix_len = MerkleTreeCap::flatten_single(&setup_cap).len();
    let mut corrupted = build_stream(&proof, &setup_cap, verifier_common::BLAKE_MODE);
    assert!(prefix_len > 0, "setup-cap prefix must be non-empty");
    corrupted[prefix_len / 2] ^= 0x5555_5555;

    let result = run_unified_base_layer(corrupted);
    assert!(result.is_err(), "corrupted setup-cap VK must be rejected");
}

#[test]
#[ignore = "requires generated unified base-layer fixture (run the prover step)"]
fn rejects_tampered_final_register_state() {
    let (proof, setup_cap) = assemble(load_bundle());
    let prefix_len = MerkleTreeCap::flatten_single(&setup_cap).len();
    let mut corrupted = build_stream(&proof, &setup_cap, verifier_common::BLAKE_MODE);
    corrupted[prefix_len + 3] ^= 0x5555_5555;

    let result = run_unified_base_layer(corrupted);
    assert!(
        result.is_err(),
        "tampered final register state must be rejected (Fiat-Shamir binding)"
    );
}

#[test]
#[ignore = "requires generated unified base-layer fixture (run the prover step)"]
fn rejects_num_it_circuits_zero() {
    let (proof, setup_cap) = assemble_with(load_bundle(), 1, 0);
    let result = run_unified_base_layer(build_stream(
        &proof,
        &setup_cap,
        verifier_common::BLAKE_MODE,
    ));
    assert!(result.is_err(), "num_it_circuits = 0 must be rejected");
}

#[test]
#[ignore = "requires generated unified base-layer fixture (run the prover step)"]
fn rejects_num_it_circuits_exceeds_num_circuits() {
    let (proof, setup_cap) = assemble_with(load_bundle(), 1, 2);
    let result = run_unified_base_layer(build_stream(
        &proof,
        &setup_cap,
        verifier_common::BLAKE_MODE,
    ));
    assert!(
        result.is_err(),
        "num_it_circuits > num_circuits must be rejected"
    );
}

#[test]
#[ignore = "requires generated unified base-layer fixture (run the prover step)"]
fn rejects_duplicated_multi_instance() {
    let (proof, setup_cap) = assemble_with(load_bundle(), 2, 2);
    let result = run_unified_base_layer(build_stream(
        &proof,
        &setup_cap,
        verifier_common::BLAKE_MODE,
    ));
    assert!(
        result.is_err(),
        "a duplicated 2-instance proof must be rejected"
    );
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
#[ignore = "requires generated fixture + RISC-V binary (run the prover + binaries steps)"]
fn unified_base_layer_transpiler_accepts_valid_proof() {
    use common_constants::rom::ROM_SECOND_WORD_BITS;
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::ir::simple_instruction_set::*;
    use riscv_transpiler::ir::ReducedMachineDecoderConfig;
    use riscv_transpiler::vm::*;
    use verifier_common::field::baby_bear::base::BabyBearField;

    let (proof, setup_cap) = assemble(load_bundle());
    // The FSV binary reads the whole stream itself (setup-cap VK first, then the flattened proof
    // which already carries the external challenges) — no separate external-challenges prefix.
    let oracle_responses = build_stream(&proof, &setup_cap, BlakeMode::Compression);
    let expected_output = run_unified_base_layer(build_stream(
        &proof,
        &setup_cap,
        verifier_common::BLAKE_MODE,
    ))
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

/// The pinned unified base-layer guest, run through `host_utils::measure_fsv_execution`,
/// returns what the native verifier returns; tampering the proof body, the setup-cap VK or the
/// final register state never yields a success record.
#[cfg(feature = "host_utils")]
#[test]
fn unified_base_layer_guest_execution_is_measured_and_rejects_tampering() {
    use full_statement_verifier::host_utils::{
        canonical_fsv_dir, load_fsv_exact, measure_fsv_execution, FsvExecutionFailure,
    };
    use verifier_common::fsv_binaries::{FsvDescriptor, FsvProgram, SecurityLevel, SoundnessMode};

    let (proof, setup_cap) = assemble(load_bundle());
    let expected = run_unified_base_layer(build_stream(
        &proof,
        &setup_cap,
        verifier_common::BLAKE_MODE,
    ))
    .expect("fixture must verify natively");
    let guest = load_fsv_exact(
        canonical_fsv_dir(),
        &FsvDescriptor::new(
            SecurityLevel::Sec100,
            SoundnessMode::PessimisticConjecture,
            FsvProgram::UnifiedBaseLayer,
            BlakeMode::Compression,
        ),
    )
    .unwrap_or_else(|err| panic!("{err}"));

    let stream = build_stream(&proof, &setup_cap, BlakeMode::Compression);
    let record =
        measure_fsv_execution(&guest, stream.clone()).unwrap_or_else(|err| panic!("{err}"));
    assert_eq!(record.output, expected);
    assert_eq!(record.digest, guest.digest());
    assert_eq!(record.stream_words, stream.len());
    assert!(record.cycles > 0);
    println!("unified base layer guest: {} cycles", record.cycles);

    let prefix_len = MerkleTreeCap::flatten_single(&setup_cap).len();
    for idx in [
        prefix_len + (stream.len() - prefix_len) / 2,
        prefix_len / 2,
        prefix_len + 3,
    ] {
        let mut tampered = stream.clone();
        tampered[idx] ^= 0x5555_5555;
        let err =
            measure_fsv_execution(&guest, tampered).expect_err("a tampered stream must not return");
        assert!(
            matches!(
                err.failure,
                FsvExecutionFailure::Aborted { .. } | FsvExecutionFailure::WrongTerminal { .. }
            ),
            "word {idx}: {err}"
        );
    }
}
