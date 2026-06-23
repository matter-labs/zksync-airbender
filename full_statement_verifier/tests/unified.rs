#![cfg(all(feature = "verifiers", feature = "proof_utils"))]

use std::collections::BTreeMap;

use common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
use full_statement_verifier::program_proof::ProgramProof;
use full_statement_verifier::unified_circuit_statement::verify_unified_circuit_base_layer;
use verifier_common::errors::DebugErrorCreator;
use verifier_common::prover::definitions::{MerkleTreeCap, DEFAULT_CAP_SIZE};
use verifier_common::prover::fsv_fixture::UnifiedBaseLayerComponents;
use verifier_common::prover::nd_source_std::{set_iterator, ThreadLocalBasedSource};

/// Must match the variant the fixture was proven with.
const REDUCED_ROUNDS: bool = true;

const FIXTURE_PATH: &str = "tests/fixtures/unified_base_layer_fixture_sec_80.json";

fn load_bundle() -> UnifiedBaseLayerComponents {
    let file = std::fs::File::open(FIXTURE_PATH).unwrap_or_else(|e| {
        panic!("open fixture {FIXTURE_PATH}: {e} (generate it via the prover step)")
    });
    serde_json::from_reader(std::io::BufReader::new(file))
        .expect("deserialize unified fixture bundle")
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
    compiled_riscv_circuits.insert(reduced_machine_idx, bundle.compiled_unified_circuit);

    let mut delegation_proofs = BTreeMap::new();
    let mut compiled_delegation_circuits = BTreeMap::new();
    for d in bundle.delegations {
        delegation_proofs.insert(d.delegation_csr, vec![d.proof]);
        compiled_delegation_circuits.insert(d.delegation_csr, d.compiled_circuit);
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
        pow_challenge: 0,
        num_it_circuits: Some(num_it_circuits),
    };

    (proof, bundle.unified_setup_cap)
}

fn build_stream(proof: &ProgramProof, setup_cap: &MerkleTreeCap<{ DEFAULT_CAP_SIZE }>) -> Vec<u32> {
    let mut responses = MerkleTreeCap::flatten_single(setup_cap).to_vec();
    responses.extend(proof.flatten_unified_for_verification());
    responses
}

fn run_unified_base_layer(responses: Vec<u32>) -> Result<[u32; 16], ()> {
    std::thread::Builder::new()
        .name("fsv unified verifier".to_string())
        .stack_size(1 << 27)
        .spawn(move || {
            set_iterator(responses.into_iter());
            let mut src = ThreadLocalBasedSource;
            // verifier reads only from the thread-local NDS set above
            verify_unified_circuit_base_layer::<
                ThreadLocalBasedSource,
                DebugErrorCreator,
                REDUCED_ROUNDS,
            >(&mut src)
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
    let responses = build_stream(&proof, &setup_cap);
    let result = run_unified_base_layer(responses);
    assert!(result.is_ok(), "valid unified base-layer proof must verify");
}

#[test]
#[ignore = "requires generated unified base-layer fixture (run the prover step)"]
fn unified_base_layer_rejects_corrupted_stream() {
    let (proof, setup_cap) = assemble(load_bundle());
    let responses = build_stream(&proof, &setup_cap);

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
    let mut corrupted = build_stream(&proof, &setup_cap);
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
    let mut corrupted = build_stream(&proof, &setup_cap);
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
    let result = run_unified_base_layer(build_stream(&proof, &setup_cap));
    assert!(result.is_err(), "num_it_circuits = 0 must be rejected");
}

#[test]
#[ignore = "requires generated unified base-layer fixture (run the prover step)"]
fn rejects_num_it_circuits_exceeds_num_circuits() {
    let (proof, setup_cap) = assemble_with(load_bundle(), 1, 2);
    let result = run_unified_base_layer(build_stream(&proof, &setup_cap));
    assert!(
        result.is_err(),
        "num_it_circuits > num_circuits must be rejected"
    );
}

#[test]
#[ignore = "requires generated unified base-layer fixture (run the prover step)"]
fn rejects_multi_instance() {
    let (proof, setup_cap) = assemble_with(load_bundle(), 2, 2);
    let result = run_unified_base_layer(build_stream(&proof, &setup_cap));
    assert!(
        result.is_err(),
    );
}

fn fsv_binary_section_path(ext: &str) -> String {
    format!(
        "{}/../tools/gkr_verifier/fsv_unified_base_layer_sec_80.{}",
        env!("CARGO_MANIFEST_DIR"),
        ext
    )
}

fn load_binary_section(path: &str) -> Vec<u32> {
    let bytes = std::fs::read(path).unwrap_or_else(|_| {
        panic!("Missing {path} — run `cd tools/gkr_verifier && ./dump_bin.sh` (or gkr_test.sh `binaries`)")
    });
    assert!(bytes.len() % 4 == 0, "binary section not word-aligned");
    bytes
        .chunks_exact(4)
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
    let oracle_responses = build_stream(&proof, &setup_cap);

    let binary = load_binary_section(&fsv_binary_section_path("bin"));
    let text_section = load_binary_section(&fsv_binary_section_path("text"));

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

    let a0 = state.registers[10].value;
    assert_eq!(a0, 1, "FSV transpiler: a0 = {a0} (expected 1 for success)");

    let exact_cycles =
        (state.timestamp - common_constants::INITIAL_TIMESTAMP) / common_constants::TIMESTAMP_STEP;
    println!("FSV unified base layer: finished in {exact_cycles} transpiler cycles");
}
