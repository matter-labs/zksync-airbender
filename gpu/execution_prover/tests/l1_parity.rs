#![cfg(not(no_cuda))]

gpu_core::force_serial_libtest!();

use execution_prover::{CommitmentMode, ExecutionKind, MachineType, ProofProfile};
use full_statement_verifier::host_utils::{
    build_unified_stream, compute_end_params, load_fsv_program, FsvRecursionChain,
};
use full_statement_verifier::program_proof::ProgramProof;
use gpu_execution_prover::{ExecutionProver, ExecutionProverConfiguration};
use prover::definitions::SecurityLevel;
use prover::field::Proth120;
use prover::gkr::prover::GKRProof;
use prover::gkr::prover_config::example_configs::{
    EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS, EVM_PRODUCTION_PACK_LOG2,
};
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use riscv_transpiler::vm::FlatResponsesSource;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ReferenceBundle {
    proof: L1Proof,
    commitment_mode: CommitmentMode,
}

#[derive(Deserialize)]
struct FileIdentity {
    name: String,
    bytes: u64,
    keccak256: String,
}

#[derive(Deserialize)]
struct FsvIdentity {
    role: String,
    stem: String,
    bin_keccak256: String,
    text_keccak256: String,
}

#[derive(Deserialize)]
struct ReferenceConfiguration {
    security_level: String,
    backend: String,
    batch_id: u64,
}

#[derive(Deserialize)]
struct ProofManifest {
    format_version: u32,
    configuration: ReferenceConfiguration,
    fsv: Vec<FsvIdentity>,
    files: Vec<FileIdentity>,
}

#[derive(Deserialize)]
struct Checkpoint {
    schema_version: u32,
    target: String,
    security_level: String,
    proof: ProgramProof,
    setups: Setups,
    chain_end_params: Vec<[u32; 8]>,
    chain_hash: [u32; 8],
    chain_preimage: [u32; 16],
}

#[derive(Deserialize)]
enum CheckpointStep {
    Feeder { layer: u8 },
}

#[derive(Deserialize)]
struct StepCheckpoint {
    fixture_schema_version: u32,
    step: CheckpointStep,
    proof: ProgramProof,
    setups: Setups,
    chain_end_params: Vec<[u32; 8]>,
    input_is_base: bool,
}

struct FsvPrograms {
    feeder_first: (Vec<u32>, Vec<u32>),
    feeder: (Vec<u32>, Vec<u32>),
}

fn l1_reference_dir() -> PathBuf {
    std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../prover_pipeline/fixtures/l1_reference")
        })
}

fn read_typed<T: DeserializeOwned>(path: &Path) -> T {
    let file = File::open(path)
        .unwrap_or_else(|error| panic!("L1 reference open {}: {error}", path.display()));
    serde_json::from_reader(BufReader::new(file))
        .unwrap_or_else(|error| panic!("L1 reference deserialize {}: {error}", path.display()))
}

fn l1_bundle() -> ReferenceBundle {
    let bundle: ReferenceBundle = read_typed(&l1_reference_dir().join("l1_bundle.json"));
    assert!(
        matches!(
            bundle.commitment_mode,
            CommitmentMode::MergedAndPackedMemoryAndWitness {
                pack_log2: EVM_PRODUCTION_PACK_LOG2,
                external_challenges_pow_bits: EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
                ..
            }
        ),
        "L1 reference bundle is not in the EVM-production packed commitment mode"
    );
    bundle
}

fn bytes<T: Serialize + ?Sized>(value: &T) -> Vec<u8> {
    serde_json::to_vec(value).expect("L1 reference serializes")
}

fn differs<T: Serialize + ?Sized>(expected: &T, actual: &T) -> bool {
    bytes(expected) != bytes(actual)
}

fn first_index<T: Serialize>(expected: &[T], actual: &[T]) -> Option<usize> {
    (0..expected.len().max(actual.len()))
        .find(|&index| expected.get(index).map(bytes) != actual.get(index).map(bytes))
}

fn whir_round(steps: &[usize], poly_index: usize) -> usize {
    let mut end = 0;
    for (round, &step) in steps.iter().enumerate() {
        end += step;
        if poly_index < end {
            return round;
        }
    }
    steps.len()
}

fn bundle_differences(expected: &ReferenceBundle, actual: &ReferenceBundle) -> Vec<String> {
    let (e, a) = (&expected.proof, &actual.proof);
    let mut differences = Vec::new();
    if differs(&e.external_challenges, &a.external_challenges) {
        differences.push("external_challenges".into());
    }
    if differs(&e.final_explicit_evaluations, &a.final_explicit_evaluations) {
        differences.push("final_explicit_evaluations".into());
    }
    if differs(
        &e.sumcheck_intermediate_values,
        &a.sumcheck_intermediate_values,
    ) {
        let layers: BTreeSet<usize> = e
            .sumcheck_intermediate_values
            .keys()
            .chain(a.sumcheck_intermediate_values.keys())
            .copied()
            .collect();
        let layer = layers.into_iter().find(|layer| {
            e.sumcheck_intermediate_values.get(layer).map(bytes)
                != a.sumcheck_intermediate_values.get(layer).map(bytes)
        });
        differences.push(format!("sumcheck_intermediate_values[{layer:?}]"));
    }
    let (ew, aw) = (&e.whir_proof, &a.whir_proof);
    for (name, ec, ac) in [
        (
            "setup_commitment",
            &ew.setup_commitment,
            &aw.setup_commitment,
        ),
        (
            "memory_commitment",
            &ew.memory_commitment,
            &aw.memory_commitment,
        ),
        (
            "witness_commitment",
            &ew.witness_commitment,
            &aw.witness_commitment,
        ),
    ] {
        if differs(&ec.commitment.cap, &ac.commitment.cap) {
            differences.push(format!("whir_proof.{name}.commitment.cap"));
        }
        if ec.num_columns != ac.num_columns {
            differences.push(format!("whir_proof.{name}.num_columns"));
        }
        if let Some(index) = first_index(&ec.evals, &ac.evals) {
            differences.push(format!("whir_proof.{name}.evals[{index}]"));
        }
        if let Some(index) = first_index(&ec.queries, &ac.queries) {
            differences.push(format!("whir_proof.{name}.queries[{index}]"));
        }
    }
    if let Some(index) = first_index(&ew.intermediate_whir_oracles, &aw.intermediate_whir_oracles) {
        differences.push(format!("whir_proof.intermediate_whir_oracles[{index}]"));
    }
    if let Some(index) = first_index(&ew.ood_samples, &aw.ood_samples) {
        differences.push(format!("whir_proof.ood_samples[{index}]"));
    }
    if let Some(index) = first_index(&ew.sumcheck_polys, &aw.sumcheck_polys) {
        differences.push(format!(
            "whir_proof.sumcheck_polys[{index}] (WHIR round {})",
            whir_round(&ew.whir_schedule.whir_steps_schedule, index)
        ));
    }
    if let Some(index) = first_index(&ew.pow_nonces, &aw.pow_nonces) {
        differences.push(format!("whir_proof.pow_nonces[{index}]"));
    }
    if let Some(index) = first_index(&ew.final_monomials, &aw.final_monomials) {
        differences.push(format!("whir_proof.final_monomials[{index}]"));
    }
    if ew.whir_schedule != aw.whir_schedule {
        differences.push("whir_proof.whir_schedule".into());
    }
    if differs(&ew.batching_challenge, &aw.batching_challenge) {
        differences.push("whir_proof.batching_challenge".into());
    }
    if differs(&ew.original_evaluation_point, &aw.original_evaluation_point) {
        differences.push("whir_proof.original_evaluation_point".into());
    }
    if differs(&ew.batched_opening, &aw.batched_opening) {
        differences.push("whir_proof.batched_opening".into());
    }
    if differs(
        &e.grand_product_accumulator_computed,
        &a.grand_product_accumulator_computed,
    ) {
        differences.push("grand_product_accumulator_computed".into());
    }
    if e.inits_and_teardowns_top_bits != a.inits_and_teardowns_top_bits {
        differences.push("inits_and_teardowns_top_bits".into());
    }
    if e.lookup_challenges_pow_nonce != a.lookup_challenges_pow_nonce {
        differences.push("lookup_challenges_pow_nonce".into());
    }
    if e.batched_proximity_check_pow_nonce != a.batched_proximity_check_pow_nonce {
        differences.push("batched_proximity_check_pow_nonce".into());
    }
    if e.intermediate_transcript_seed != a.intermediate_transcript_seed {
        differences.push("intermediate_transcript_seed".into());
    }
    if expected.commitment_mode != actual.commitment_mode {
        differences.push("commitment_mode".into());
    }
    differences
}

fn assert_bundle_eq(expected: &ReferenceBundle, actual: &ReferenceBundle) {
    if bytes(expected) != bytes(actual) {
        panic!(
            "L1 bundle mismatch: {}",
            bundle_differences(expected, actual).join(", ")
        );
    }
}

fn keccak_hex(bytes: &[u8]) -> String {
    Keccak256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn proof_manifest(configuration: &ExecutionProverConfiguration) -> ProofManifest {
    let _ = env_logger::builder().is_test(true).try_init();
    let manifest: ProofManifest = read_typed(&l1_reference_dir().join("manifest.json"));
    assert_eq!(
        manifest.format_version, 1,
        "L1 parity proof manifest format"
    );
    assert_eq!(
        manifest.configuration.security_level, "Sec100",
        "L1 parity reference security level"
    );
    assert_eq!(
        configuration.security_level,
        SecurityLevel::Sec100,
        "L1 parity GPU security level differs from the reference"
    );
    assert_eq!(
        manifest.configuration.backend, "Cpu",
        "L1 parity reference backend"
    );
    assert_eq!(
        manifest.configuration.batch_id, 0,
        "L1 parity reference batch id"
    );
    manifest
}

fn check_file(manifest: &ProofManifest, name: &str) {
    let entry = manifest
        .files
        .iter()
        .find(|file| file.name == name)
        .unwrap_or_else(|| panic!("L1 parity manifest omits {name}"));
    let path = l1_reference_dir().join(name);
    let data = fs::read(&path)
        .unwrap_or_else(|error| panic!("L1 parity read {}: {error}", path.display()));
    assert_eq!(
        data.len() as u64,
        entry.bytes,
        "L1 parity reference size differs: {name}"
    );
    assert_eq!(
        keccak_hex(&data),
        entry.keccak256,
        "L1 parity reference identity differs: {name}"
    );
}

fn checkpoint(manifest: &ProofManifest, name: &str, target: &str) -> Checkpoint {
    check_file(manifest, name);
    let checkpoint: Checkpoint = read_typed(&l1_reference_dir().join(name));
    assert_eq!(
        checkpoint.schema_version, 4,
        "L1 parity checkpoint schema: {name}"
    );
    assert_eq!(
        checkpoint.target, target,
        "L1 parity checkpoint target: {name}"
    );
    assert_eq!(
        checkpoint.security_level, manifest.configuration.security_level,
        "L1 parity checkpoint security level: {name}"
    );
    let chain = rebuild_chain(&checkpoint.chain_end_params);
    assert_eq!(
        chain.hash(),
        checkpoint.chain_hash,
        "L1 parity checkpoint chain hash: {name}"
    );
    assert_eq!(
        chain.preimage(),
        checkpoint.chain_preimage,
        "L1 parity checkpoint chain preimage: {name}"
    );
    checkpoint
}

fn feeder_layer_0(manifest: &ProofManifest) -> StepCheckpoint {
    let name = "feeder_layer_0.json";
    check_file(manifest, name);
    let checkpoint: StepCheckpoint = read_typed(&l1_reference_dir().join(name));
    assert_eq!(
        checkpoint.fixture_schema_version, 1,
        "L1 parity feeder layer schema"
    );
    assert!(
        matches!(checkpoint.step, CheckpointStep::Feeder { layer: 0 }) && !checkpoint.input_is_base,
        "L1 parity feeder layer 0 checkpoint"
    );
    rebuild_chain(&checkpoint.chain_end_params);
    checkpoint
}

fn fsv_programs(manifest: &ProofManifest) -> FsvPrograms {
    let dir = std::env::var_os("FSV_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tools/gkr_verifier"));
    let load = |role: &str, program: FsvProgram| {
        let mode = BlakeMode::BlakeSpecialOpcodes;
        let stem = program.file_stem(mode);
        let entry = manifest
            .fsv
            .iter()
            .find(|entry| entry.role == role)
            .unwrap_or_else(|| panic!("L1 parity manifest omits fsv role {role}"));
        assert_eq!(stem, entry.stem, "L1 parity fsv stem differs: {role}");
        for (extension, expected) in [
            ("bin", &entry.bin_keccak256),
            ("text", &entry.text_keccak256),
        ] {
            let path = dir.join(format!("{stem}.{extension}"));
            let data = fs::read(&path)
                .unwrap_or_else(|error| panic!("L1 parity fsv read {}: {error}", path.display()));
            assert_eq!(
                keccak_hex(&data),
                *expected,
                "L1 parity fsv identity differs: {role}.{extension}"
            );
        }
        load_fsv_program(&dir, program, mode)
    };
    FsvPrograms {
        feeder_first: load("feeder_first", FsvProgram::UnifiedRecursionLayer),
        feeder: load("feeder", FsvProgram::UnifiedRecursionLayerL1Feeder),
    }
}

fn rebuild_chain(end_params: &[[u32; 8]]) -> FsvRecursionChain {
    let (first, rest) = end_params
        .split_first()
        .expect("L1 parity checkpoint has a recursion chain");
    let mut chain = FsvRecursionChain::begin(first);
    for end in rest {
        chain.extend(end);
    }
    chain
}

fn prove_feeder_layer(
    prover: &mut ExecutionProver,
    words: (Vec<u32>, Vec<u32>),
    chain: &mut FsvRecursionChain,
    proof: ProgramProof,
    setups: Setups,
    chain_end_params: &mut Vec<[u32; 8]>,
) -> (ProgramProof, Setups) {
    let handle = prover.add_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        words.0,
        words.1,
        None,
        &[ProofProfile::L1Feeder],
    );
    let result = prover.commit_memory_and_prove(
        0,
        &handle,
        FlatResponsesSource::new_with_reads(build_unified_stream(&setups, &proof)),
        CommitmentMode::MergedMemoryAndWitness,
        ProofProfile::L1Feeder,
    );
    let (mut stage_proof, stage_setups) = program_prover::assemble_program_proof(
        &prover.program_artifacts(&handle, ProofProfile::L1Feeder),
        result,
    );
    stage_proof.set_recursion_chain(chain);
    let end = compute_end_params(&stage_setups, stage_proof.final_pc);
    chain.extend(&end);
    chain_end_params.push(end);
    (stage_proof, stage_setups)
}

fn first_family_difference<T: Serialize>(
    name: &str,
    expected: &BTreeMap<u32, Vec<T>>,
    actual: &BTreeMap<u32, Vec<T>>,
) -> Option<String> {
    let families: BTreeSet<u32> = expected.keys().chain(actual.keys()).copied().collect();
    for family in families {
        match (expected.get(&family), actual.get(&family)) {
            (Some(e), Some(a)) => {
                if let Some(sequence) = first_index(e, a) {
                    return Some(format!("{name}: family {family} sequence {sequence}"));
                }
            }
            _ => return Some(format!("{name}: family {family} presence")),
        }
    }
    None
}

fn program_differences(expected: &ProgramProof, actual: &ProgramProof) -> Vec<String> {
    let mut differences = Vec::new();
    macro_rules! field {
        ($field:ident) => {
            if differs(&expected.$field, &actual.$field) {
                differences.push(stringify!($field).into());
            }
        };
    }
    if let Some(message) =
        first_family_difference("riscv_proofs", &expected.riscv_proofs, &actual.riscv_proofs)
    {
        differences.push(message);
    }
    field!(compiled_riscv_circuits);
    if let Some(sequence) = first_index(
        &expected.inits_and_teardown_proofs,
        &actual.inits_and_teardown_proofs,
    ) {
        differences.push(format!("inits_and_teardown_proofs: sequence {sequence}"));
    }
    field!(inits_and_teardowns_circuit);
    if let Some(message) = first_family_difference(
        "delegation_proofs",
        &expected.delegation_proofs,
        &actual.delegation_proofs,
    ) {
        differences.push(message);
    }
    field!(compiled_delegation_circuits);
    field!(register_final_values);
    field!(final_pc);
    field!(final_timestamp);
    field!(end_params);
    field!(recursion_chain_preimage);
    field!(recursion_chain_hash);
    field!(pow_challenge);
    field!(num_it_circuits);
    differences
}

fn assert_feeder_eq(
    expected_proof: &ProgramProof,
    expected_setups: &Setups,
    expected_end_params: &[[u32; 8]],
    actual_proof: &ProgramProof,
    actual_setups: &Setups,
    actual_end_params: &[[u32; 8]],
) {
    if bytes(&(expected_proof, expected_setups, expected_end_params))
        != bytes(&(actual_proof, actual_setups, actual_end_params))
    {
        let mut differences = program_differences(expected_proof, actual_proof);
        if differs(expected_setups, actual_setups) {
            differences.push("setups".into());
        }
        if differs(expected_end_params, actual_end_params) {
            differences.push("chain_end_params".into());
        }
        panic!("L1 feeder mismatch: {}", differences.join(", "));
    }
}

fn write_bundle(name: &str, bundle: &ReferenceBundle) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/l1_parity");
    fs::create_dir_all(&dir).expect("L1 parity bundle dump directory");
    let path = dir.join(name);
    let file = File::create(&path)
        .unwrap_or_else(|error| panic!("L1 parity bundle dump {}: {error}", path.display()));
    let mut writer = BufWriter::new(file);
    serde_json::to_writer(&mut writer, bundle).expect("L1 parity bundle dump serialization");
    writer.flush().expect("L1 parity bundle dump flush");
}

/// Negative control at M0: fails with `GPU backend does not support L1Wrap` from
/// `gpu/execution_prover/src/backend.rs:92-96`; M8 makes it pass by byte equality.
#[test]
#[ignore]
fn l1_wrap_cpu_gpu_proof_diff() {
    let configuration = ExecutionProverConfiguration::default();
    let manifest = proof_manifest(&configuration);
    let feeder = checkpoint(&manifest, "l1_feeder.json", "L1Feeder");
    check_file(&manifest, "l1_bundle.json");
    let bundle = l1_bundle();
    let programs = fsv_programs(&manifest);
    eprintln!("M0 negative control expects: GPU backend does not support L1Wrap");
    let mut prover = ExecutionProver::with_configuration(configuration);
    let handle = prover.add_binary(
        ExecutionKind::L1Wrap,
        MachineType::Reduced,
        programs.feeder.0,
        programs.feeder.1,
        None,
        &[ProofProfile::L1Wrap],
    );
    let nd = build_unified_stream(&feeder.setups, &feeder.proof);
    let result = prover.prove_l1_wrap(0, &handle, FlatResponsesSource::new_with_reads(nd));
    let actual = ReferenceBundle {
        proof: result.proof,
        commitment_mode: result.commitment_mode,
    };
    if bytes(&bundle) != bytes(&actual) {
        write_bundle("l1_wrap_cpu.json", &bundle);
        write_bundle("l1_wrap_gpu.json", &actual);
    }
    assert_eq!(
        actual.commitment_mode, bundle.commitment_mode,
        "L1 wrap commitment mode differs"
    );
    assert_bundle_eq(&bundle, &actual);
}

/// Negative control at M0: fails with `GPU backend supports only ProofProfile::Standard` from
/// `gpu/execution_prover/src/backend.rs:97-101`; M8 makes it pass by byte equality.
#[test]
#[ignore]
fn l1_feeder_first_cpu_gpu_proof_diff() {
    let configuration = ExecutionProverConfiguration::default();
    let manifest = proof_manifest(&configuration);
    let input = checkpoint(&manifest, "recursion_unified.json", "RecursionUnified");
    let expected = feeder_layer_0(&manifest);
    let programs = fsv_programs(&manifest);
    let mut end_params = input.chain_end_params;
    let mut chain = rebuild_chain(&end_params);
    eprintln!("M0 negative control expects: GPU backend supports only ProofProfile::Standard");
    let mut prover = ExecutionProver::with_configuration(configuration);
    let (proof, setups) = prove_feeder_layer(
        &mut prover,
        programs.feeder_first,
        &mut chain,
        input.proof,
        input.setups,
        &mut end_params,
    );
    assert_feeder_eq(
        &expected.proof,
        &expected.setups,
        &expected.chain_end_params,
        &proof,
        &setups,
        &end_params,
    );
}

/// Negative control at M0: fails with `GPU backend supports only ProofProfile::Standard` from
/// `gpu/execution_prover/src/backend.rs:97-101`; M8 makes it pass by byte equality.
#[test]
#[ignore]
fn l1_feeder_second_cpu_gpu_proof_diff() {
    let configuration = ExecutionProverConfiguration::default();
    let manifest = proof_manifest(&configuration);
    let input = feeder_layer_0(&manifest);
    let expected = checkpoint(&manifest, "l1_feeder.json", "L1Feeder");
    let programs = fsv_programs(&manifest);
    let mut end_params = input.chain_end_params;
    let mut chain = rebuild_chain(&end_params);
    eprintln!("M0 negative control expects: GPU backend supports only ProofProfile::Standard");
    let mut prover = ExecutionProver::with_configuration(configuration);
    let (proof, setups) = prove_feeder_layer(
        &mut prover,
        programs.feeder,
        &mut chain,
        input.proof,
        input.setups,
        &mut end_params,
    );
    assert_feeder_eq(
        &expected.proof,
        &expected.setups,
        &expected.chain_end_params,
        &proof,
        &setups,
        &end_params,
    );
    assert_eq!(
        chain.hash(),
        expected.chain_hash,
        "L1 feeder chain hash differs"
    );
    assert_eq!(
        chain.preimage(),
        expected.chain_preimage,
        "L1 feeder chain preimage differs"
    );
}

/// Negative control at M0: fails with `GPU backend supports only ProofProfile::Standard` from
/// `gpu/execution_prover/src/backend.rs:97-101`; M8 makes it pass by byte equality.
#[test]
#[ignore]
fn l1_feeder_cpu_gpu_proof_diff() {
    let configuration = ExecutionProverConfiguration::default();
    let manifest = proof_manifest(&configuration);
    let input = checkpoint(&manifest, "recursion_unified.json", "RecursionUnified");
    let expected_first = feeder_layer_0(&manifest);
    let expected_second = checkpoint(&manifest, "l1_feeder.json", "L1Feeder");
    let programs = fsv_programs(&manifest);
    let mut end_params = input.chain_end_params;
    let mut chain = rebuild_chain(&end_params);
    eprintln!("M0 negative control expects: GPU backend supports only ProofProfile::Standard");
    let mut prover = ExecutionProver::with_configuration(configuration);
    let (first_proof, first_setups) = prove_feeder_layer(
        &mut prover,
        programs.feeder_first,
        &mut chain,
        input.proof,
        input.setups,
        &mut end_params,
    );
    assert_feeder_eq(
        &expected_first.proof,
        &expected_first.setups,
        &expected_first.chain_end_params,
        &first_proof,
        &first_setups,
        &end_params,
    );
    let (proof, setups) = prove_feeder_layer(
        &mut prover,
        programs.feeder,
        &mut chain,
        first_proof,
        first_setups,
        &mut end_params,
    );
    assert_feeder_eq(
        &expected_second.proof,
        &expected_second.setups,
        &expected_second.chain_end_params,
        &proof,
        &setups,
        &end_params,
    );
    assert_eq!(
        chain.hash(),
        expected_second.chain_hash,
        "L1 feeder chain hash differs"
    );
    assert_eq!(
        chain.preimage(),
        expected_second.chain_preimage,
        "L1 feeder chain preimage differs"
    );
}
