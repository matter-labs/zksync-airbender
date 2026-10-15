#![cfg(not(no_cuda))]

gpu_core::force_serial_libtest!();

use execution_prover::{CommitmentMode, ExecutionKind, MachineType, ProofProfile};
use execution_prover_model::circuit_type::UnrolledCircuitType;
use full_statement_verifier::host_utils::{
    build_unified_stream, compute_end_params, load_fsv_program, native_verify_unified_l1_feeder,
    FsvRecursionChain,
};
use full_statement_verifier::program_proof::ProgramProof;
use gpu_execution_prover::{ExecutionProver, ExecutionProverConfiguration, MemoryPreset};
use prover::definitions::SecurityLevel;
use prover::field::Proth120;
use prover::gkr::prover::GKRProof;
use prover::gkr::prover_config::example_configs::l1_wrap_2p21::{
    EXTERNAL_CHALLENGES_POW_BITS, PACK_LOG2,
};
use prover::gkr::prover_config::example_configs::L1_FEEDER_QUERIES_AND_POW;
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

struct FsvPrograms {
    wrap: (Vec<u32>, Vec<u32>),
}

fn l1_reference_dir() -> PathBuf {
    std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../prover_pipeline/fixtures/l1_reference_2p21")
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
                pack_log2: PACK_LOG2,
                external_challenges_pow_bits: EXTERNAL_CHALLENGES_POW_BITS,
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
        checkpoint.schema_version, 5,
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
        wrap: load("feeder_wrap", FsvProgram::UnifiedRecursionLayerL1FeederWrap),
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

#[test]
#[ignore]
fn l1_wrap_cpu_gpu_proof_diff() {
    let mut configuration = ExecutionProverConfiguration::default();
    configuration.backend.memory_preset = MemoryPreset::GiB30;
    let manifest = proof_manifest(&configuration);
    let feeder = checkpoint(&manifest, "l1_feeder.json", "L1Feeder");
    check_file(&manifest, "l1_bundle.json");
    let bundle = l1_bundle();
    let programs = fsv_programs(&manifest);
    let mut prover = ExecutionProver::with_configuration(configuration);
    let handle = prover.add_binary(
        ExecutionKind::L1Wrap21,
        MachineType::Reduced,
        programs.wrap.0,
        programs.wrap.1,
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

/// Profiling variant: one warmup commit + proof, then the measured
/// commit + proof in the same process with the same setup and inputs, each inside a
/// host NVTX range `l1_wrap.iteration.{warmup,measured}`; both must equal the reference.
#[test]
#[ignore]
fn l1_wrap_cpu_gpu_proof_diff_warm() {
    let mut configuration = ExecutionProverConfiguration::default();
    configuration.backend.memory_preset = MemoryPreset::GiB30;
    let manifest = proof_manifest(&configuration);
    let feeder = checkpoint(&manifest, "l1_feeder.json", "L1Feeder");
    check_file(&manifest, "l1_bundle.json");
    let bundle = l1_bundle();
    let programs = fsv_programs(&manifest);
    let mut prover = ExecutionProver::with_configuration(configuration);
    let handle = prover.add_binary(
        ExecutionKind::L1Wrap21,
        MachineType::Reduced,
        programs.wrap.0,
        programs.wrap.1,
        None,
        &[ProofProfile::L1Wrap],
    );
    for iteration in ["warmup", "measured"] {
        let label = format!("l1_wrap.iteration.{iteration}");
        let started = std::time::Instant::now();
        let actual = {
            let _range = gpu_core::primitives::nvtx::scoped_range(None, &label);
            let nd = build_unified_stream(&feeder.setups, &feeder.proof);
            let result = prover.prove_l1_wrap(0, &handle, FlatResponsesSource::new_with_reads(nd));
            ReferenceBundle {
                proof: result.proof,
                commitment_mode: result.commitment_mode,
            }
        };
        eprintln!(
            "{label}: {:.3} ms wall (prove_l1_wrap incl. setup init on warmup)",
            started.elapsed().as_secs_f64() * 1e3
        );
        assert_eq!(
            actual.commitment_mode, bundle.commitment_mode,
            "L1 wrap commitment mode differs ({iteration})"
        );
        assert_bundle_eq(&bundle, &actual);
    }
}

/// The fields of `prover_pipeline`'s 2^22 feeder reference manifest these tests read.
#[derive(Deserialize)]
struct FeederManifest {
    fixture_schema_version: u32,
    input: String,
    fsv: Vec<FsvIdentity>,
    feeder_queries_and_pow: Vec<(usize, u32)>,
    files: Vec<(String, u64, String)>,
}

/// The fields of the reference seed (`recursion_unified.json`, a `ProofArtifact`) these tests read.
#[derive(Deserialize)]
struct FeederSeed {
    schema_version: u32,
    target: String,
    security_level: String,
    batch_id: u64,
    proof: ProgramProof,
    setups: Setups,
    chain_end_params: Vec<[u32; 8]>,
    chain_hash: [u32; 8],
}

/// The fields of a reference `layer_{n}.json` (`LayerFixture`) these tests read.
#[derive(Deserialize)]
struct FeederLayer {
    fixture_schema_version: u32,
    layer: u8,
    instances: usize,
    native_output: [u32; 16],
    chain_hash: [u32; 8],
    proof: ProgramProof,
    setups: Setups,
    chain_end_params: Vec<[u32; 8]>,
}

struct FeederReference {
    dir: PathBuf,
    manifest: FeederManifest,
    fsv_dir: PathBuf,
}

impl FeederReference {
    fn load() -> Self {
        let _ = env_logger::builder().is_test(true).try_init();
        let root = std::env::var_os("AB_F3_REFERENCE_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| {
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../../prover_pipeline/fixtures/l1_feeder_reference")
            });
        let input = std::env::var("AB_F3_INPUT").unwrap_or_else(|_| "basic_fibonacci".into());
        let dir = root.join(&input);
        let manifest_path = dir.join("manifest.json");
        assert!(
            manifest_path.exists(),
            "L1 feeder parity reference {} is not generated (it is not committed); generate it: RUST_MIN_STACK=1073741824 cargo test -p prover_pipeline --release --lib l1_feeder_reference::generate_feeder_reference -- --exact --ignored --nocapture --test-threads=1",
            dir.display()
        );
        let manifest: FeederManifest = read_typed(&manifest_path);
        assert_eq!(
            manifest.fixture_schema_version, 1,
            "L1 feeder parity reference schema"
        );
        assert_eq!(manifest.input, input, "L1 feeder parity reference input");
        assert_eq!(
            manifest.feeder_queries_and_pow,
            L1_FEEDER_QUERIES_AND_POW.to_vec(),
            "L1 feeder parity reference was produced under another feeder config"
        );
        let fsv_dir = std::env::var_os("FSV_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| {
                Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tools/gkr_verifier")
            });
        Self {
            dir,
            manifest,
            fsv_dir,
        }
    }

    fn read<T: DeserializeOwned>(&self, name: &str) -> T {
        let (_, bytes, keccak256) = self
            .manifest
            .files
            .iter()
            .find(|(file, _, _)| file == name)
            .unwrap_or_else(|| panic!("L1 feeder parity manifest omits {name}"));
        let path = self.dir.join(name);
        let data = fs::read(&path)
            .unwrap_or_else(|error| panic!("L1 feeder parity read {}: {error}", path.display()));
        assert_eq!(
            data.len() as u64,
            *bytes,
            "L1 feeder parity reference size differs: {name}"
        );
        assert_eq!(
            keccak_hex(&data),
            *keccak256,
            "L1 feeder parity reference identity differs: {name}"
        );
        serde_json::from_slice(&data)
            .unwrap_or_else(|error| panic!("L1 feeder parity deserialize {name}: {error}"))
    }

    fn seed(&self) -> FeederSeed {
        let seed: FeederSeed = self.read("recursion_unified.json");
        assert_eq!(seed.schema_version, 5, "L1 feeder parity seed schema");
        assert_eq!(
            seed.target, "RecursionUnified",
            "L1 feeder parity seed target"
        );
        assert_eq!(
            seed.security_level, "Sec100",
            "L1 feeder parity seed security"
        );
        assert_eq!(seed.batch_id, 0, "L1 feeder parity seed batch id");
        assert_eq!(
            rebuild_chain(&seed.chain_end_params).hash(),
            seed.chain_hash,
            "L1 feeder parity seed chain hash"
        );
        seed
    }

    fn layer(&self, layer: u8) -> FeederLayer {
        let fixture: FeederLayer = self.read(&format!("layer_{layer}.json"));
        assert_eq!(
            fixture.fixture_schema_version, 1,
            "L1 feeder parity layer schema"
        );
        assert_eq!(fixture.layer, layer, "L1 feeder parity layer index");
        assert_eq!(
            rebuild_chain(&fixture.chain_end_params).hash(),
            fixture.chain_hash,
            "L1 feeder parity layer {layer} chain hash"
        );
        fixture
    }

    fn program(&self, role: &str, program: FsvProgram) -> (Vec<u32>, Vec<u32>) {
        let mode = BlakeMode::BlakeSpecialOpcodes;
        let stem = program.file_stem(mode);
        let entry = self
            .manifest
            .fsv
            .iter()
            .find(|entry| entry.role == role)
            .unwrap_or_else(|| panic!("L1 feeder parity manifest omits fsv role {role}"));
        assert_eq!(
            stem, entry.stem,
            "L1 feeder parity fsv stem differs: {role}"
        );
        for (extension, expected) in [
            ("bin", &entry.bin_keccak256),
            ("text", &entry.text_keccak256),
        ] {
            let path = self.fsv_dir.join(format!("{stem}.{extension}"));
            let data = fs::read(&path).unwrap_or_else(|error| {
                panic!("L1 feeder parity fsv read {}: {error}", path.display())
            });
            assert_eq!(
                keccak_hex(&data),
                *expected,
                "L1 feeder parity fsv identity differs: {role}.{extension}"
            );
        }
        load_fsv_program(&self.fsv_dir, program, mode)
    }
}

/// One GPU feeder layer as `prover_pipeline` proves it: `Unified22` with
/// `[L1Feeder]` in the merged commitment mode, batch 0, at the 30 GiB preset.
fn prove_feeder_layer(
    words: (Vec<u32>, Vec<u32>),
    proof: &ProgramProof,
    setups: &Setups,
    chain_end_params: &[[u32; 8]],
) -> (ProgramProof, Setups, Vec<[u32; 8]>) {
    let mut configuration = ExecutionProverConfiguration::default();
    configuration.backend.memory_preset = MemoryPreset::GiB30;
    assert_eq!(configuration.security_level, SecurityLevel::Sec100);
    let mut prover = ExecutionProver::with_configuration(configuration);
    let handle = prover.add_binary(
        ExecutionKind::Unified22,
        MachineType::Reduced,
        words.0,
        words.1,
        None,
        &[ProofProfile::L1Feeder],
    );
    let result = prover.commit_memory_and_prove(
        0,
        &handle,
        FlatResponsesSource::new_with_reads(build_unified_stream(setups, proof)),
        CommitmentMode::MergedMemoryAndWitness,
        ProofProfile::L1Feeder,
    );
    let (mut layer_proof, layer_setups) = program_prover::assemble_program_proof(
        &prover.program_artifacts(&handle, ProofProfile::L1Feeder),
        result,
    );
    let mut chain = rebuild_chain(chain_end_params);
    layer_proof.set_recursion_chain(&chain);
    let end = compute_end_params(&layer_setups, layer_proof.final_pc);
    chain.extend(&end);
    let mut end_params = chain_end_params.to_vec();
    end_params.push(end);
    (layer_proof, layer_setups, end_params)
}

fn assert_feeder_layer_eq(
    expected: &FeederLayer,
    proof: &ProgramProof,
    setups: &Setups,
    end_params: &[[u32; 8]],
) {
    assert_feeder_eq(
        &expected.proof,
        &expected.setups,
        &expected.chain_end_params,
        proof,
        setups,
        end_params,
    );
    let family = UnrolledCircuitType::Unified22.get_family_idx() as u32;
    assert_eq!(
        proof.riscv_proofs.keys().copied().collect::<Vec<_>>(),
        [family],
        "L1 feeder layer {} proof families",
        expected.layer
    );
    assert_eq!(
        proof.riscv_proofs[&family].len(),
        expected.instances,
        "L1 feeder layer {} instances",
        expected.layer
    );
    assert_eq!(
        rebuild_chain(end_params).hash(),
        expected.chain_hash,
        "L1 feeder layer {} chain hash",
        expected.layer
    );
    let native_output = native_verify_unified_l1_feeder(build_unified_stream(setups, proof))
        .unwrap_or_else(|error| panic!("L1 feeder layer {}: {error}", expected.layer));
    assert_eq!(
        native_output, expected.native_output,
        "L1 feeder layer {} native output",
        expected.layer
    );
}

#[test]
#[ignore]
fn l1_feeder_f1_cpu_gpu_proof_diff() {
    let reference = FeederReference::load();
    let seed = reference.seed();
    let expected = reference.layer(0);
    let program = reference.program("feeder_first", FsvProgram::UnifiedRecursionLayer);
    let (proof, setups, end_params) =
        prove_feeder_layer(program, &seed.proof, &seed.setups, &seed.chain_end_params);
    assert_feeder_layer_eq(&expected, &proof, &setups, &end_params);
}

#[test]
#[ignore]
fn l1_feeder_f2_cpu_gpu_proof_diff() {
    let reference = FeederReference::load();
    let input = reference.layer(0);
    let expected = reference.layer(1);
    let program = reference.program("feeder", FsvProgram::UnifiedRecursionLayerL1Feeder);
    let (proof, setups, end_params) = prove_feeder_layer(
        program,
        &input.proof,
        &input.setups,
        &input.chain_end_params,
    );
    assert_feeder_layer_eq(&expected, &proof, &setups, &end_params);
}

#[test]
#[ignore]
fn l1_feeder_f3_cpu_gpu_proof_diff() {
    let reference = FeederReference::load();
    let input = reference.layer(1);
    let expected = reference.layer(2);
    let program = reference.program("feeder", FsvProgram::UnifiedRecursionLayerL1Feeder);
    let (proof, setups, end_params) = prove_feeder_layer(
        program,
        &input.proof,
        &input.setups,
        &input.chain_end_params,
    );
    assert_feeder_layer_eq(&expected, &proof, &setups, &end_params);
}
