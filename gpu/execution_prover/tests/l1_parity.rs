#![cfg(not(no_cuda))]

gpu_core::force_serial_libtest!();

use execution_prover::{ExecutionKind, MachineType, OperationMode, ProofProfile};
use execution_prover_model::circuit_type::UnrolledCircuitType;
use full_statement_verifier::host_utils::{
    build_unified_stream, compute_end_params, load_fsv_exact, native_verify_unified_l1_feeder,
    native_verify_unified_l1_feeder_a, FsvRecursionChain,
};
use full_statement_verifier::program_proof::ProgramProof;
use gpu_execution_prover::{ExecutionProver, ExecutionProverConfiguration, MemoryPreset};
use prover::definitions::SecurityLevel;
use prover::field::Proth120;
use prover::gkr::prover::GKRProof;
use prover::gkr::prover_config::example_configs::l1_wrap_2p21::EXTERNAL_CHALLENGES_POW_BITS;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use riscv_transpiler::vm::FlatResponsesSource;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::fs::{self, File};
use std::io::{BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProfile, FsvProgram};

type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ReferenceBundle {
    proof: L1Proof,
    operation_mode: OperationMode,
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
    fsv_rom_digest_v1: String,
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
            bundle.operation_mode,
            OperationMode::SingleChunk {
                external_challenges_pow_bits: EXTERNAL_CHALLENGES_POW_BITS,
                ..
            }
        ),
        "L1 reference bundle is not in the EVM-production single-chunk operation"
    );
    bundle
}

fn bytes<T: Serialize + ?Sized>(value: &T) -> Vec<u8> {
    serde_json::to_vec(value).expect("L1 reference serializes")
}

fn assert_bundle_eq(expected: &ReferenceBundle, actual: &ReferenceBundle) {
    if bytes(expected) != bytes(actual) {
        write_bundle("l1_wrap_cpu.json", expected);
        write_bundle("l1_wrap_gpu.json", actual);
        panic!("L1 bundle bytes differ; see target/l1_parity/l1_wrap_{{cpu,gpu}}.json");
    }
}

fn write_bundle<T: Serialize>(name: &str, bundle: &T) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/l1_parity");
    fs::create_dir_all(&dir).expect("L1 parity bundle dump directory");
    let path = dir.join(name);
    let file = File::create(&path)
        .unwrap_or_else(|error| panic!("L1 parity bundle dump {}: {error}", path.display()));
    let mut writer = BufWriter::new(file);
    serde_json::to_writer(&mut writer, bundle).expect("L1 parity bundle dump serialization");
    writer.flush().expect("L1 parity bundle dump flush");
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
        checkpoint.schema_version, 6,
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

#[test]
fn cpu_l1_reference_checkpoints_are_current() {
    let manifest = proof_manifest(&ExecutionProverConfiguration::default());
    checkpoint(&manifest, "recursion_unified.json", "RecursionUnified");
    checkpoint(&manifest, "l1_feeder.json", "L1Feeder");
    l1_bundle();
}

/// The guest's registry path without `.elf`: the stem the L1 reference manifest records.
fn registry_stem(descriptor: &FsvDescriptor) -> &'static str {
    descriptor
        .registry_entry()
        .unwrap_or_else(|error| panic!("{error}"))
        .relative_path
        .trim_end_matches(".elf")
}

fn fsv_programs(manifest: &ProofManifest) -> FsvPrograms {
    let dir = std::env::var_os("FSV_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../tools/gkr_verifier/full_statement_verifiers")
        });
    let load = |role: &str, descriptor: FsvDescriptor| {
        let stem = registry_stem(&descriptor);
        let entry = manifest
            .fsv
            .iter()
            .find(|entry| entry.role == role)
            .unwrap_or_else(|| panic!("L1 parity manifest omits fsv role {role}"));
        assert_eq!(stem, entry.stem, "L1 parity fsv stem differs: {role}");
        let guest = load_fsv_exact(&dir, &descriptor).unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(
            guest.digest().to_string(),
            entry.fsv_rom_digest_v1,
            "L1 parity fsv-rom-digest-v1 differs from the registry: {role}"
        );
        guest.into_words()
    };
    FsvPrograms {
        wrap: load(
            "feeder_wrap",
            FsvDescriptor::l1_feeder(FsvProfile::L1FeederWrap),
        ),
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

fn assert_feeder_eq(
    expected_proof: &ProgramProof,
    expected_setups: &Setups,
    expected_end_params: &[[u32; 8]],
    actual_proof: &ProgramProof,
    actual_setups: &Setups,
    actual_end_params: &[[u32; 8]],
) {
    let expected = (expected_proof, expected_setups, expected_end_params);
    let actual = (actual_proof, actual_setups, actual_end_params);
    if bytes(&expected) != bytes(&actual) {
        write_bundle("l1_feeder_cpu.json", &expected);
        write_bundle("l1_feeder_gpu.json", &actual);
        panic!("L1 feeder bytes differ; see target/l1_parity/l1_feeder_{{cpu,gpu}}.json");
    }
}

fn wrap_matches_cpu_reference(preset: MemoryPreset) {
    let mut configuration = ExecutionProverConfiguration::default();
    configuration.backend.memory_preset = preset;
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
    let nd = build_unified_stream(
        &feeder.setups,
        &feeder.proof,
        verifier_common::fsv_binaries::BlakeMode::BlakeSpecialOpcodes,
    );
    let result = prover.prove_l1_wrap(0, &handle, FlatResponsesSource::new_with_reads(nd));
    let actual = ReferenceBundle {
        proof: result.proof,
        operation_mode: result.operation_mode,
    };
    assert_bundle_eq(&bundle, &actual);
}

#[test]
#[ignore]
fn l1_wrap_cpu_gpu_proof_diff() {
    wrap_matches_cpu_reference(MemoryPreset::GiB30);
}

#[test]
#[ignore]
fn l1_wrap_cpu_gpu_proof_diff_21gib() {
    wrap_matches_cpu_reference(MemoryPreset::GiB21);
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

/// A canonical CPU checkpoint, with the native output derived from its proof.
#[derive(Deserialize)]
struct FeederLayer {
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
    manifest: ProofManifest,
    fsv_dir: PathBuf,
}

impl FeederReference {
    fn load() -> Self {
        let _ = env_logger::builder().is_test(true).try_init();
        let dir = l1_reference_dir();
        let manifest = proof_manifest(&ExecutionProverConfiguration::default());
        let fsv_dir = std::env::var_os("FSV_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| {
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../../tools/gkr_verifier/full_statement_verifiers")
            });
        Self {
            dir,
            manifest,
            fsv_dir,
        }
    }

    fn read<T: DeserializeOwned>(&self, name: &str) -> T {
        let entry = self
            .manifest
            .files
            .iter()
            .find(|entry| entry.name == name)
            .unwrap_or_else(|| panic!("CPU reference manifest omits {name}"));
        let data = fs::read(self.dir.join(name)).expect("CPU feeder reference");
        assert_eq!(data.len() as u64, entry.bytes);
        assert_eq!(keccak_hex(&data), entry.keccak256);
        serde_json::from_slice(&data)
            .unwrap_or_else(|error| panic!("L1 feeder parity deserialize {name}: {error}"))
    }

    fn seed(&self) -> FeederSeed {
        let seed: FeederSeed = self.read("recursion_unified.json");
        assert_eq!(seed.schema_version, 6, "L1 feeder parity seed schema");
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
        let (proof, setups, chain_end_params) = if layer < 2 {
            #[derive(Deserialize)]
            struct Nonterminal {
                fixture_schema_version: u32,
                feeder_layers: u32,
                proof: ProgramProof,
                setups: Setups,
                chain_end_params: Vec<[u32; 8]>,
            }
            let checkpoint: Nonterminal = self.read(&format!("feeder_layer_{layer}.json"));
            assert_eq!(checkpoint.fixture_schema_version, 2);
            assert_eq!(checkpoint.feeder_layers, u32::from(layer) + 1);
            (
                checkpoint.proof,
                checkpoint.setups,
                checkpoint.chain_end_params,
            )
        } else {
            assert_eq!(layer, 2);
            let terminal: FeederSeed = self.read("l1_feeder.json");
            assert_eq!(terminal.target, "L1Feeder");
            (terminal.proof, terminal.setups, terminal.chain_end_params)
        };
        let family = UnrolledCircuitType::Unified.get_family_idx() as u32;
        let instances = proof.riscv_proofs[&family].len();
        let chain_hash = rebuild_chain(&chain_end_params).hash();
        let stream = build_unified_stream(
            &setups,
            &proof,
            verifier_common::fsv_binaries::BlakeMode::BlakeSpecialOpcodes,
        );
        let native_output = match feeder_profile(&proof).1 {
            ProofProfile::L1FeederA => native_verify_unified_l1_feeder_a(stream),
            ProofProfile::L1Feeder => native_verify_unified_l1_feeder(stream),
            _ => unreachable!(),
        }
        .expect("CPU feeder reference verifies");
        FeederLayer {
            layer,
            instances,
            native_output,
            chain_hash,
            proof,
            setups,
            chain_end_params,
        }
    }

    fn program(&self, role: &str, descriptor: FsvDescriptor) -> (Vec<u32>, Vec<u32>) {
        let stem = registry_stem(&descriptor);
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
        let guest =
            load_fsv_exact(&self.fsv_dir, &descriptor).unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(
            guest.digest().to_string(),
            entry.fsv_rom_digest_v1,
            "L1 feeder parity fsv-rom-digest-v1 differs from the registry: {role}"
        );
        guest.into_words()
    }
}

fn feeder_profile(proof: &ProgramProof) -> (ExecutionKind, ProofProfile) {
    let family = UnrolledCircuitType::Unified.get_family_idx() as u32;
    match proof.compiled_riscv_circuits[&family].trace_len {
        n if n == UnrolledCircuitType::Unified.get_domain_size() => {
            (ExecutionKind::Unified, ProofProfile::L1FeederA)
        }
        n if n == UnrolledCircuitType::Unified22.get_domain_size() => {
            (ExecutionKind::Unified22, ProofProfile::L1Feeder)
        }
        n => panic!("unsupported feeder trace length {n}"),
    }
}

/// One GPU feeder layer at the expected proof's production profile, in the
/// merged commitment mode, batch 0, at the 30 GiB preset.
fn prove_feeder_layer(
    words: (Vec<u32>, Vec<u32>),
    proof: &ProgramProof,
    setups: &Setups,
    chain_end_params: &[[u32; 8]],
    expected: &ProgramProof,
) -> (ProgramProof, Setups, Vec<[u32; 8]>) {
    let (kind, profile) = feeder_profile(expected);
    let mut configuration = ExecutionProverConfiguration::default();
    configuration.backend.memory_preset = MemoryPreset::GiB30;
    assert_eq!(configuration.security_level, SecurityLevel::Sec100);
    let mut prover = ExecutionProver::with_configuration(configuration);
    let handle = prover.add_binary(
        kind,
        MachineType::Reduced,
        words.0,
        words.1,
        None,
        &[profile],
    );
    let result = prover.commit_memory_and_prove(
        0,
        &handle,
        FlatResponsesSource::new_with_reads(build_unified_stream(
            setups,
            proof,
            verifier_common::fsv_binaries::BlakeMode::BlakeSpecialOpcodes,
        )),
        profile,
    );
    let (mut layer_proof, layer_setups) =
        program_prover::assemble_program_proof(&prover.program_artifacts(&handle, profile), result);
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
    let stream = build_unified_stream(
        setups,
        proof,
        verifier_common::fsv_binaries::BlakeMode::BlakeSpecialOpcodes,
    );
    let native_output = match feeder_profile(proof).1 {
        ProofProfile::L1FeederA => native_verify_unified_l1_feeder_a(stream),
        ProofProfile::L1Feeder => native_verify_unified_l1_feeder(stream),
        _ => unreachable!(),
    }
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
    let program = reference.program(
        "feeder_first",
        FsvDescriptor::new(
            verifier_common::fsv_binaries::SecurityLevel::Sec100,
            verifier_common::fsv_binaries::SoundnessMode::PessimisticConjecture,
            FsvProgram::UnifiedRecursionLayer,
            BlakeMode::BlakeSpecialOpcodes,
        ),
    );
    let (proof, setups, end_params) = prove_feeder_layer(
        program,
        &seed.proof,
        &seed.setups,
        &seed.chain_end_params,
        &expected.proof,
    );
    assert_feeder_layer_eq(&expected, &proof, &setups, &end_params);
}

#[test]
#[ignore]
fn l1_feeder_f2_cpu_gpu_proof_diff() {
    let reference = FeederReference::load();
    let input = reference.layer(0);
    let expected = reference.layer(1);
    let program = reference.program("feeder_a", FsvDescriptor::l1_feeder(FsvProfile::L1FeederA));
    let (proof, setups, end_params) = prove_feeder_layer(
        program,
        &input.proof,
        &input.setups,
        &input.chain_end_params,
        &expected.proof,
    );
    assert_feeder_layer_eq(&expected, &proof, &setups, &end_params);
}

#[test]
#[ignore]
fn l1_feeder_f3_cpu_gpu_proof_diff() {
    let reference = FeederReference::load();
    let input = reference.layer(1);
    let expected = reference.layer(2);
    let program = reference.program("feeder_a", FsvDescriptor::l1_feeder(FsvProfile::L1FeederA));
    let (proof, setups, end_params) = prove_feeder_layer(
        program,
        &input.proof,
        &input.setups,
        &input.chain_end_params,
        &expected.proof,
    );
    assert_feeder_layer_eq(&expected, &proof, &setups, &end_params);
}
