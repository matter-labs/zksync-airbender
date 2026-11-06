// Shared native fixture support; each example uses a subset of these helpers.
#![allow(dead_code)]

use full_statement_verifier::{host_utils, program_proof::ProgramProof};
use prover::definitions::{BlakeMode, SecurityLevel, SoundnessMode};
use std::{
    collections::BTreeMap,
    io::Write,
    path::{Path, PathBuf},
};
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::prover;
use verifier_common::{cs::gkr_compiler::GKRCircuitArtifact, errors::DebugErrorCreator};

pub const READS: [u32; 2] = [0, 1];
pub const FILES: [&str; 3] = [
    "proof.compact.json.zlib",
    "setups.compact.json.zlib",
    "manifest.json",
];
pub const PROGRAM: &str = "examples/hashed_fibonacci/app_blake2_with_compression";
const RISCV: [(u32, &str); 6] = [
    (1, "unrolled_circuits/add_sub_lui_auipc_mop"),
    (2, "unrolled_circuits/jump_branch_slt"),
    (3, "unrolled_circuits/shift_binary"),
    (4, "unrolled_circuits/mul_div_unsigned"),
    (16, "unrolled_circuits/load_store_word_only"),
    (17, "unrolled_circuits/load_store_subword_only"),
];

#[derive(Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub version: u32,
    pub program: String,
    pub program_digest: String,
    pub reads: [u32; 2],
    pub security_level: String,
    pub soundness_mode: String,
    pub expected_output: [u32; 16],
    pub riscv_proofs: BTreeMap<u32, usize>,
    pub inits_and_teardowns_proofs: usize,
    pub delegation_proofs: BTreeMap<u32, usize>,
}

pub fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_owned()
}

pub fn fixture_dir() -> PathBuf {
    root().join("full_statement_verifier/tests/fixtures/hashed_fibonacci")
}

pub fn program() -> (Vec<u32>, Vec<u32>) {
    riscv_transpiler::elf::load_legacy_binaries(
        &root().join(format!("{PROGRAM}.bin")),
        &root().join(format!("{PROGRAM}.text")),
    )
}

fn canonicalize(layout: &mut GKRCircuitArtifact<BabyBearField>) {
    let prefix = format!("{}/", root().display());
    // file!() is absolute when a dependency is built outside its workspace.
    // Source-location labels do not change the circuit or its setup columns.
    for label in layout.variable_names.values_mut() {
        *label = label.replace(&prefix, "");
    }
}

fn check_layout(name: &str, layout: &GKRCircuitArtifact<BabyBearField>) {
    let path = root()
        .join("circuit_defs")
        .join(name)
        .join("generated/layout.json");
    let mut current: GKRCircuitArtifact<BabyBearField> =
        serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    canonicalize(&mut current);
    assert!(
        layout == &current,
        "{name}: fixture layout differs from production; regenerate fixture"
    );
}

fn check_schedule(name: &str, schedule: &impl serde::Serialize) {
    let path = root()
        .join("circuit_defs")
        .join(name)
        .join("generated/prover_config_sec_100_pessimistic_conjecture.json");
    let config: serde_json::Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    assert!(
        serde_json::to_value(schedule).unwrap() == config["whir_schedule"],
        "{name}: fixture WHIR schedule differs from committed config; regenerate fixture"
    );
}

fn counts(proof: &ProgramProof) -> (BTreeMap<u32, usize>, BTreeMap<u32, usize>) {
    (
        proof
            .riscv_proofs
            .iter()
            .map(|(&id, p)| (id, p.len()))
            .collect(),
        proof
            .delegation_proofs
            .iter()
            .map(|(&id, p)| (id, p.len()))
            .collect(),
    )
}

pub fn validate(proof: &ProgramProof, setups: &setups::Setups) {
    assert_eq!(
        setups.keys().copied().collect::<Vec<_>>(),
        [1, 2, 3, 4, 16, 17]
    );
    let (riscv, delegation) = counts(proof);
    assert_eq!(riscv, BTreeMap::from([(1, 1), (2, 1), (3, 1), (16, 1)]));
    assert_eq!(delegation, BTreeMap::from([(1991, 1)]));
    assert_eq!(proof.inits_and_teardown_proofs.len(), 1);
    for (id, name) in RISCV {
        assert_eq!(setups[&id].family_idx, id);
        check_layout(name, &proof.compiled_riscv_circuits[&id]);
        for p in proof.riscv_proofs.get(&id).into_iter().flatten() {
            check_schedule(name, &p.whir_proof.whir_schedule);
        }
    }
    check_layout(
        "unrolled_circuits/inits_and_teardowns",
        proof.inits_and_teardowns_circuit.as_ref().unwrap(),
    );
    check_schedule(
        "unrolled_circuits/inits_and_teardowns",
        &proof.inits_and_teardown_proofs[0].whir_proof.whir_schedule,
    );
    check_layout(
        "blake2_with_compression",
        &proof.compiled_delegation_circuits[&1991],
    );
    check_schedule(
        "blake2_with_compression",
        &proof.delegation_proofs[&1991][0].whir_proof.whir_schedule,
    );
}

pub fn verify(stream: &[u32]) -> [u32; 16] {
    assert_eq!(
        verifier_common::BLAKE_MODE,
        BlakeMode::Compression,
        "enable miri_fsv for the compression guest opening layout"
    );
    std::thread::scope(|scope| {
        std::thread::Builder::new().stack_size(1 << 27).spawn_scoped(scope, || {
            let mut nds = stream.iter().copied();
            let output = full_statement_verifier::unrolled_proof_statement::verify_unrolled_base_layer::<
                _, DebugErrorCreator, {verifier_common::USE_REDUCED_BLAKE2_ROUNDS}
            >(&mut nds, SecurityLevel::Sec100, SoundnessMode::PessimisticConjecture).unwrap();
            std::hint::black_box(output);
            assert!(nds.next().is_none(), "full statement verifier left NDS words");
            assert_eq!(output[..8], [1,0,3010984625,0,0,0,0,0]);
            output
        }).unwrap().join().unwrap()
    })
}

pub fn write_fixture(mut proof: ProgramProof, setups: setups::Setups, out: &Path) {
    for layout in proof
        .compiled_riscv_circuits
        .values_mut()
        .chain(proof.compiled_delegation_circuits.values_mut())
        .chain(proof.inits_and_teardowns_circuit.iter_mut())
    {
        canonicalize(layout);
    }
    validate(&proof, &setups);
    let stream = host_utils::build_unrolled_stream(&setups, &proof, BlakeMode::Compression);
    let expected_output = verify(&stream);
    let (binary, text) = program();
    let (riscv_proofs, delegation_proofs) = counts(&proof);
    let manifest = Manifest {
        version: 1,
        program: PROGRAM.into(),
        program_digest: host_utils::fsv_digest(&binary, &text).to_string(),
        reads: READS,
        security_level: "sec100".into(),
        soundness_mode: "pessimistic_conjecture".into(),
        expected_output,
        riscv_proofs,
        inits_and_teardowns_proofs: proof.inits_and_teardown_proofs.len(),
        delegation_proofs,
    };
    std::fs::create_dir_all(out).unwrap();
    for (name, bytes) in [
        (
            FILES[0],
            host_utils::fixture_codec::encode(&proof, Vec::new()),
        ),
        (
            FILES[1],
            host_utils::fixture_codec::encode(&setups, Vec::new()),
        ),
    ] {
        std::fs::write(out.join(name), bytes).unwrap();
    }
    let mut file = std::fs::File::create(out.join(FILES[2])).unwrap();
    serde_json::to_writer_pretty(&mut file, &manifest).unwrap();
    file.write_all(b"\n").unwrap();
    // Validate the stored encoding through the same path used for CI input prep.
    let (_, decoded_manifest) = load(out);
    assert_eq!(decoded_manifest, manifest);
    println!("wrote deterministic fixture files to {}", out.display());
}

pub fn load(dir: &Path) -> (Vec<u32>, Manifest) {
    let proof: ProgramProof =
        host_utils::fixture_codec::decode(&std::fs::read(dir.join(FILES[0])).unwrap());
    let setups: setups::Setups =
        host_utils::fixture_codec::decode(&std::fs::read(dir.join(FILES[1])).unwrap());
    let manifest: Manifest =
        serde_json::from_slice(&std::fs::read(dir.join(FILES[2])).unwrap()).unwrap();
    assert_eq!(manifest.version, 1);
    assert_eq!(manifest.program, PROGRAM);
    assert_eq!(manifest.reads, READS);
    assert_eq!(manifest.security_level, "sec100");
    assert_eq!(manifest.soundness_mode, "pessimistic_conjecture");
    let (binary, text) = program();
    assert_eq!(
        manifest.program_digest,
        host_utils::fsv_digest(&binary, &text).to_string(),
        "program changed; regenerate fixture"
    );
    validate(&proof, &setups);
    let (riscv, delegation) = counts(&proof);
    assert_eq!(manifest.riscv_proofs, riscv);
    assert_eq!(manifest.delegation_proofs, delegation);
    assert_eq!(
        manifest.inits_and_teardowns_proofs,
        proof.inits_and_teardown_proofs.len()
    );
    let stream = host_utils::build_unrolled_stream(&setups, &proof, BlakeMode::Compression);
    assert_eq!(verify(&stream), manifest.expected_output);
    (stream, manifest)
}
