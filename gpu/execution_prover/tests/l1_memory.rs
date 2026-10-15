#![cfg(not(no_cuda))]
#![feature(allocator_api)]

gpu_core::force_serial_libtest!();

use cpu_execution_prover::test_support::with_l1_wrap_fixture_for;
use cpu_execution_prover::CpuExecutionProverConfiguration;
use execution_prover::ExecutionKind;
use full_statement_verifier::host_utils::{build_unified_stream, load_fsv_program};
use full_statement_verifier::program_proof::ProgramProof;
use gpu_execution_prover::memory_sweep::l1::{
    run_case, CapacityCase, Stage, WrapReference, WrapSource, WRAP_QUALIFYING_GIB,
};
use serde::de::DeserializeOwned;
use serde::Deserialize;
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::fs::{self, File};
use std::io::BufReader;
use std::path::{Path, PathBuf};
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

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

/// The fields of the 2p21 wrap reference manifest this test reads.
#[derive(Deserialize)]
struct ProofManifest {
    format_version: u32,
    fsv: Vec<FsvIdentity>,
    files: Vec<FileIdentity>,
}

/// The fields of the reference `l1_feeder.json` (`prover_pipeline::ProofArtifact`) this test reads.
#[derive(Deserialize)]
struct FeederArtifact {
    schema_version: u32,
    target: String,
    proof: ProgramProof,
    setups: Setups,
}

fn reference_dir() -> PathBuf {
    std::env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../prover_pipeline/fixtures/l1_reference_2p21")
        })
}

fn keccak_hex(bytes: &[u8]) -> String {
    Keccak256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn proof_manifest() -> ProofManifest {
    let path = reference_dir().join("manifest.json");
    let file = File::open(&path)
        .unwrap_or_else(|error| panic!("L1 capacity manifest open {}: {error}", path.display()));
    let manifest: ProofManifest = serde_json::from_reader(BufReader::new(file))
        .unwrap_or_else(|error| panic!("L1 capacity manifest {}: {error}", path.display()));
    assert_eq!(
        manifest.format_version, 1,
        "L1 capacity wrap reference manifest format"
    );
    manifest
}

fn read_checked<T: DeserializeOwned>(manifest: &ProofManifest, name: &str) -> T {
    let entry = manifest
        .files
        .iter()
        .find(|file| file.name == name)
        .unwrap_or_else(|| panic!("L1 capacity manifest omits {name}"));
    let path = reference_dir().join(name);
    let data = fs::read(&path)
        .unwrap_or_else(|error| panic!("L1 capacity read {}: {error}", path.display()));
    assert_eq!(
        data.len() as u64,
        entry.bytes,
        "L1 capacity reference size differs: {name}"
    );
    assert_eq!(
        keccak_hex(&data),
        entry.keccak256,
        "L1 capacity reference identity differs: {name}"
    );
    serde_json::from_slice(&data)
        .unwrap_or_else(|error| panic!("L1 capacity artifact {name}: {error}"))
}

fn feeder_artifact(manifest: &ProofManifest) -> FeederArtifact {
    let name = "l1_feeder.json";
    let artifact: FeederArtifact = read_checked(manifest, name);
    assert_eq!(
        artifact.schema_version, 5,
        "L1 capacity artifact schema: {name}"
    );
    assert_eq!(
        artifact.target, "L1Feeder",
        "L1 capacity artifact target: {name}"
    );
    artifact
}

fn fsv_feeder_wrap(manifest: &ProofManifest) -> (Vec<u32>, Vec<u32>) {
    let dir = std::env::var_os("FSV_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tools/gkr_verifier"));
    let program = FsvProgram::UnifiedRecursionLayerL1FeederWrap;
    let mode = BlakeMode::BlakeSpecialOpcodes;
    let stem = program.file_stem(mode);
    let entry = manifest
        .fsv
        .iter()
        .find(|entry| entry.role == "feeder_wrap")
        .expect("L1 capacity manifest omits fsv role feeder_wrap");
    assert_eq!(
        stem, entry.stem,
        "L1 capacity fsv stem differs: feeder_wrap"
    );
    for (extension, expected) in [
        ("bin", &entry.bin_keccak256),
        ("text", &entry.text_keccak256),
    ] {
        let path = dir.join(format!("{stem}.{extension}"));
        let data = fs::read(&path)
            .unwrap_or_else(|error| panic!("L1 capacity fsv read {}: {error}", path.display()));
        assert_eq!(
            keccak_hex(&data),
            *expected,
            "L1 capacity fsv identity differs: feeder_wrap.{extension}"
        );
    }
    load_fsv_program(&dir, program, mode)
}

fn run(stage: Stage) {
    let _ = env_logger::builder()
        .is_test(true)
        .filter_level(log::LevelFilter::Info)
        .format_timestamp_millis()
        .try_init();
    let case = CapacityCase::from_env(stage);
    let row = if case.needs_wrap_source() {
        let manifest = proof_manifest();
        let feeder = feeder_artifact(&manifest);
        let reference: WrapReference = read_checked(&manifest, "l1_bundle.json");
        assert_eq!(reference.wrap, "2p21", "L1 capacity bundle wrap version");
        let (bin, text) = fsv_feeder_wrap(&manifest);
        let nd_words = build_unified_stream(&feeder.setups, &feeder.proof);
        drop(feeder);
        with_l1_wrap_fixture_for(
            ExecutionKind::L1Wrap21,
            CpuExecutionProverConfiguration::default(),
            bin,
            text,
            nd_words,
            None,
            move |fixture| {
                run_case(
                    &case,
                    Some(WrapSource {
                        setup: fixture.setup,
                        tracing_data: fixture.tracing_data,
                        inits_and_teardowns: fixture.inits_and_teardowns,
                        commitment_mode: fixture.commitment_mode,
                        reference: &reference,
                    }),
                )
            },
        )
    } else {
        run_case::<std::alloc::Global>(&case, None)
    };
    log::info!(
        "L1 capacity case {}: fits {}, proof_equals_reference {:?}, measured peak {:?} B, failed phase {:?}",
        row.case,
        row.fits,
        row.proof_equals_reference,
        row.measured_peak_bytes,
        row.failed_phase
    );
    // run_case writes the evidence row before any correctness or qualification assertion.
    if row.stage == Stage::Wrap {
        if row.fits || row.output_fingerprint.is_some() || row.proof_equals_reference.is_some() {
            assert_eq!(
                row.proof_equals_reference,
                Some(true),
                "L1 capacity completed wrap proof differs from the reference: {}",
                row.case
            );
        }
        if row.arena_bytes == WRAP_QUALIFYING_GIB << 30 {
            assert!(
                row.fits,
                "L1 capacity wrap does not fit the qualifying arena: {}",
                row.case
            );
        }
    }
}

#[test]
fn cpu_w5_wrap_capacity_reference_is_current() {
    let manifest = proof_manifest();
    let _feeder = feeder_artifact(&manifest);
    let reference: WrapReference = read_checked(&manifest, "l1_bundle.json");
    assert_eq!(reference.wrap, "2p21");
    // The typed round trip reproduces the bundle's own serialization of both fields.
    let bundle = fs::read(reference_dir().join("l1_bundle.json")).unwrap();
    for field in [&reference.proof_json, &reference.commitment_mode_json] {
        assert!(bundle
            .windows(field.len())
            .any(|window| window == &field[..]));
    }
    let (bin, text) = fsv_feeder_wrap(&manifest);
    assert!(!bin.is_empty() && !text.is_empty());
}

#[test]
#[ignore]
fn l1_wrap_capacity_case() {
    run(Stage::Wrap);
}

#[test]
#[ignore]
fn l1_feeder_commit_capacity_case() {
    run(Stage::FeederCommit);
}

#[test]
#[ignore]
fn l1_feeder_proof_capacity_case() {
    run(Stage::FeederProof);
}
