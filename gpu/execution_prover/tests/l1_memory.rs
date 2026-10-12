#![cfg(not(no_cuda))]
#![feature(allocator_api)]

gpu_core::force_serial_libtest!();

use cpu_execution_prover::test_support::with_l1_wrap_fixture;
use cpu_execution_prover::CpuExecutionProverConfiguration;
use full_statement_verifier::host_utils::{build_unified_stream, load_fsv_program};
use full_statement_verifier::program_proof::ProgramProof;
use gpu_execution_prover::memory_sweep::l1::{run_case, CapacityCase, Stage, WrapSource};
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

#[derive(Deserialize)]
struct ReferenceConfiguration {
    security_level: String,
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
    proof: ProgramProof,
    setups: Setups,
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
        .unwrap_or_else(|error| panic!("L1 capacity reference open {}: {error}", path.display()));
    serde_json::from_reader(BufReader::new(file)).unwrap_or_else(|error| {
        panic!(
            "L1 capacity reference deserialize {}: {error}",
            path.display()
        )
    })
}

fn keccak_hex(bytes: &[u8]) -> String {
    Keccak256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn proof_manifest() -> ProofManifest {
    let manifest: ProofManifest = read_typed(&l1_reference_dir().join("manifest.json"));
    assert_eq!(
        manifest.format_version, 1,
        "L1 capacity proof manifest format"
    );
    assert_eq!(
        manifest.configuration.security_level, "Sec100",
        "L1 capacity reference security level"
    );
    manifest
}

fn checkpoint(manifest: &ProofManifest, name: &str, target: &str) -> Checkpoint {
    let entry = manifest
        .files
        .iter()
        .find(|file| file.name == name)
        .unwrap_or_else(|| panic!("L1 capacity manifest omits {name}"));
    let path = l1_reference_dir().join(name);
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
    let checkpoint: Checkpoint = serde_json::from_slice(&data)
        .unwrap_or_else(|error| panic!("L1 capacity checkpoint {name}: {error}"));
    assert_eq!(
        checkpoint.schema_version, 4,
        "L1 capacity checkpoint schema: {name}"
    );
    assert_eq!(
        checkpoint.target, target,
        "L1 capacity checkpoint target: {name}"
    );
    checkpoint
}

fn fsv_feeder(manifest: &ProofManifest) -> (Vec<u32>, Vec<u32>) {
    let dir = std::env::var_os("FSV_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tools/gkr_verifier"));
    let program = FsvProgram::UnifiedRecursionLayerL1Feeder;
    let mode = BlakeMode::BlakeSpecialOpcodes;
    let stem = program.file_stem(mode);
    let entry = manifest
        .fsv
        .iter()
        .find(|entry| entry.role == "feeder")
        .expect("L1 capacity manifest omits fsv role feeder");
    assert_eq!(stem, entry.stem, "L1 capacity fsv stem differs: feeder");
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
            "L1 capacity fsv identity differs: feeder.{extension}"
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
        let feeder = checkpoint(&manifest, "l1_feeder.json", "L1Feeder");
        let (bin, text) = fsv_feeder(&manifest);
        let nd_words = build_unified_stream(&feeder.setups, &feeder.proof);
        drop(feeder);
        with_l1_wrap_fixture(
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
                    }),
                )
            },
        )
    } else {
        run_case::<std::alloc::Global>(&case, None)
    };
    log::info!(
        "L1 capacity case {}: fits {}, measured peak {:?} B, failed phase {:?}",
        row.case,
        row.fits,
        row.measured_peak_bytes,
        row.failed_phase
    );
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
