#![cfg(not(no_cuda))]
#![feature(allocator_api)]

gpu_core::force_serial_libtest!();

use cpu_execution_prover::test_support::with_l1_wrap_fixture;
use cpu_execution_prover::CpuExecutionProverConfiguration;
use full_statement_verifier::host_utils::{build_unified_stream, load_fsv_program};
use full_statement_verifier::program_proof::ProgramProof;
use gpu_execution_prover::memory_sweep::l1::{run_case, CapacityCase, Stage, WrapSource};
use prover::gkr::prover_config::example_configs::L1_FEEDER_QUERIES_AND_POW;
use serde::Deserialize;
use setups::Setups;
use sha3::{Digest, Keccak256};
use std::fs::{self, File};
use std::io::BufReader;
use std::path::{Path, PathBuf};
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

#[derive(Deserialize)]
struct FsvIdentity {
    role: String,
    stem: String,
    bin_keccak256: String,
    text_keccak256: String,
}

/// The fields of `prover_pipeline`'s feeder reference manifest this test reads.
#[derive(Deserialize)]
struct FeederManifest {
    fixture_schema_version: u32,
    fsv: Vec<FsvIdentity>,
    feeder_queries_and_pow: Vec<(usize, u32)>,
    files: Vec<(String, u64, String)>,
}

/// The fields of the reference `l1_feeder.json` (`prover_pipeline::ProofArtifact`) this test reads.
#[derive(Deserialize)]
struct FeederArtifact {
    schema_version: u32,
    target: String,
    proof: ProgramProof,
    setups: Setups,
}

fn feeder_reference_dir() -> PathBuf {
    let root = std::env::var_os("AB_F3_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../prover_pipeline/fixtures/l1_feeder_reference")
        });
    root.join(std::env::var("AB_F3_INPUT").unwrap_or_else(|_| "basic_fibonacci".into()))
}

fn keccak_hex(bytes: &[u8]) -> String {
    Keccak256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn feeder_manifest() -> FeederManifest {
    let path = feeder_reference_dir().join("manifest.json");
    let file = File::open(&path)
        .unwrap_or_else(|error| panic!("L1 capacity manifest open {}: {error}", path.display()));
    let manifest: FeederManifest = serde_json::from_reader(BufReader::new(file))
        .unwrap_or_else(|error| panic!("L1 capacity manifest {}: {error}", path.display()));
    assert_eq!(
        manifest.fixture_schema_version, 1,
        "L1 capacity feeder reference schema"
    );
    assert_eq!(
        manifest.feeder_queries_and_pow,
        L1_FEEDER_QUERIES_AND_POW.to_vec(),
        "L1 capacity feeder reference was produced under another feeder config"
    );
    manifest
}

fn feeder_artifact(manifest: &FeederManifest) -> FeederArtifact {
    let name = "l1_feeder.json";
    let (_, bytes, keccak256) = manifest
        .files
        .iter()
        .find(|(file, _, _)| file == name)
        .unwrap_or_else(|| panic!("L1 capacity manifest omits {name}"));
    let path = feeder_reference_dir().join(name);
    let data = fs::read(&path)
        .unwrap_or_else(|error| panic!("L1 capacity read {}: {error}", path.display()));
    assert_eq!(
        data.len() as u64,
        *bytes,
        "L1 capacity reference size differs: {name}"
    );
    assert_eq!(
        keccak_hex(&data),
        *keccak256,
        "L1 capacity reference identity differs: {name}"
    );
    let artifact: FeederArtifact = serde_json::from_slice(&data)
        .unwrap_or_else(|error| panic!("L1 capacity artifact {name}: {error}"));
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

fn fsv_feeder_wrap(manifest: &FeederManifest) -> (Vec<u32>, Vec<u32>) {
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
        let manifest = feeder_manifest();
        let feeder = feeder_artifact(&manifest);
        let (bin, text) = fsv_feeder_wrap(&manifest);
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
