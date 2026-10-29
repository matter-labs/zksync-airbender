use prover_pipeline::{L1Bundle, ProofArtifact};
use std::{
    fs::File,
    path::{Path, PathBuf},
};

/// Run after the actual GPU CLI basic_fibonacci L1 proof has passed verification.
#[test]
#[ignore = "compares the actual CLI artifact at AB_L1_CLI_ARTIFACT to the CPU reference"]
fn cli_l1_bundle_matches_cpu_reference() {
    let path = std::env::var_os("AB_L1_CLI_ARTIFACT").expect("AB_L1_CLI_ARTIFACT");
    let artifact: ProofArtifact =
        serde_json::from_reader(File::open(path).expect("CLI artifact")).expect("proof artifact");
    let root = std::env::var_os("AB_TEST_ARTIFACT_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."));
    let path = root.join("prover_pipeline/fixtures/l1_reference_2p21/l1_bundle.json");
    let reference: L1Bundle =
        serde_json::from_reader(File::open(path).expect("CPU reference")).expect("L1 bundle");
    // Typed serialization preserves every u128 proof integer.
    assert_eq!(
        serde_json::to_vec(&artifact.l1.expect("CLI L1 bundle")).unwrap(),
        serde_json::to_vec(&reference).unwrap(),
    );
}
