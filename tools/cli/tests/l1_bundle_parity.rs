use prover_pipeline::{L1Bundle, ProofArtifact};
use serde::de::DeserializeOwned;
use serde::Serialize;
use std::collections::BTreeSet;
use std::env;
use std::ffi::OsString;
use std::fs::{self, File};
use std::io::BufReader;
use std::path::{Path, PathBuf};

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn reference_dir() -> PathBuf {
    env::var_os("AB_PROTH120_REFERENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| workspace_root().join("prover_pipeline/fixtures/l1_reference"))
}

fn artifact_path(value: Option<OsString>) -> PathBuf {
    value
        .map(PathBuf::from)
        .expect("M8_CLI_ARTIFACT is not set")
}

fn read_typed<T: DeserializeOwned>(path: &Path, name: &str) -> T {
    let file =
        File::open(path).unwrap_or_else(|error| panic!("{name} open {}: {error}", path.display()));
    serde_json::from_reader(BufReader::new(file))
        .unwrap_or_else(|error| panic!("{name} deserialize {}: {error}", path.display()))
}

fn compare_artifact_to_reference(artifact: &Path) {
    let artifact: ProofArtifact = read_typed(artifact, "M8 CLI artifact");
    let actual = artifact.l1.expect("M8 CLI artifact has no l1 bundle");
    let expected: L1Bundle = read_typed(&reference_dir().join("l1_bundle.json"), "L1 reference");
    if bytes(&expected) != bytes(&actual) {
        let differences = bundle_differences(&expected, &actual);
        let first = differences.first().map(String::as_str).unwrap_or("bundle");
        panic!("L1 bundle mismatch: {first}");
    }
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

fn bundle_differences(expected: &L1Bundle, actual: &L1Bundle) -> Vec<String> {
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

fn comparator_file(name: &str) -> PathBuf {
    let root = workspace_root();
    let target = env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join("target"));
    let target = if target.is_absolute() {
        target
    } else {
        root.join(target)
    };
    let dir = target.join("m8-comparator");
    fs::create_dir_all(&dir).expect("M8 comparator directory");
    dir.join(name)
}

fn write_artifact(path: &Path, artifact: &ProofArtifact) {
    fs::write(path, bytes(artifact)).expect("M8 comparator artifact write");
}

fn assert_named_panic(f: impl FnOnce() + std::panic::UnwindSafe, expected: &str) {
    let panic = std::panic::catch_unwind(f).expect_err("M8 comparator must reject invalid input");
    let message = panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .expect("M8 comparator named panic");
    assert!(message.contains(expected), "{message}");
}

#[test]
#[ignore]
fn cpu_m8_cli_l1_bundle_parity() {
    compare_artifact_to_reference(&artifact_path(env::var_os("M8_CLI_ARTIFACT")));
}

#[test]
fn cpu_m8_cli_l1_bundle_parity_reference_roundtrip() {
    let mut artifact: ProofArtifact = read_typed(
        &reference_dir().join("l1_feeder.json"),
        "L1 feeder reference",
    );
    assert!(
        artifact.l1.is_none(),
        "L1 feeder reference must have no l1 bundle"
    );
    artifact.l1 = Some(read_typed(
        &reference_dir().join("l1_bundle.json"),
        "L1 reference",
    ));
    let path = comparator_file("roundtrip.json");
    write_artifact(&path, &artifact);
    compare_artifact_to_reference(&path);
}

#[test]
fn cpu_m8_cli_l1_bundle_parity_rejects_missing() {
    assert_named_panic(
        || {
            artifact_path(None);
        },
        "M8_CLI_ARTIFACT is not set",
    );
    let missing = comparator_file("missing.json");
    if missing.exists() {
        fs::remove_file(&missing).expect("M8 comparator missing-file control");
    }
    assert_named_panic(
        || compare_artifact_to_reference(&missing),
        "M8 CLI artifact open",
    );
    let mut artifact: ProofArtifact = read_typed(
        &reference_dir().join("l1_feeder.json"),
        "L1 feeder reference",
    );
    assert!(
        artifact.l1.is_none(),
        "L1 feeder reference must have no l1 bundle"
    );
    let path = comparator_file("no-l1.json");
    write_artifact(&path, &artifact);
    assert_named_panic(
        || compare_artifact_to_reference(&path),
        "M8 CLI artifact has no l1 bundle",
    );
    artifact.l1 = Some(read_typed(
        &reference_dir().join("l1_bundle.json"),
        "L1 reference",
    ));
    artifact
        .l1
        .as_mut()
        .expect("M8 comparator reference bundle")
        .proof
        .lookup_challenges_pow_nonce ^= 1;
    let path = comparator_file("mismatch.json");
    write_artifact(&path, &artifact);
    assert_named_panic(
        || compare_artifact_to_reference(&path),
        "L1 bundle mismatch: lookup_challenges_pow_nonce",
    );
}
