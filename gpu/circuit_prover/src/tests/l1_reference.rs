//! Loader convention for the committed Proth120 L1 reference set; stage tests copy
//! `ReferenceBundle`, `l1_reference_dir`, `l1_bundle` and `assert_bundle_eq`.
//!
//! The set is produced by `prover_pipeline`'s `l1_reference::generate_l1_reference` into the
//! tracked `prover_pipeline/fixtures/l1_reference_2p21` (`../../prover_pipeline/fixtures/l1_reference_2p21`
//! from a `gpu/<crate>` manifest dir); `AB_PROTH120_REFERENCE_DIR` overrides the directory. A
//! missing or malformed file is a failure, never a skip. Every file is read into a local typed
//! projection with `serde_json::from_reader`: `Proth120` serializes its raw Montgomery `u128`,
//! which `serde_json::Value` cannot hold above `u64::MAX` without `arbitrary_precision`.
//! Equality is byte equality of `serde_json::to_vec` of the typed bundle; on mismatch
//! `assert_bundle_eq` names the differing root fields, the first differing sumcheck layer and
//! the first differing WHIR member, with sumcheck polynomials mapped to their WHIR round.

use prover::definitions::SecurityLevel;
use prover::field::Proth120;
use prover::gkr::prover::{CommitmentMode, GKRProof};
use prover::gkr::prover_config::example_configs::l1_wrap_2p21::{
    EXTERNAL_CHALLENGES_POW_BITS, PACK_LOG2, TRACE_LEN_LOG2,
};
use prover::gkr::prover_config::ProofProfile;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use sha3::{Digest, Keccak256};
use std::collections::BTreeSet;
use std::fs::{self, File};
use std::io::BufReader;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};

type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct ReferenceBundle {
    pub(crate) proof: L1Proof,
    pub(crate) commitment_mode: CommitmentMode,
}

#[derive(Deserialize)]
struct FileIdentity {
    name: String,
    keccak256: String,
}

#[derive(Deserialize)]
struct ProofManifest {
    files: Vec<FileIdentity>,
}

pub(crate) fn l1_reference_dir() -> PathBuf {
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

pub(crate) fn l1_bundle() -> ReferenceBundle {
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

pub(crate) fn assert_bundle_eq(expected: &ReferenceBundle, actual: &ReferenceBundle) {
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

fn scratch_dir(purpose: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/l1_reference_staging")
        .join(format!("{purpose}-{}", std::process::id()));
    fs::create_dir_all(&dir).expect("L1 reference scratch directory");
    dir
}

fn synthetic_bundle(accumulator: u128) -> ReferenceBundle {
    ReferenceBundle {
        proof: L1Proof {
            external_challenges: Default::default(),
            final_explicit_evaluations: Default::default(),
            sumcheck_intermediate_values: Default::default(),
            whir_proof: Default::default(),
            grand_product_accumulator_computed: Proth120(accumulator),
            inits_and_teardowns_top_bits: vec![],
            lookup_challenges_pow_nonce: 0,
            batched_proximity_check_pow_nonce: 0,
            intermediate_transcript_seed: None,
        },
        commitment_mode: CommitmentMode::MergedMemoryAndWitness,
    }
}

#[test]
fn cpu_l1_reference_loads() {
    let bundle = l1_bundle();
    let proof = &bundle.proof;
    let whir = &proof.whir_proof;
    assert_eq!(
        proof
            .sumcheck_intermediate_values
            .keys()
            .copied()
            .collect::<Vec<_>>(),
        (0..=23).collect::<Vec<_>>()
    );
    assert_eq!(
        whir.whir_schedule,
        ProofProfile::L1Wrap
            .prover_config(TRACE_LEN_LOG2, SecurityLevel::Sec100)
            .whir_schedule
    );
    assert_eq!(whir.pow_nonces.len(), 5);
    assert_eq!(whir.intermediate_whir_oracles.len(), 4);
    assert_eq!(whir.ood_samples.len(), 4);
    assert_eq!(whir.sumcheck_polys.len(), 17);
    assert_eq!(whir.final_monomials.len(), 128);
    assert!(whir.batching_challenge.is_some());
    assert_eq!(
        whir.original_evaluation_point
            .as_ref()
            .map(|point| point.len()),
        Some(24)
    );
    assert!(whir.batched_opening.is_some());
    assert!(proof.intermediate_transcript_seed.is_some());
    assert_eq!(whir.witness_commitment.num_columns, 0);
    assert_eq!(proof.inits_and_teardowns_top_bits.len(), 2);
    let manifest: ProofManifest = read_typed(&l1_reference_dir().join("manifest.json"));
    let entry = manifest
        .files
        .iter()
        .find(|file| file.name == "l1_bundle.json")
        .expect("L1 reference manifest lists l1_bundle.json");
    assert_eq!(
        entry.keccak256,
        keccak_hex(&fs::read(l1_reference_dir().join("l1_bundle.json")).unwrap())
    );
    assert_bundle_eq(&bundle, &bundle.clone());
}

#[test]
fn cpu_l1_reference_u128_round_trip() {
    let value = (u64::MAX as u128) + 0x1234_5678_9abc_def0;
    let bundle = synthetic_bundle(value);
    let encoded = bytes(&bundle);
    let decoded: ReferenceBundle = serde_json::from_slice(&encoded).unwrap();
    assert_eq!(decoded.proof.grand_product_accumulator_computed.0, value);
    assert_eq!(bytes(&decoded), encoded);
    let perturbed = synthetic_bundle(value ^ (1 << 100));
    assert_ne!(bytes(&perturbed), encoded);
    let message = catch_unwind(|| assert_bundle_eq(&bundle, &perturbed))
        .expect_err("a perturbed high limb must fail the comparison");
    assert_eq!(
        message.downcast_ref::<String>().map(String::as_str),
        Some("L1 bundle mismatch: grand_product_accumulator_computed")
    );
}

#[test]
fn cpu_l1_reference_rejects_malformed() {
    let reference = l1_reference_dir();
    let committed = fs::read(reference.join("l1_bundle.json")).unwrap();
    let dir = scratch_dir("malformed");
    let cases: [(&str, Option<Vec<u8>>, &str); 4] = [
        ("missing", None, "L1 reference open"),
        (
            "artifact",
            Some(fs::read(reference.join("l1_feeder.json")).unwrap()),
            "L1 reference deserialize",
        ),
        (
            "missing_field",
            Some(br#"{"commitment_mode":"MergedMemoryAndWitness"}"#.to_vec()),
            "L1 reference deserialize",
        ),
        (
            "truncated",
            Some(committed[..committed.len() / 2].to_vec()),
            "L1 reference deserialize",
        ),
    ];
    let previous = std::env::var_os("AB_PROTH120_REFERENCE_DIR");
    for (name, contents, expected) in cases {
        let case = dir.join(name);
        fs::create_dir_all(&case).unwrap();
        if let Some(contents) = contents {
            fs::write(case.join("l1_bundle.json"), contents).unwrap();
        }
        std::env::set_var("AB_PROTH120_REFERENCE_DIR", &case);
        let outcome = catch_unwind(AssertUnwindSafe(l1_bundle));
        match &previous {
            Some(previous) => std::env::set_var("AB_PROTH120_REFERENCE_DIR", previous),
            None => std::env::remove_var("AB_PROTH120_REFERENCE_DIR"),
        }
        let payload = outcome.expect_err(name);
        let message = payload
            .downcast_ref::<String>()
            .unwrap_or_else(|| panic!("{name}: loader panic carries a formatted message"));
        assert!(message.starts_with(expected), "{name}: {message}");
    }
    fs::remove_dir_all(dir).unwrap();
}
