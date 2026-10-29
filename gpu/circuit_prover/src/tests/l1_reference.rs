//! Loader convention for the committed Proth120 L1 reference set; stage tests copy
//! `ReferenceBundle`, `l1_reference_dir`, `l1_bundle` and `assert_bundle_eq`.
//!
//! The set is produced by `prover_pipeline`'s `l1_reference::generate_l1_reference_seed` followed by
//! `l1_reference::generate_l1_reference_from_recursion_unified` into the
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
use prover::gkr::prover::{GKRProof, OperationMode};
use prover::gkr::prover_config::example_configs::l1_wrap_2p21::{
    EXTERNAL_CHALLENGES_POW_BITS, TRACE_LEN_LOG2,
};
use prover::gkr::prover_config::ProofProfile;
use prover::merkle_trees::keccak256_for_everything_tree::Keccak256MerkleTreeWithCap;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use sha3::{Digest, Keccak256};
use std::fs::{self, File};
use std::io::BufReader;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};

type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct ReferenceBundle {
    pub(crate) proof: L1Proof,
    pub(crate) operation_mode: OperationMode,
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

fn bundle_differences(expected: &ReferenceBundle, actual: &ReferenceBundle) -> Vec<String> {
    let mut differences = Vec::new();
    macro_rules! compare {
        ($name:expr, $expected:expr, $actual:expr) => {
            if bytes($expected) != bytes($actual) {
                differences.push($name.to_string());
            }
        };
    }
    let (e, a) = (&expected.proof, &actual.proof);
    compare!(
        "operation_mode",
        &expected.operation_mode,
        &actual.operation_mode
    );
    compare!(
        "external_challenges",
        &e.external_challenges,
        &a.external_challenges
    );
    compare!(
        "final_explicit_evaluations",
        &e.final_explicit_evaluations,
        &a.final_explicit_evaluations
    );
    compare!(
        "sumcheck_intermediate_values",
        &e.sumcheck_intermediate_values,
        &a.sumcheck_intermediate_values
    );
    compare!(
        "grand_product_accumulator_computed",
        &e.grand_product_accumulator_computed,
        &a.grand_product_accumulator_computed
    );
    compare!(
        "inits_and_teardowns_top_bits",
        &e.inits_and_teardowns_top_bits,
        &a.inits_and_teardowns_top_bits
    );
    compare!(
        "lookup_challenges_pow_nonce",
        &e.lookup_challenges_pow_nonce,
        &a.lookup_challenges_pow_nonce
    );
    let (e, a) = (&e.whir_proof, &a.whir_proof);
    compare!(
        "whir.setup_commitment",
        &e.setup_commitment,
        &a.setup_commitment
    );
    compare!(
        "whir.memory_commitment",
        &e.memory_commitment,
        &a.memory_commitment
    );
    compare!(
        "whir.witness_commitment",
        &e.witness_commitment,
        &a.witness_commitment
    );
    compare!(
        "whir.batching_challenge_pow_nonce",
        &e.batching_challenge_pow_nonce,
        &a.batching_challenge_pow_nonce
    );
    compare!(
        "whir.base_sumcheck_polys",
        &e.base_sumcheck_polys,
        &a.base_sumcheck_polys
    );
    compare!(
        "whir.base_folding_pow_nonces",
        &e.base_folding_pow_nonces,
        &a.base_folding_pow_nonces
    );
    compare!(
        "whir.base_queries_pow_nonce",
        &e.base_queries_pow_nonce,
        &a.base_queries_pow_nonce
    );
    compare!(
        "whir.intermediate_whir_oracles",
        &e.intermediate_whir_oracles,
        &a.intermediate_whir_oracles
    );
    compare!(
        "whir.final_monomials",
        &e.final_monomials,
        &a.final_monomials
    );
    compare!("whir.whir_schedule", &e.whir_schedule, &a.whir_schedule);
    differences
}

pub(crate) fn assert_bundle_eq(expected: &ReferenceBundle, actual: &ReferenceBundle) {
    let differences = bundle_differences(expected, actual);
    assert!(
        differences.is_empty(),
        "L1 bundle mismatch: {}",
        differences.join(", ")
    );
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

fn empty_whir(
) -> prover::gkr::whir::WhirPolyCommitProof<Proth120, Proth120, Keccak256MerkleTreeWithCap> {
    let oracle = || prover::gkr::whir::WhirBaseLayerCommitmentAndQueries {
        commitment: Default::default(),
        num_columns: 0,
        evals: vec![],
        queries: vec![],
    };
    prover::gkr::whir::WhirPolyCommitProof {
        setup_commitment: oracle(),
        memory_commitment: oracle(),
        witness_commitment: oracle(),
        batching_challenge_pow_nonce: 0,
        base_sumcheck_polys: vec![],
        base_folding_pow_nonces: vec![],
        base_queries_pow_nonce: 0,
        intermediate_whir_oracles: vec![],
        final_monomials: vec![],
        whir_schedule: ProofProfile::L1Wrap
            .prover_config(21, SecurityLevel::Sec100)
            .whir_schedule,
    }
}

fn synthetic_bundle(accumulator: u128) -> ReferenceBundle {
    ReferenceBundle {
        proof: L1Proof {
            external_challenges: Default::default(),
            final_explicit_evaluations: Default::default(),
            sumcheck_intermediate_values: Default::default(),
            whir_proof: empty_whir(),
            grand_product_accumulator_computed: Proth120(accumulator),
            inits_and_teardowns_top_bits: vec![],
            lookup_challenges_pow_nonce: 0,
        },
        operation_mode: OperationMode::MultipleChunks,
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
    assert_eq!(whir.queries_pow_nonces().len(), 5);
    assert_eq!(whir.intermediate_whir_oracles.len(), 4);
    assert_eq!(whir.all_ood_samples().count(), 4);
    assert_eq!(whir.all_sumcheck_polys().count(), 17);
    assert_eq!(whir.final_monomials.len(), 128);
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
            Some(br#"{"operation_mode":"MultipleChunks"}"#.to_vec()),
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

#[test]
fn cpu_l1_bundle_diff_names_canonical_whir_fields() {
    let expected = synthetic_bundle(7);
    let mut actual = expected.clone();
    actual.proof.whir_proof.batching_challenge_pow_nonce = 9;
    actual.proof.whir_proof.base_queries_pow_nonce = 10;
    assert_eq!(
        bundle_differences(&expected, &actual),
        [
            "whir.batching_challenge_pow_nonce",
            "whir.base_queries_pow_nonce"
        ]
    );
}
