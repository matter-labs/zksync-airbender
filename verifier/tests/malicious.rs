#![cfg(feature = "gkr_verify")]

#[macro_use]
mod common;

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::DefaultTreeConstructor;
use verifier_common::errors::DebugErrorCreator;
use verifier_common::gkr::flatten::flatten_gkr_proof_for_nds;
use verifier_common::prover::nd_source_std::{set_iterator, ThreadLocalBasedSource};

const CIRCUIT_NAME: &str = "jump_branch_slt";

fn repo_root() -> String {
    format!("{}/..", env!("CARGO_MANIFEST_DIR"))
}

fn deserialize_from_file<T: serde::de::DeserializeOwned>(path: &str) -> T {
    let src = std::fs::File::open(path).unwrap_or_else(|e| {
        panic!(
            "failed to open {}: {} — did you run the malicious prover tests first?",
            path, e
        )
    });
    serde_json::from_reader(src).unwrap()
}

fn verify_nds(nds: Vec<u32>) -> bool {
    let prev_hook = std::panic::take_hook();
    let panic_msg = std::sync::Arc::new(std::sync::Mutex::new(None::<String>));
    let panic_msg_clone = panic_msg.clone();
    std::panic::set_hook(Box::new(move |info| {
        *panic_msg_clone.lock().unwrap() = Some(format!("{}", info));
    }));

    let accepted = std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name("malicious_verify".to_string())
            .stack_size(1 << 27)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                with_circuit!(CIRCUIT_NAME, |m| {
                    m::verify::<ThreadLocalBasedSource, DebugErrorCreator>()
                        .map_err(|e| format!("{:?}", e))
                })
            })
            .expect("failed to spawn thread");

        match handle.join() {
            Ok(Ok(())) => true,
            Ok(Err(e)) => {
                println!("  [malicious test] rejected via error: {}", e);
                false
            }
            Err(_) => false,
        }
    });

    std::panic::set_hook(prev_hook);

    if !accepted {
        if let Some(msg) = panic_msg.lock().unwrap().take() {
            println!("  [malicious test] rejected via panic: {}", msg);
        }
    }

    accepted
}

fn load_malicious_proof(
    variant: &str,
) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
    let path = format!(
        "{}/prover/test_proofs/malicious_{}_gkr_proof.json",
        repo_root(),
        variant
    );
    deserialize_from_file(&path)
}

fn malicious_proof_to_nds(variant: &str) -> Vec<u32> {
    let proof = load_malicious_proof(variant);
    let circuit_data = common::circuit_by_name(CIRCUIT_NAME);
    let compiled = circuit_data.compiled_circuit();
    flatten_gkr_proof_for_nds::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
        &proof,
        &compiled,
        circuit_data.whir_schedule(),
        &[],
    )
}

fn test_rejects_malicious(variant: &str) {
    let nds = malicious_proof_to_nds(variant);
    assert!(
        !verify_nds(nds),
        "verifier should reject malicious proof: {}",
        variant
    );
}

#[test]
#[ignore]
fn rejects_malicious_lookup_16bits() {
    test_rejects_malicious("lookup_16bits");
}

#[test]
#[ignore]
fn rejects_malicious_lookup_timestamps() {
    test_rejects_malicious("lookup_timestamps");
}

#[test]
#[ignore]
fn rejects_malicious_lookup_generic() {
    test_rejects_malicious("lookup_generic");
}

#[test]
#[ignore]
fn rejects_malicious_witness_value() {
    test_rejects_malicious("witness_value");
}

#[test]
#[ignore]
fn rejects_malicious_memory_value() {
    test_rejects_malicious("memory_value");
}
