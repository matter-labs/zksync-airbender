// GPU-produced ethproofs-soundcalc proofs on the generated verifiers of that
// mode: each proof is accepted, and flipping any one of its folding-challenge
// or OOD-draw PoW nonces is rejected. The proofs come from
// `gpu_circuit_prover`'s `run_*_ethproofs_proof_parity_test`s run with
// `AB_GPU_PROOF_EXPORT_DIR` set (each is byte-identical to the CPU proof of
// the same witness).

#[macro_use]
mod common;

use common::{SecurityLevel, SoundnessMode};
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::DefaultTreeConstructor;
use verifier_common::errors::DebugErrorCreator;

type Proof = GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>;

const PROOF_SUFFIX: &str = "_ethproofs_soundcalc_gpu_proof.json";

/// Runs `name`'s ethproofs-soundcalc verifier on `proof`. A rejection is
/// either a verification error or a panic (e.g. from `verify_pow`).
fn verify(name: &str, proof: &Proof) -> Result<(), String> {
    let (nds, external_challenges) = common::proof_to_nds(name, SecurityLevel::Sec100, proof);
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::thread::scope(|s| {
        std::thread::Builder::new()
            .name(format!("gpu proof verifier {name}"))
            .stack_size(common::VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                let mut it = nds.into_iter();
                with_circuit!(
                    name,
                    SecurityLevel::Sec100,
                    SoundnessMode::EthproofsSoundnessCalc,
                    |m| {
                        m::verify::<_, DebugErrorCreator>(&external_challenges, &mut it)
                            .map(|_| ())
                            .map_err(|e| format!("{e:?}"))
                    }
                )
            })
            .expect("failed to spawn verifier thread")
            .join()
    });
    std::panic::set_hook(prev_hook);
    match outcome {
        Ok(result) => result,
        Err(panic) => Err(panic
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_else(|| "panic".to_string())),
    }
}

#[test]
#[ignore = "needs GPU proofs exported to AB_GPU_PROOF_EXPORT_DIR by gpu_circuit_prover's ethproofs parity tests"]
fn gpu_ethproofs_proofs_verify_and_reject_tampered_pow_nonces() {
    let dir = std::env::var("AB_GPU_PROOF_EXPORT_DIR")
        .expect("AB_GPU_PROOF_EXPORT_DIR must name the GPU proof export directory");
    let mut checked = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        let Some(name) = path
            .file_name()
            .and_then(|file| file.to_str())
            .and_then(|file| file.strip_suffix(PROOF_SUFFIX))
        else {
            continue;
        };
        let proof: Proof =
            serde_json::from_reader(std::io::BufReader::new(std::fs::File::open(&path).unwrap()))
                .unwrap();
        verify(name, &proof).unwrap_or_else(|e| panic!("{name}: GPU proof rejected: {e}"));

        let mut tampered = 0;
        for (i, oracle) in proof.whir_proof.intermediate_whir_oracles.iter().enumerate() {
            for k in 0..oracle.folding_pow_nonces.len() {
                let mut bad = proof.clone();
                bad.whir_proof.intermediate_whir_oracles[i].folding_pow_nonces[k] ^= 1;
                assert!(
                    verify(name, &bad).is_err(),
                    "{name}: accepted a tampered folding nonce (oracle {i}, step {k})"
                );
                tampered += 1;
            }
            if let Some(nonce) = oracle.ood_pow_nonce {
                let mut bad = proof.clone();
                bad.whir_proof.intermediate_whir_oracles[i].ood_pow_nonce = Some(nonce ^ 1);
                assert!(
                    verify(name, &bad).is_err(),
                    "{name}: accepted a tampered OOD nonce (oracle {i})"
                );
                tampered += 1;
            }
        }
        assert!(tampered > 0, "{name}: proof carries no folding/OOD PoW nonce");
        println!("{name}: GPU proof accepted; {tampered} tampered PoW nonces rejected");
        checked += 1;
    }
    assert!(checked > 0, "no *{PROOF_SUFFIX} proofs in {dir}");
}
