use prover::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::DefaultTreeConstructor;
use prover_pipeline::{ProofArtifact, ProofTarget, SoundnessMode};

#[test]
fn compression_final_fixture_equals_chain_terminal_proof() {
    let chain: ProofArtifact = proof_fixtures::read_file(proof_fixtures::chain_artifact(
        "pessimistic_conjecture",
        "compression",
    ));
    chain
        .validate_expected_mode(SoundnessMode::PessimisticConjecture)
        .unwrap();
    assert_eq!(chain.target, ProofTarget::Compression);
    let mut proofs = chain.proof.riscv_proofs.values().flatten();
    let terminal = proofs.next().expect("terminal compression circuit proof");
    assert!(proofs.next().is_none());
    let circuit: GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> =
        proof_fixtures::read_file(proof_fixtures::circuit_proof(
            "pessimistic_conjecture",
            "compression_final",
        ));
    assert_eq!(
        serde_json::to_value(circuit).unwrap(),
        serde_json::to_value(terminal).unwrap(),
        "regenerate the compression stage to refresh both committed copies"
    );
}
