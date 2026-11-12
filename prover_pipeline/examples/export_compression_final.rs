//! Export the final compression circuit proof in the canonical circuit fixture format.
use prover::gkr::prover_config::example_configs::compression_final_config_for_2_22;
use prover_pipeline::{ProofArtifact, ProofTarget, SoundnessMode};

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    assert_eq!(
        args.len(),
        2,
        "usage: export_compression_final CHAIN OUTPUT"
    );
    let artifact: ProofArtifact = proof_fixtures::read_file(&args[0]);
    artifact
        .validate_expected_mode(SoundnessMode::PessimisticConjecture)
        .expect("pessimistic compression artifact");
    assert_eq!(artifact.target, ProofTarget::Compression);
    assert!(artifact.proof.delegation_proofs.is_empty());
    assert!(artifact.proof.inits_and_teardown_proofs.is_empty());
    let mut proofs = artifact.proof.riscv_proofs.values().flatten();
    let proof = proofs.next().expect("terminal compression circuit proof");
    assert!(proofs.next().is_none(), "one terminal circuit proof");
    assert_eq!(
        proof.whir_proof.whir_schedule,
        compression_final_config_for_2_22().whir_schedule,
        "terminal proof must use the CompressionFinal profile"
    );
    proof_fixtures::write_file(&args[1], proof);
}
