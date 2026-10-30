//! Gates using unchanged, real v3 artifacts and the private measured ethproofs base proof.
//! The ignored gates require externally produced files; no synthetic proof substitutes.

use full_statement_verifier::host_utils::{
    build_unified_stream, build_unrolled_stream, compute_end_params,
    try_native_verify_unified_in_mode, try_native_verify_unrolled_in_mode, FsvRecursionChain,
};
use prover_pipeline::{
    verify_artifact_in_mode, ProgramSource, ProofArtifact, ProofTarget, SoundnessMode,
};
use std::path::{Path, PathBuf};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

fn v3_artifact(name: &str) -> ProofArtifact {
    let dir = std::env::var_os("TASK_S_V3_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| root().join("target/soundness-mode/v3-compat-inputs"));
    serde_json::from_reader(std::io::BufReader::new(
        std::fs::File::open(dir.join(name)).unwrap(),
    ))
    .unwrap()
}

fn source() -> ProgramSource {
    ProgramSource::legacy_binaries_from_bin(root().join("examples/basic_fibonacci/app.bin"))
}

#[test]
#[ignore = "requires preserved real v3 CPU CLI base and unified artifacts"]
fn real_v3_artifacts_verify_and_reject_ethproofs_labels() {
    for name in ["base.json", "recursion_unified.json"] {
        let mut artifact = v3_artifact(name);
        assert_eq!(artifact.schema_version, 3);
        assert_eq!(
            artifact.soundness_mode,
            SoundnessMode::PessimisticConjecture
        );
        verify_artifact_in_mode(&artifact, &source(), SoundnessMode::PessimisticConjecture)
            .unwrap();
        let error =
            verify_artifact_in_mode(&artifact, &source(), SoundnessMode::EthproofsSoundnessCalc)
                .unwrap_err();
        assert!(error.contains("SoundnessModeMismatch"), "{error}");
        // Check actual wrong-mode verification too, independently of the metadata gate.
        let rejected = if artifact.target == ProofTarget::Base {
            try_native_verify_unrolled_in_mode(
                build_unrolled_stream(
                    &artifact.setups,
                    &artifact.proof,
                    verifier_common::BLAKE_MODE,
                ),
                true,
                SoundnessMode::EthproofsSoundnessCalc,
            )
        } else {
            try_native_verify_unified_in_mode(
                build_unified_stream(
                    &artifact.setups,
                    &artifact.proof,
                    verifier_common::BLAKE_MODE,
                ),
                false,
                SoundnessMode::EthproofsSoundnessCalc,
            )
        };
        assert!(
            rejected.is_err(),
            "{name} accepted under the wrong native verifier"
        );
        artifact.schema_version = 4;
        artifact.soundness_mode = SoundnessMode::EthproofsSoundnessCalc;
        assert!(
            verify_artifact_in_mode(&artifact, &source(), SoundnessMode::EthproofsSoundnessCalc)
                .is_err(),
            "{name} label flip accepted"
        );
    }
}

#[test]
#[ignore = "requires the versioned private ethproofs CPU base measurement checkpoint"]
fn measured_ethproofs_base_rejects_a_pessimistic_label() {
    let path = std::env::var_os("TASK_S_ETH_BASE")
        .map(PathBuf::from)
        .unwrap_or_else(|| root().join("target/soundness-mode/ethproofs-base-recovered-v1.json"));
    let bundle = program_prover::bundle::read_program_proof_bundle(
        &path,
        SoundnessMode::EthproofsSoundnessCalc,
    )
    .unwrap();
    assert_eq!(bundle.schema_version, 1);
    let mode = bundle.soundness_mode;
    let (proof, setups) = bundle.into_parts();
    let stream = build_unrolled_stream(&setups, &proof, verifier_common::BLAKE_MODE);
    try_native_verify_unrolled_in_mode(stream.clone(), true, mode).unwrap();
    assert!(
        try_native_verify_unrolled_in_mode(stream, true, SoundnessMode::PessimisticConjecture)
            .is_err()
    );

    // Build the public v4 envelope around the actual measured payload; metadata is not trusted.
    let mut artifact = v3_artifact("base.json");
    artifact.schema_version = 4;
    artifact.soundness_mode = mode;
    artifact.proof = proof;
    artifact.setups = setups;
    let end = compute_end_params(&artifact.setups, artifact.proof.final_pc);
    let chain = FsvRecursionChain::begin(&end);
    artifact.chain_end_params = vec![end];
    artifact.chain_hash = chain.hash();
    artifact.chain_preimage = chain.preimage();
    verify_artifact_in_mode(&artifact, &source(), mode).unwrap();
    artifact.soundness_mode = SoundnessMode::PessimisticConjecture;
    let error = verify_artifact_in_mode(&artifact, &source(), SoundnessMode::PessimisticConjecture)
        .unwrap_err();
    assert!(error.contains("NativeVerificationFailed"), "{error}");
}
