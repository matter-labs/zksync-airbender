use cpu_execution_prover::{CpuExecutionProver, CpuExecutionProverConfiguration};
use execution_prover::{CommitmentMode, ExecutionKind, L1Proof, MachineType, ProofProfile};
use full_statement_verifier::host_utils::{build_unified_stream, load_fsv_program};
use prover_pipeline::{ProofArtifact, ProofTarget};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

#[test]
#[ignore = "CPU L1 wrap over L1_FEEDER_ARTIFACT, compared with the legacy fixture in L1_WRAP_LEGACY_DIR"]
fn l1_wrap_matches_the_legacy_wrap() {
    let artifact: ProofArtifact = prover_pipeline::deserialize_from_file(
        &std::env::var("L1_FEEDER_ARTIFACT").expect("set L1_FEEDER_ARTIFACT"),
    );
    assert_eq!(artifact.target, ProofTarget::L1Feeder);
    let legacy_dir = std::path::PathBuf::from(
        std::env::var("L1_WRAP_LEGACY_DIR").expect("set L1_WRAP_LEGACY_DIR"),
    );
    let fsv_dir =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tools/gkr_verifier");
    let (bin, text) = load_fsv_program(
        &fsv_dir,
        FsvProgram::UnifiedRecursionLayerL1Feeder,
        BlakeMode::BlakeSpecialOpcodes,
    );

    let mut prover =
        CpuExecutionProver::with_configuration(CpuExecutionProverConfiguration::default());
    let handle = prover.add_binary(
        ExecutionKind::L1Wrap,
        MachineType::Reduced,
        bin,
        text,
        None,
        &[ProofProfile::L1Wrap],
    );
    let result = prover.prove_l1_wrap(
        1,
        &handle,
        QuasiUARTSource::new_with_reads(build_unified_stream(&artifact.setups, &artifact.proof)),
    );

    let legacy_proof: L1Proof = prover_pipeline::deserialize_from_file(
        legacy_dir
            .join("unified_circuit_proof_proth120.json")
            .to_str()
            .unwrap(),
    );
    let legacy_mode: CommitmentMode = prover_pipeline::deserialize_from_file(
        legacy_dir
            .join("unified_circuit_proof_proth120_commitment_mod_aux_data.json")
            .to_str()
            .unwrap(),
    );
    if let Ok(out) = std::env::var("L1_WRAP_OUT_DIR") {
        let out = std::path::PathBuf::from(out);
        prover_pipeline::serialize_to_file(&result.proof, &out.join("l1_proof.json"));
        prover_pipeline::serialize_to_file(
            &result.commitment_mode,
            &out.join("l1_commitment_mode.json"),
        );
    }
    assert!(
        serde_json::to_string(&result.commitment_mode).unwrap()
            == serde_json::to_string(&legacy_mode).unwrap(),
        "commitment mode differs from the legacy wrap"
    );
    assert!(
        serde_json::to_string(&result.proof).unwrap()
            == serde_json::to_string(&legacy_proof).unwrap(),
        "L1 proof differs from the legacy wrap"
    );
}
