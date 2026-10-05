use cpu_execution_prover::{CpuExecutionProver, CpuExecutionProverConfiguration};
use execution_prover::{CommitmentMode, ExecutionKind, MachineType, ProofProfile};
use full_statement_verifier::host_utils::{build_unified_stream, load_fsv_program};
use prover::definitions::SecurityLevel;
use prover::gkr::prover::{DefaultBabyBearBackend, DefaultBabyBearGKRBackend};
use prover::gkr::prover_config::example_configs::l1_feeder_config_for_2_23;
use prover_pipeline::{ProofArtifact, ProofTarget};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

#[test]
#[ignore = "F1 at L1Feeder twice over a recursion-unified artifact from L1_FEEDER_PARITY_ARTIFACT"]
fn f1_matches_the_legacy_feeder_transition() {
    let artifact_path = std::env::var("L1_FEEDER_PARITY_ARTIFACT")
        .expect("set L1_FEEDER_PARITY_ARTIFACT to a recursion-unified artifact");
    let artifact: ProofArtifact = prover_pipeline::deserialize_from_file(&artifact_path);
    assert_eq!(artifact.target, ProofTarget::RecursionUnified);

    let fsv_dir =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tools/gkr_verifier");
    let (bin, text) = load_fsv_program(
        &fsv_dir,
        FsvProgram::UnifiedRecursionLayer,
        BlakeMode::BlakeSpecialOpcodes,
    );
    let stream = build_unified_stream(&artifact.setups, &artifact.proof);

    let legacy_stream = {
        let worker = worker::Worker::new();
        let (proof, setups) =
            program_prover::unified_transition::prove_unified_transition_with_replayer(
                1 << 27,
                &bin,
                &text,
                true,
                QuasiUARTSource::new_with_reads(stream.clone()),
                1 << 30,
                &worker,
                SecurityLevel::Sec100,
                verifier_common::MEMORY_DELEGATION_POW_BITS as u32,
                &l1_feeder_config_for_2_23(),
                &DefaultBabyBearBackend::default(),
                &DefaultBabyBearGKRBackend::default(),
            );
        build_unified_stream(&setups, &proof)
    };

    let pipeline_stream = {
        let mut prover =
            CpuExecutionProver::with_configuration(CpuExecutionProverConfiguration::default());
        let handle = prover.add_binary(
            ExecutionKind::Unified,
            MachineType::Reduced,
            bin,
            text,
            None,
            &[ProofProfile::L1Feeder],
        );
        let result = prover.commit_memory_and_prove(
            1,
            &handle,
            QuasiUARTSource::new_with_reads(stream),
            CommitmentMode::MergedMemoryAndWitness,
            ProofProfile::L1Feeder,
        );
        let (proof, setups) = program_prover::assemble_program_proof(
            &prover.program_artifacts(&handle, ProofProfile::L1Feeder),
            result,
        );
        build_unified_stream(&setups, &proof)
    };

    assert_eq!(legacy_stream.len(), pipeline_stream.len());
    if let Some(word) = legacy_stream
        .iter()
        .zip(pipeline_stream.iter())
        .position(|(legacy, pipeline)| legacy != pipeline)
    {
        panic!(
            "F1 streams diverge at word {word} of {}",
            legacy_stream.len()
        );
    }
}
