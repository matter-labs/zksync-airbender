use super::*;
use crate::compression_tests::{compression_artifact, empty_gkr_proof};
use prover::definitions::FinalRegisterValue;

fn result() -> L1WrapResult {
    let external_challenges_pow_bits =
        prover::gkr::prover_config::example_configs::l1_wrap::EXTERNAL_CHALLENGES_POW_BITS;
    L1WrapResult {
        proof: empty_gkr_proof(),
        operation_mode: OperationMode::SingleChunk {
            external_challenges_pow_bits,
            register_final_state: [FinalRegisterValue {
                value: 0,
                last_access_timestamp: 0,
            }; 32],
            final_pc: 4,
            final_timestamp: 16,
        },
    }
}

fn wrapped_artifact() -> ProofArtifact {
    let mut checkpoint = compression_artifact(ProofTarget::Compression, 6);
    checkpoint.target = ProofTarget::L1;
    checkpoint.l1 = Some(L1Bundle::from_result(result()));
    checkpoint
}

fn unused_source() -> ProgramSource {
    ProgramSource::elf("must-not-read.elf")
}

#[test]
fn malformed_l1_envelopes_fail_verify_and_continuation_before_loading_programs() {
    validate_artifact_envelope(&wrapped_artifact()).unwrap();
    let mutations: &[(&str, fn(&mut ProofArtifact))] = &[
        ("l1 bundle", |a| a.l1 = None),
        ("production single-chunk operation", |a| {
            a.l1.as_mut().unwrap().operation_mode = OperationMode::MultipleChunks
        }),
        ("production single-chunk operation", |a| {
            if let OperationMode::SingleChunk {
                external_challenges_pow_bits,
                ..
            } = &mut a.l1.as_mut().unwrap().operation_mode
            {
                *external_challenges_pow_bits -= 1;
            }
        }),
        ("non-L1", |a| a.target = ProofTarget::Compression),
        ("reduced-machine family", |a| {
            a.proof = crate::compression_tests::empty_proof()
        }),
    ];
    for (expected, mutate) in mutations {
        let mut checkpoint = wrapped_artifact();
        mutate(&mut checkpoint);
        assert!(verify_artifact_in_mode(
            &checkpoint,
            &unused_source(),
            SoundnessMode::PessimisticConjecture
        )
        .unwrap_err()
        .contains(expected));
        // A continuation accepts the artifact's mode before its request checks.
        assert!(checkpoint
            .validate_expected_mode(SoundnessMode::PessimisticConjecture)
            .and_then(|()| validate_continuation_request(&checkpoint, ProofTarget::L1))
            .unwrap_err()
            .contains(expected));
        // The session's own verify checks the same envelope before it reads its source or
        // reaches a backend (the test backend is unused).
        let mut session = ProgramProver {
            source: unused_source(),
            config: ProgramProverConfig {
                target: checkpoint.target,
                ..Default::default()
            },
            backend: BackendImpl::Cpu(PipelineBackend::new(&ProgramProverConfig {
                worker_threads: Some(1),
                ..Default::default()
            })),
            fsv: FsvPrograms::load(
                ProofTarget::Base,
                prover::definitions::SoundnessMode::DEFAULT,
            ),
        };
        let error = session.verify(&checkpoint).unwrap_err();
        assert!(error.contains(expected), "{expected}: {error}");
    }
}

#[test]
fn l1_activation_rejects_gpu_before_registration() {
    for target in [ProofTarget::L1, ProofTarget::Compression] {
        let error = ProgramProver::new(
            unused_source(),
            ProgramProverConfig {
                target,
                backend: ProverBackend::Gpu,
                ..Default::default()
            },
        )
        .err()
        .expect(
            "GPU L1 targets must be rejected before reading the source or registering binaries",
        );
        assert_eq!(
            error,
            format!("ProofTarget::{target:?} is not supported by the GPU backend")
        );
    }
}
