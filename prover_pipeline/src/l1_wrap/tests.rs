use super::*;
use crate::l1_feeder_tests::{empty_gkr_proof, feeder_artifact};
use prover::definitions::FinalRegisterValue;

fn result() -> L1WrapResult {
    let external_challenges_pow_bits =
        L1WrapVersion::of_kind(L1_WRAP_KIND).external_challenges_pow_bits();
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
    let mut checkpoint = feeder_artifact(ProofTarget::L1Feeder, 5, 2);
    checkpoint.target = ProofTarget::L1;
    checkpoint.l1 = Some(L1Bundle::from_result(result()));
    checkpoint
}

fn unused_source() -> ProgramSource {
    ProgramSource::elf("must-not-read.elf")
}

#[test]
fn remaining_stage_calls_include_exactly_one_wrap() {
    use ProofTarget::{Base, L1Feeder, RecursionUnified, L1};
    for (current, target, expected) in [
        (Base, L1, vec![RecursionUnified, L1Feeder, L1]),
        (RecursionUnified, L1Feeder, vec![L1Feeder]),
        (RecursionUnified, L1, vec![L1Feeder, L1]),
        (L1Feeder, L1, vec![L1]),
    ] {
        let mut calls = vec![];
        advance_stages((), current, target, |(), next| {
            calls.push(next);
            Ok::<_, String>(())
        })
        .unwrap();
        assert_eq!(calls, expected, "{current:?} -> {target:?}");
    }
}

#[test]
fn malformed_l1_envelopes_fail_verify_and_continuation_before_loading_programs() {
    validate_artifact_envelope(&wrapped_artifact()).unwrap();
    let mutations: &[(&str, fn(&mut ProofArtifact))] = &[
        ("UnsupportedArtifactVersion", |a| a.schema_version += 1),
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
        ("non-L1", |a| a.target = ProofTarget::L1Feeder),
        ("reduced-machine family", |a| {
            a.proof = crate::l1_feeder_tests::empty_proof()
        }),
    ];
    for (expected, mutate) in mutations {
        let mut checkpoint = wrapped_artifact();
        mutate(&mut checkpoint);
        assert!(verify_artifact(&checkpoint, &unused_source())
            .unwrap_err()
            .contains(expected));
        assert!(validate_continuation_request(&checkpoint, ProofTarget::L1)
            .unwrap_err()
            .contains(expected));
    }
}

#[test]
fn l1_bundle_rejects_unknown_wrap_version() {
    let mut json = serde_json::to_value(L1Bundle::from_result(result())).unwrap();
    json["wrap"] = "unknown_wrap".into();
    let err = serde_json::from_value::<L1Bundle>(json).unwrap_err();
    assert!(
        err.to_string().contains("unknown variant `unknown_wrap`"),
        "{err}"
    );
}

#[test]
fn wrap_circuit_matches_the_guest_geometry() {
    let circuit = L1_WRAP_KIND.unified_circuit().unwrap();
    assert_eq!(circuit.get_domain_size(), L1_WRAP_PROGRAM_CYCLE_LIMIT);
    assert_eq!(
        circuit.rom(),
        verifier_common::fsv_binaries::FsvProfile::L1FeederWrap.rom()
    );
}
