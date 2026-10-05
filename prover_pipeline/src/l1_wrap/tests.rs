use super::*;
use crate::l1_feeder_tests::artifact;
use prover::definitions::{FinalRegisterValue, GKRExternalChallenges};
use prover::gkr::whir::{WhirBaseLayerCommitmentAndQueries, WhirPolyCommitProof};

fn empty_gkr_proof<
    F: prover::field::PrimeField,
    E: prover::field::FieldExtension<F> + prover::field::Field,
    T: prover::merkle_trees::ColumnMajorMerkleTreeConstructor<F>,
>() -> prover::gkr::prover::GKRProof<F, E, T> {
    let empty_commitment = || WhirBaseLayerCommitmentAndQueries {
        commitment: Default::default(),
        num_columns: 0,
        evals: vec![],
        queries: vec![],
    };
    prover::gkr::prover::GKRProof {
        external_challenges: GKRExternalChallenges::default(),
        final_explicit_evaluations: Default::default(),
        sumcheck_intermediate_values: Default::default(),
        whir_proof: WhirPolyCommitProof {
            setup_commitment: empty_commitment(),
            memory_commitment: empty_commitment(),
            witness_commitment: empty_commitment(),
            intermediate_whir_oracles: vec![],
            ood_samples: vec![],
            sumcheck_polys: vec![],
            pow_nonces: vec![],
            final_monomials: vec![],
            whir_schedule: Default::default(),
            batching_challenge: None,
            original_evaluation_point: None,
            batched_opening: None,
        },
        grand_product_accumulator_computed: Default::default(),
        inits_and_teardowns_top_bits: vec![],
        lookup_challenges_pow_nonce: 0,
        batched_proximity_check_pow_nonce: 0,
        intermediate_transcript_seed: None,
    }
}

fn result() -> L1WrapResult {
    L1WrapResult {
        proof: empty_gkr_proof(),
        commitment_mode: CommitmentMode::MergedAndPackedMemoryAndWitness {
            pack_log2: EVM_PRODUCTION_PACK_LOG2,
            external_challenges_pow_bits: EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
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
    let mut checkpoint = artifact(ProofTarget::L1Feeder, 5, Some(1));
    checkpoint.target = ProofTarget::L1;
    checkpoint.l1 = Some(L1Bundle::from_result(result()).unwrap());
    checkpoint
}

fn unused_source() -> ProgramSource {
    ProgramSource::from_paths("must-not-read.bin".into(), None)
}

#[test]
fn remaining_stage_calls_include_exactly_one_wrap() {
    use ProofTarget::{Base, L1Feeder, RecursionUnified, RecursionUnrolled, L1};
    for (current, target, expected) in [
        (Base, Base, vec![]),
        (Base, RecursionUnrolled, vec![RecursionUnrolled]),
        (Base, RecursionUnified, vec![RecursionUnified]),
        (Base, L1Feeder, vec![RecursionUnified, L1Feeder]),
        (Base, L1, vec![RecursionUnified, L1Feeder, L1]),
        (RecursionUnrolled, RecursionUnified, vec![RecursionUnified]),
        (
            RecursionUnrolled,
            L1Feeder,
            vec![RecursionUnified, L1Feeder],
        ),
        (RecursionUnrolled, L1, vec![RecursionUnified, L1Feeder, L1]),
        (RecursionUnified, L1Feeder, vec![L1Feeder]),
        (RecursionUnified, L1, vec![L1Feeder, L1]),
        (L1Feeder, L1, vec![L1]),
    ] {
        let mut calls = vec![];
        advance_stages((), current, target, |(), next| {
            calls.push(next);
            Ok(())
        })
        .unwrap();
        assert_eq!(calls, expected, "{current:?} -> {target:?}");
    }
}

#[test]
fn schema_version_must_match_exactly() {
    for version in [3, 4, 5, 6] {
        for (target, layers, rounds) in [
            (ProofTarget::Base, 1, None),
            (ProofTarget::RecursionUnrolled, 2, None),
            (ProofTarget::RecursionUnified, 3, None),
            (ProofTarget::L1Feeder, 5, Some(1)),
            (ProofTarget::L1, 5, Some(1)),
        ] {
            let mut checkpoint = if target == ProofTarget::L1 {
                wrapped_artifact()
            } else {
                artifact(target, layers, rounds)
            };
            checkpoint.schema_version = version;
            let expected = version == ARTIFACT_SCHEMA_VERSION;
            assert_eq!(
                validate_artifact_envelope(&checkpoint).is_ok(),
                expected,
                "v{version} {target:?}"
            );
        }
    }
}

#[test]
fn l1_round_trip_preserves_the_feeder_payload_and_chain() {
    let feeder = artifact(ProofTarget::L1Feeder, 5, Some(1));
    let wrapped = wrapped_artifact();
    let json = serde_json::to_value(&wrapped).unwrap();
    assert_eq!(json["schema_version"], ARTIFACT_SCHEMA_VERSION);
    assert_eq!(json["l1"]["profile_tag"], L1_PROFILE_TAG);
    let feeder_json = serde_json::to_value(feeder).unwrap();
    for field in [
        "proof",
        "setups",
        "proof_counts",
        "cycles",
        "chain_hash",
        "chain_preimage",
        "chain_end_params",
    ] {
        assert_eq!(json[field], feeder_json[field], "{field}");
    }
    let decoded: ProofArtifact = serde_json::from_value(json).unwrap();
    validate_artifact_envelope(&decoded).unwrap();
    validate_artifact_chain(&decoded).unwrap();
    assert_eq!(chain_unrolled_layers(&decoded).unwrap(), 0);

    let mut minimal = serde_json::to_value(artifact(ProofTarget::Base, 1, None)).unwrap();
    assert!(minimal
        .as_object_mut()
        .unwrap()
        .remove("l1")
        .unwrap()
        .is_null());
    assert!(minimal["timings_ms"]
        .as_object_mut()
        .unwrap()
        .remove("l1_wrap_ms")
        .unwrap()
        .is_null());
    let decoded: ProofArtifact = serde_json::from_value(minimal).unwrap();
    assert!(decoded.l1.is_none());
    validate_continuation_request(&decoded, ProofTarget::L1).unwrap();
}

#[test]
fn malformed_l1_envelopes_fail_verify_and_continuation_before_loading_programs() {
    let mutations: &[(&str, fn(&mut ProofArtifact))] = &[
        ("schema_version", |a| a.schema_version = 2),
        ("l1 bundle", |a| a.l1 = None),
        ("profile_tag", |a| {
            a.l1.as_mut().unwrap().profile_tag = "standard".into()
        }),
        ("layout_keccak", |a| {
            a.l1.as_mut().unwrap().layout_keccak[0] ^= 1
        }),
        ("production packing", |a| {
            a.l1.as_mut().unwrap().commitment_mode = CommitmentMode::MergedMemoryAndWitness
        }),
        ("production packing", |a| {
            if let CommitmentMode::MergedAndPackedMemoryAndWitness { pack_log2, .. } =
                &mut a.l1.as_mut().unwrap().commitment_mode
            {
                *pack_log2 += 1;
            }
        }),
        ("production packing", |a| {
            if let CommitmentMode::MergedAndPackedMemoryAndWitness {
                external_challenges_pow_bits,
                ..
            } = &mut a.l1.as_mut().unwrap().commitment_mode
            {
                *external_challenges_pow_bits -= 1;
            }
        }),
        ("l1_feeder_rounds", |a| a.l1_feeder_rounds = None),
        ("verifier cycles", |a| a.l1_feeder_verifier_cycles = None),
        ("non-L1", |a| a.target = ProofTarget::L1Feeder),
    ];
    for (expected, mutate) in mutations {
        let mut checkpoint = wrapped_artifact();
        mutate(&mut checkpoint);
        assert!(verify_feeder_sidecar(&checkpoint, &unused_source())
            .unwrap_err()
            .contains(expected));
        assert!(validate_continuation_request(&checkpoint, ProofTarget::L1)
            .unwrap_err()
            .contains(expected));
    }
    let mut missing_proof = serde_json::to_value(wrapped_artifact()).unwrap();
    missing_proof["l1"].as_object_mut().unwrap().remove("proof");
    assert!(serde_json::from_value::<ProofArtifact>(missing_proof).is_err());
}

#[test]
fn l1_verify_requires_opt_in_and_rejects_an_empty_sidecar() {
    let checkpoint = wrapped_artifact();
    assert!(verify_artifact(&checkpoint, &unused_source())
        .unwrap_err()
        .contains("L1 Proth proof verification is not implemented"));
    assert!(verify_feeder_sidecar(&checkpoint, &unused_source())
        .unwrap_err()
        .contains("L1Feeder sidecar must contain one RISC-V proof"));
}

#[test]
fn envelope_validation_does_not_authenticate_proth_proof_values() {
    let mut checkpoint = wrapped_artifact();
    checkpoint
        .l1
        .as_mut()
        .unwrap()
        .proof
        .lookup_challenges_pow_nonce ^= 1;
    validate_artifact_envelope(&checkpoint).unwrap();
}

#[derive(Default)]
struct WrapBackend {
    calls: Vec<(u64, Vec<u32>)>,
}

impl ProveBackend for WrapBackend {
    fn register(
        &mut self,
        _: ExecutionKind,
        _: MachineType,
        _: &[u32],
        _: &[u32],
        _: Option<u32>,
        _: &[ProofProfile],
    ) {
        panic!("wrap stage must use pre-registered binaries");
    }
    fn prove(&mut self, _: ProveRequest<'_>) -> Result<(ProgramProof, Setups), String> {
        panic!("wrap stage must use the typed Proth operation");
    }
    fn prove_l1_wrap(&mut self, request: L1WrapRequest<'_>) -> Result<L1WrapResult, String> {
        self.calls.push((request.batch_id, request.nd_words));
        Ok(result())
    }
    fn setups(
        &mut self,
        _: ExecutionKind,
        _: MachineType,
        _: &[u32],
        _: &[u32],
        _: ProofProfile,
    ) -> Option<Setups> {
        panic!("wrap stage must not read setups");
    }
}

fn request() -> L1WrapRequest<'static> {
    L1WrapRequest {
        batch_id: 7,
        bin: &[1, 2],
        text: &[1],
        nd_words: vec![42, 43],
    }
}

#[test]
fn wrap_remeasures_the_stream_and_submits_the_same_input() {
    let mut backend = WrapBackend::default();
    let measured = std::cell::Cell::new(false);
    let (_, cycles) = measure_then_wrap(&mut backend, request(), |bin, text, nd, bound| {
        assert_eq!(bin, [1, 2]);
        assert_eq!(text, [1]);
        assert_eq!(nd, [42, 43]);
        assert_eq!(bound, 1 << 22);
        measured.set(true);
        Ok(bound as u64)
    })
    .unwrap();
    assert!(measured.get());
    assert_eq!(cycles, L1_WRAP_CYCLES_BOUND as u64);
    assert_eq!(backend.calls, [(7, vec![42, 43])]);
}

#[test]
fn failed_or_oversized_remeasurement_never_submits_a_wrap() {
    for measurement in [
        Err("did not reach success exit".into()),
        Ok(0),
        Ok(L1_WRAP_CYCLES_BOUND as u64 + 1),
    ] {
        let mut backend = WrapBackend::default();
        let error =
            measure_then_wrap(&mut backend, request(), |_, _, _, _| measurement).unwrap_err();
        assert!(error.contains("L1Wrap feeder"));
        assert!(backend.calls.is_empty());
    }
}

#[test]
fn gpu_l1_target_fails_before_backend_initialization() {
    let config = ProgramProverConfig {
        target: ProofTarget::L1,
        backend: ProverBackend::Gpu,
        ..Default::default()
    };
    assert!(
        matches!(ProgramProver::new(unused_source(), config), Err(error) if error == "GPU backend does not support L1Wrap")
    );
}

#[test]
fn wrap_replaces_stale_telemetry_and_keeps_the_feeder_statement() {
    let mut checkpoint = artifact(ProofTarget::L1Feeder, 5, Some(1));
    checkpoint
        .proof
        .riscv_proofs
        .insert(128, vec![empty_gkr_proof()]);
    let expected_proof = serde_json::to_value(&checkpoint.proof).unwrap();
    let expected_setups = serde_json::to_value(&checkpoint.setups).unwrap();
    let expected_chain = checkpoint.chain_end_params.clone();
    let state = RecursionState {
        stage: ProofTarget::L1Feeder,
        l1_feeder_rounds: checkpoint.l1_feeder_rounds,
        l1_feeder_verifier_cycles: Some(1),
        l1: None,
        proof: checkpoint.proof,
        setups: checkpoint.setups,
        chain_end_params: checkpoint.chain_end_params,
        input_is_base: false,
        timings: checkpoint.timings_ms,
        program_cycles: checkpoint.program_cycles,
    };
    let mut backend = WrapBackend::default();
    let wrapped = wrap_feeder_checkpoint(state, |before| {
        assert_eq!(before.l1_feeder_verifier_cycles, Some(1));
        measure_then_wrap(&mut backend, request(), |_, _, _, bound| Ok(bound as u64))
    })
    .unwrap();
    assert_eq!(wrapped.stage, ProofTarget::L1);
    assert_eq!(
        wrapped.l1_feeder_verifier_cycles,
        Some(L1_WRAP_CYCLES_BOUND as u64)
    );
    assert_eq!(wrapped.l1_feeder_rounds, Some(1));
    assert_eq!(wrapped.chain_end_params, expected_chain);
    assert_eq!(
        serde_json::to_value(&wrapped.proof).unwrap(),
        expected_proof
    );
    assert_eq!(
        serde_json::to_value(&wrapped.setups).unwrap(),
        expected_setups
    );
    assert!(wrapped.l1.is_some());
    assert!(wrapped.timings.l1_wrap_ms.is_some());
    assert_eq!(backend.calls, [(7, vec![42, 43])]);
}
