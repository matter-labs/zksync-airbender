use super::*;
use crate::l1_feeder_tests::{artifact, empty_gkr_proof, feeder_artifact};
use prover::definitions::FinalRegisterValue;

/// An empty proof with the GKR layer rounds and the WHIR counts of an
/// `L1_WRAP_KIND` proof.
fn wrap_proof_skeleton() -> L1Proof {
    use prover::gkr::prover::SumcheckIntermediateProofValues;
    use prover::gkr::whir::whir_proof::WhirIntermediateCommitmentAndQueries;

    let circuit = L1_WRAP_KIND.unified_circuit().unwrap();
    let log = circuit.get_domain_size_log2() as usize;
    let config = ProofProfile::L1Wrap.prover_config(log, COMPILED_SECURITY_LEVEL.to_prover());
    let (pack_log2, _) = l1_wrap_packing(circuit);
    let schedule = config.whir_schedule.clone();
    let folds: usize = schedule.whir_steps_schedule.iter().sum();
    let mut proof: L1Proof = empty_gkr_proof();
    let rounds = (0..5).map(|_| log).chain((4..log).rev());
    for (layer, sumcheck_num_rounds) in rounds.enumerate() {
        proof.sumcheck_intermediate_values.insert(
            layer,
            SumcheckIntermediateProofValues {
                sumcheck_num_rounds,
                internal_round_coefficients: vec![],
                final_step_evaluations: Default::default(),
                extra_evaluations_from_caching_relations: Default::default(),
                _marker: core::marker::PhantomData,
            },
        );
    }
    let whir = &mut proof.whir_proof;
    whir.pow_nonces = vec![0; schedule.whir_steps_schedule.len()];
    whir.sumcheck_polys = vec![Default::default(); folds];
    whir.final_monomials = vec![Default::default(); 1 << (log + pack_log2 - folds)];
    whir.intermediate_whir_oracles = schedule.whir_queries_schedule[1..]
        .iter()
        .map(|&queries| WhirIntermediateCommitmentAndQueries {
            commitment: Default::default(),
            queries: vec![Default::default(); queries],
        })
        .collect();
    whir.whir_schedule = schedule;
    proof
}

fn result() -> L1WrapResult {
    let (pack_log2, external_challenges_pow_bits) =
        l1_wrap_packing(L1_WRAP_KIND.unified_circuit().unwrap());
    L1WrapResult {
        proof: wrap_proof_skeleton(),
        commitment_mode: CommitmentMode::MergedAndPackedMemoryAndWitness {
            pack_log2,
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
fn malformed_l1_envelopes_fail_verify_and_continuation_before_loading_programs() {
    let mutations: &[(&str, fn(&mut ProofArtifact))] = &[
        ("schema_version", |a| a.schema_version += 1),
        ("l1 bundle", |a| a.l1 = None),
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

struct NoProving;

impl ProveBackend for NoProving {
    fn register(
        &mut self,
        _: ExecutionKind,
        _: MachineType,
        _: &[u32],
        _: &[u32],
        _: Option<u32>,
        _: &[ProofProfile],
    ) {
        panic!("the wrap stage must not register binaries");
    }
    fn prove(&mut self, _: ProveRequest<'_>) -> Result<(ProgramProof, Setups), String> {
        panic!("the wrap stage must not prove BabyBear layers");
    }
    fn prove_l1_wrap(&mut self, _: L1WrapRequest<'_>) -> Result<L1WrapResult, String> {
        panic!("an invalid feeder checkpoint must not be wrapped");
    }
    fn setups(
        &mut self,
        _: ExecutionKind,
        _: MachineType,
        _: &[u32],
        _: &[u32],
        _: ProofProfile,
    ) -> Option<Setups> {
        panic!("the wrap stage must not read setups");
    }
}

#[test]
fn wrap_rejects_an_invalid_feeder_proof_before_proving() {
    let fsv = FsvPrograms::load(ProofTarget::Base, PipelineBlakeModes::from_env());
    let checkpoint = artifact(ProofTarget::L1Feeder, 5);
    let state = RecursionState {
        stage: ProofTarget::L1Feeder,
        l1: None,
        proof: checkpoint.proof,
        setups: checkpoint.setups,
        chain_end_params: checkpoint.chain_end_params,
        input_is_base: false,
        timings: checkpoint.timings_ms,
        program_cycles: checkpoint.program_cycles,
        feeder_layers: checkpoint.feeder_layers,
    };
    let Err(error) = advance_l1_wrap(&mut NoProving, &fsv, state, 0) else {
        panic!("an invalid feeder checkpoint was wrapped");
    };
    assert!(error.contains("reduced-machine family"), "{error}");
}

#[test]
#[cfg(not(feature = "gpu"))]
fn gpu_l1_target_requires_gpu_feature() {
    let config = ProgramProverConfig {
        target: ProofTarget::L1,
        backend: ProverBackend::Gpu,
        ..Default::default()
    };
    assert!(
        matches!(ProgramProver::new(unused_source(), config), Err(error) if error == "CLI was compiled without `gpu` feature, but `--backend gpu` was requested")
    );
}

#[test]
fn cpu_m8_l1_registration_plan() {
    let loaded = LoadedProgram {
        bin_bytes: vec![],
        text_bytes: vec![],
        bin_u32: vec![0x13],
        text_u32: vec![0x13],
    };
    let fsv = FsvPrograms {
        unrolled_blake: BlakeMode::Compression,
        bridge_blake: BlakeMode::Compression,
        final_blake: BlakeMode::Compression,
        unrolled_base: (vec![], vec![]),
        unrolled_recursion: (vec![], vec![]),
        bridge_base: (vec![], vec![]),
        bridge_recursion: (vec![], vec![]),
        unified: (vec![], vec![]),
        feeder_first: (vec![0x13, 1], vec![1]),
        feeder: (vec![0x13, 2], vec![2]),
        feeder_wrap: (vec![0x13, 3], vec![3]),
    };
    let registrations = pipeline_registrations(
        &loaded,
        Some(ProofTarget::RecursionUnified),
        ProofTarget::L1,
        None,
        &fsv,
    );
    assert_eq!(registrations.len(), 3);
    for (program, kind, profile) in [
        (
            &fsv.feeder_first,
            ExecutionKind::Unified22,
            ProofProfile::L1Feeder,
        ),
        (
            &fsv.feeder,
            ExecutionKind::Unified22,
            ProofProfile::L1Feeder,
        ),
        (&fsv.feeder_wrap, L1_WRAP_KIND, ProofProfile::L1Wrap),
    ] {
        let key = handle_key(kind, MachineType::Reduced, &program.0, &program.1);
        let registration = &registrations[&key];
        assert_eq!(registration.kind, kind);
        assert_eq!(registration.machine, MachineType::Reduced);
        assert_eq!(registration.bin, program.0);
        assert_eq!(registration.text, program.1);
        assert_eq!(registration.cycles_bound, None);
        assert_eq!(registration.profiles, BTreeSet::from([profile]));
    }
}

#[test]
fn l1_activation_accepts_cpu_wrap21() {
    assert_eq!(L1_WRAP_KIND, ExecutionKind::L1Wrap21);
    validate_l1_wrap_activation().unwrap();
    validate_l1_wrap_backend(ProverBackend::Cpu).unwrap();
    validate_artifact_envelope(&wrapped_artifact()).unwrap();
}

#[test]
fn l1_activation_rejects_gpu_before_registration() {
    let err = validate_l1_wrap_backend(ProverBackend::Gpu).unwrap_err();
    assert!(
        err.contains("ExecutionKind::L1Wrap21") && err.contains("W5"),
        "{err}"
    );
}

#[test]
fn l1_bundle_requires_wrap_version() {
    let bundle = L1Bundle::from_result(result());
    let mut json = serde_json::to_value(&bundle).unwrap();
    assert_eq!(json["wrap"], "2p21");
    json.as_object_mut().unwrap().remove("wrap");
    let err = serde_json::from_value::<L1Bundle>(json).unwrap_err();
    assert!(err.to_string().contains("missing field `wrap`"), "{err}");
}

#[test]
fn l1_bundle_rejects_2p22_version() {
    let mut bundle = L1Bundle::from_result(result());
    bundle.wrap = L1WrapVersion::Wrap2p22;
    let err = bundle.validate().unwrap_err();
    assert!(err.contains("proven in the Wrap2p22 wrap"), "{err}");
}

#[test]
fn l1_bundle_rejects_truncated_whir_round() {
    let mutations: &[(&str, fn(&mut L1Proof))] = &[
        ("WHIR intermediate oracles", |p| {
            p.whir_proof.intermediate_whir_oracles.pop();
        }),
        ("WHIR round 3 queries", |p| {
            p.whir_proof.intermediate_whir_oracles[2].queries.pop();
        }),
        ("WHIR final monomials", |p| {
            p.whir_proof.final_monomials.pop();
        }),
        ("WHIR PoW nonces", |p| {
            p.whir_proof.pow_nonces.pop();
        }),
        ("WHIR schedule", |p| {
            p.whir_proof.whir_schedule.whir_pow_schedule[2] -= 1;
        }),
        ("sumcheck rounds in GKR layer 5", |p| {
            p.sumcheck_intermediate_values
                .get_mut(&5)
                .unwrap()
                .sumcheck_num_rounds -= 1;
        }),
        ("GKR layers", |p| {
            p.sumcheck_intermediate_values.pop_last();
        }),
    ];
    L1Bundle::from_result(result()).validate().unwrap();
    for (expected, mutate) in mutations {
        let mut bundle = L1Bundle::from_result(result());
        mutate(&mut bundle.proof);
        let err = bundle.validate().unwrap_err();
        assert!(err.contains(expected), "{expected}: {err}");
    }
}
