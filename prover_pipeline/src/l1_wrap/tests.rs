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
    let mut checkpoint = artifact(ProofTarget::L1Feeder, 5);
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
        ("one RISC-V proof", |_| {}),
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
    };
    let Err(error) = advance_l1_wrap(&mut NoProving, &fsv, state, 0) else {
        panic!("an invalid feeder proof was wrapped");
    };
    assert!(error.contains("one RISC-V proof"), "{error}");
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
        (&fsv.feeder, ExecutionKind::L1Wrap, ProofProfile::L1Wrap),
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
