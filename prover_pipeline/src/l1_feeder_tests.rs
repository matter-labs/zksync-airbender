use super::*;
use prover::definitions::{GKRExternalChallenges, SoundnessMode};
use prover::gkr::whir::{WhirBaseLayerCommitmentAndQueries, WhirPolyCommitProof};

pub(super) fn empty_gkr_proof<
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
            base_sumcheck_polys: vec![],
            base_folding_pow_nonces: vec![],
            base_queries_pow_nonce: 0,
            batching_challenge_pow_nonce: 0,
            final_monomials: vec![],
            whir_schedule: Default::default(),
        },
        grand_product_accumulator_computed: Default::default(),
        inits_and_teardowns_top_bits: vec![],
        lookup_challenges_pow_nonce: 0,
    }
}

fn compression_modes() -> PipelineBlakeModes {
    PipelineBlakeModes {
        unrolled: BlakeMode::Compression,
        bridge: BlakeMode::Compression,
        final_layer: BlakeMode::Compression,
    }
}

fn program() -> LoadedProgram {
    LoadedProgram {
        bin_bytes: vec![],
        text_bytes: vec![],
        bin_u32: vec![0x0000_0013],
        text_u32: vec![0x0000_0013],
    }
}

pub(super) fn empty_proof() -> ProgramProof {
    ProgramProof {
        riscv_proofs: BTreeMap::new(),
        compiled_riscv_circuits: BTreeMap::new(),
        inits_and_teardown_proofs: vec![],
        inits_and_teardowns_circuit: None,
        delegation_proofs: BTreeMap::new(),
        compiled_delegation_circuits: BTreeMap::new(),
        register_final_values: vec![],
        final_pc: 0,
        final_timestamp: prover::common_constants::INITIAL_TIMESTAMP,
        end_params: [0; 8],
        recursion_chain_hash: None,
        recursion_chain_preimage: None,
        pow_challenge: 0,
        num_it_circuits: None,
    }
}

fn modes_only(blake: PipelineBlakeModes) -> FsvPrograms {
    FsvPrograms::load(ProofTarget::Base, SoundnessMode::DEFAULT, blake)
}

pub(super) fn artifact(target: ProofTarget, n: usize) -> ProofArtifact {
    feeder_artifact(target, n)
}

/// A fake single-instance feeder proof: the reduced family with `instances`
/// instances, one inits-and-teardowns instance, no delegation proofs.
pub(super) fn fake_feeder_proof(final_pc: u32, instances: usize) -> ProgramProof {
    fake_feeder_proof_for_profile(final_pc, instances, FeederProfile::C)
}

pub(super) fn fake_feeder_proof_for_profile(
    final_pc: u32,
    instances: usize,
    profile: FeederProfile,
) -> ProgramProof {
    let family = profile.circuit().get_family_idx() as u32;
    let schedule = profile.config().whir_schedule;
    let mut proof = empty_proof();
    proof.final_pc = final_pc;
    proof.riscv_proofs.insert(
        family,
        (0..instances)
            .map(|_| {
                let mut instance = empty_gkr_proof();
                instance.whir_proof.whir_schedule = schedule.clone();
                instance
            })
            .collect(),
    );
    let layout = match profile {
        FeederProfile::A => serde_json::from_str(include_str!(
            "../../circuit_defs/unrolled_circuits/unified_reduced_machine/generated/layout.json"
        ))
        .unwrap(),
        FeederProfile::C => unified_reduced_machine_2_22_layout(),
    };
    proof.compiled_riscv_circuits.insert(family, layout);
    proof.num_it_circuits = Some(1);
    proof
}

/// The committed 2^22 unified layout, the compiled circuit a feeder proof
/// carries.
pub(super) fn unified_reduced_machine_2_22_layout(
) -> prover::cs::gkr_compiler::GKRCircuitArtifact<prover::field::baby_bear::base::BabyBearField> {
    serde_json::from_str(include_str!(
        "../../circuit_defs/unrolled_circuits/unified_reduced_machine_2_22/generated/layout.json"
    ))
    .unwrap()
}

pub(super) fn feeder_artifact(target: ProofTarget, n: usize) -> ProofArtifact {
    finalize_artifact(
        &modes_only(compression_modes()),
        &ProgramProverConfig {
            target,
            backend: ProverBackend::Cpu,
            ..Default::default()
        },
        0,
        &program(),
        RecursionState {
            stage: target,
            l1: None,
            proof: if target >= ProofTarget::L1Feeder {
                fake_feeder_proof(0, 1)
            } else {
                empty_proof()
            },
            setups: BTreeMap::new(),
            chain_end_params: (1..=n).map(|i| [i as u32; 8]).collect(),
            input_is_base: target == ProofTarget::Base,
            timings: ProofTimingsMs::default(),
            program_cycles: 0,
        },
    )
}

#[test]
fn continuation_keeps_historical_modes_when_current_modes_differ() {
    let mut checkpoint = artifact(ProofTarget::RecursionUnified, 3);
    checkpoint.blake_final = BlakeMode::BlakeSpecialOpcodes.tag().to_string();
    let blake = PipelineBlakeModes::continuing(&checkpoint, compression_modes).unwrap();
    assert_eq!(
        PipelineBlakeModes::continuing(&checkpoint, || panic!(
            "historical modes must not read the environment"
        ))
        .unwrap(),
        blake
    );
    assert_eq!(blake.final_layer, BlakeMode::BlakeSpecialOpcodes);
}

#[test]
fn feeder_artifacts_require_the_fixed_chain_tail() {
    assert_eq!(
        chain_unrolled_layers(&feeder_artifact(ProofTarget::L1Feeder, 7)).unwrap(),
        1
    );
    assert_eq!(
        chain_unrolled_layers(&feeder_artifact(ProofTarget::L1, 6)).unwrap(),
        0
    );
    assert!(chain_unrolled_layers(&feeder_artifact(ProofTarget::L1Feeder, 5)).is_err());
}

#[test]
fn terminal_c_rejects_profile_a_sized_setup_caps() {
    let family = FeederProfile::C.circuit().get_family_idx() as u32;
    let mut artifact = feeder_artifact(ProofTarget::L1Feeder, 6);
    let setup = |cap_size| setups::UnrolledCircuitSetupParams {
        family_idx: family,
        capacity: FeederProfile::C.circuit().get_domain_size() as u32,
        setup_caps: prover::merkle_trees::MerkleTreeCapVarLength {
            cap: vec![[7; 8]; cap_size],
        },
    };
    artifact
        .setups
        .insert(family, setup(FeederProfile::C.cap_size()));
    validate_artifact_envelope(&artifact).unwrap();
    artifact
        .setups
        .insert(family, setup(FeederProfile::A.cap_size()));
    assert!(validate_artifact_envelope(&artifact)
        .unwrap_err()
        .contains("leafs"));
}

// A regression reaching backend setup must return the missing-GPU-feature error,
// rather than allocate a GPU outside the CPU test harness.
#[cfg(not(feature = "gpu"))]
#[test]
fn continuation_constructor_rejects_request_and_source_before_backend_setup() {
    let missing = ProgramSource::elf("must-not-read-continuation-input.elf");
    assert!(matches!(&missing, ProgramSource::Elf(path) if !path.exists()));
    let source = ProgramSource::legacy_binaries_from_bin(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/hashed_fibonacci/app_plain.bin"),
    );
    let loaded = load_program(&source).unwrap();
    let config = ProgramProverConfig {
        target: ProofTarget::RecursionUnified,
        backend: ProverBackend::Gpu,
        ..Default::default()
    };
    let mut wrong_bin = artifact(ProofTarget::Base, 1);
    wrong_bin.program_bin_keccak = keccak256(&loaded.bin_bytes);
    wrong_bin.program_bin_keccak[0] ^= 1;
    let mut wrong_text = wrong_bin.clone();
    wrong_text.program_bin_keccak = keccak256(&loaded.bin_bytes);
    wrong_text.program_text_keccak = keccak256(&loaded.text_bytes);
    wrong_text.program_text_keccak[0] ^= 1;
    for (source, invalid, expected) in [
        (
            &missing,
            artifact(ProofTarget::RecursionUnified, 3),
            "already at target",
        ),
        (&source, wrong_bin, "program_bin_keccak"),
        (&source, wrong_text, "program_text_keccak"),
    ] {
        let error = ProgramProver::for_continuation(source.clone(), config.clone(), &invalid)
            .err()
            .expect("invalid continuation");
        assert!(error.contains(expected), "{error}");
    }
}

/// A feeder artifact is admitted against the trusted chain of the supplied
/// program before its continuation proves anything: a history that hashes
/// consistently but is not the program's chain is rejected.
#[test]
fn feeder_continuation_requires_the_trusted_chain() {
    let source = ProgramSource::legacy_binaries_from_bin(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/basic_fibonacci/app.bin"),
    );
    let mut artifact: ProofArtifact = proof_fixtures::read_file(proof_fixtures::chain_artifact(
        "pessimistic_conjecture",
        "l1_feeder",
    ));
    artifact.chain_end_params[0][0] ^= 1;
    let chain = rebuild_chain(&artifact.chain_end_params).unwrap();
    artifact.chain_hash = chain.hash();
    artifact.chain_preimage = chain.preimage();
    validate_continuation_request(&artifact, ProofTarget::L1).unwrap();
    let error = verify_artifact_in_mode(&artifact, &source, SoundnessMode::PessimisticConjecture)
        .unwrap_err();
    assert!(
        error.contains("do not match the trusted per-layer end-params"),
        "{error}"
    );
}

#[test]
fn feeder_proof_profile_requires_the_trace_and_every_instance_schedule() {
    for profile in FeederProfile::ALL {
        let proof = fake_feeder_proof_for_profile(0, 1, profile);
        validate_feeder_proof(&proof, profile, 1).unwrap();
    }
    let mut proof = fake_feeder_proof_for_profile(0, 2, FeederProfile::A);
    let family = UnrolledCircuitType::Unified.get_family_idx() as u32;
    proof.riscv_proofs.get_mut(&family).unwrap()[1]
        .whir_proof
        .whir_schedule = FeederProfile::C.config().whir_schedule;
    assert!(validate_feeder_proof(&proof, FeederProfile::A, 2)
        .unwrap_err()
        .contains("WHIR schedule"));
    let proof = fake_feeder_proof_for_profile(0, 2, FeederProfile::C);
    assert!(validate_feeder_proof(&proof, FeederProfile::C, 1)
        .unwrap_err()
        .contains("expected 1"));
    let proof = fake_feeder_proof_for_profile(0, 1, FeederProfile::A);
    assert!(validate_feeder_proof(&proof, FeederProfile::C, 1)
        .unwrap_err()
        .contains("trace length"));
}
