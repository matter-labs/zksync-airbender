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

/// A fake single-instance compression proof: the reduced family with `instances`
/// instances, one inits-and-teardowns instance, no delegation proofs.
pub(super) fn fake_compression_proof(final_pc: u32, instances: usize) -> ProgramProof {
    fake_compression_proof_for_profile(final_pc, instances, CompressionProfile::Final)
}

pub(super) fn fake_compression_proof_for_profile(
    final_pc: u32,
    instances: usize,
    profile: CompressionProfile,
) -> ProgramProof {
    fake_compression_proof_in_mode(
        final_pc,
        instances,
        profile,
        SoundnessMode::PessimisticConjecture,
    )
}

fn fake_compression_proof_in_mode(
    final_pc: u32,
    instances: usize,
    profile: CompressionProfile,
    mode: SoundnessMode,
) -> ProgramProof {
    let family = profile.circuit().get_family_idx() as u32;
    let schedule = profile.config(mode).whir_schedule;
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
        CompressionProfile::Step => serde_json::from_str(include_str!(
            "../../circuit_defs/unrolled_circuits/unified_reduced_machine/generated/layout.json"
        ))
        .unwrap(),
        CompressionProfile::Final => unified_reduced_machine_2_22_layout(),
    };
    proof.compiled_riscv_circuits.insert(family, layout);
    proof.num_it_circuits = Some(1);
    proof
}

/// The committed 2^22 unified layout, the compiled circuit a compression proof
/// carries.
pub(super) fn unified_reduced_machine_2_22_layout(
) -> prover::cs::gkr_compiler::GKRCircuitArtifact<prover::field::baby_bear::base::BabyBearField> {
    serde_json::from_str(include_str!(
        "../../circuit_defs/unrolled_circuits/unified_reduced_machine_2_22/generated/layout.json"
    ))
    .unwrap()
}

pub(super) fn compression_artifact(target: ProofTarget, n: usize) -> ProofArtifact {
    finalize_artifact(
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
            proof: if target >= ProofTarget::Compression {
                fake_compression_proof(0, 1)
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
fn compression_artifacts_require_the_fixed_chain_tail() {
    assert_eq!(
        chain_unrolled_layers(&compression_artifact(ProofTarget::Compression, 7)).unwrap(),
        1
    );
    assert_eq!(
        chain_unrolled_layers(&compression_artifact(ProofTarget::L1, 6)).unwrap(),
        0
    );
    assert!(chain_unrolled_layers(&compression_artifact(ProofTarget::Compression, 5)).is_err());
}

#[test]
fn compression_final_rejects_compression_sized_setup_caps() {
    let family = CompressionProfile::Final.circuit().get_family_idx() as u32;
    let mut artifact = compression_artifact(ProofTarget::Compression, 6);
    let setup = |cap_size| setups::UnrolledCircuitSetupParams {
        family_idx: family,
        capacity: CompressionProfile::Final.circuit().get_domain_size() as u32,
        setup_caps: prover::merkle_trees::MerkleTreeCapVarLength {
            cap: vec![[7; 8]; cap_size],
        },
    };
    artifact.setups.insert(
        family,
        setup(CompressionProfile::Final.cap_size(SoundnessMode::PessimisticConjecture)),
    );
    validate_artifact_envelope(&artifact).unwrap();
    artifact.setups.insert(
        family,
        setup(CompressionProfile::Step.cap_size(SoundnessMode::PessimisticConjecture)),
    );
    assert!(validate_artifact_envelope(&artifact)
        .unwrap_err()
        .contains("leafs"));
}

/// A compression artifact is admitted against the trusted chain of the supplied
/// program before its continuation proves anything: a history that hashes
/// consistently but is not the program's chain is rejected.
#[test]
fn compression_continuation_requires_the_trusted_chain() {
    let source = ProgramSource::legacy_binaries_from_bin(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/basic_fibonacci/app.bin"),
    );
    let mut artifact: ProofArtifact = proof_fixtures::read_file(proof_fixtures::chain_artifact(
        "pessimistic_conjecture",
        "compression",
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
fn compression_proof_profile_requires_the_trace_and_every_instance_schedule() {
    for profile in CompressionProfile::ALL {
        let proof = fake_compression_proof_for_profile(0, 1, profile);
        validate_compression_proof(&proof, profile, 1, SoundnessMode::PessimisticConjecture)
            .unwrap();
    }
    let mut proof = fake_compression_proof_for_profile(0, 2, CompressionProfile::Step);
    let family = UnrolledCircuitType::Unified.get_family_idx() as u32;
    proof.riscv_proofs.get_mut(&family).unwrap()[1]
        .whir_proof
        .whir_schedule = CompressionProfile::Final
        .config(SoundnessMode::PessimisticConjecture)
        .whir_schedule;
    assert!(validate_compression_proof(
        &proof,
        CompressionProfile::Step,
        2,
        SoundnessMode::PessimisticConjecture
    )
    .unwrap_err()
    .contains("WHIR schedule"));
    let proof = fake_compression_proof_for_profile(0, 2, CompressionProfile::Final);
    assert!(validate_compression_proof(
        &proof,
        CompressionProfile::Final,
        1,
        SoundnessMode::PessimisticConjecture
    )
    .unwrap_err()
    .contains("expected 1"));
    let proof = fake_compression_proof_for_profile(0, 1, CompressionProfile::Step);
    assert!(validate_compression_proof(
        &proof,
        CompressionProfile::Final,
        1,
        SoundnessMode::PessimisticConjecture
    )
    .unwrap_err()
    .contains("trace length"));
}

#[test]
fn ethproofs_compression_envelope_uses_its_last_step_profile() {
    let mode = SoundnessMode::EthproofsSoundnessCalc;
    assert_target_mode(ProofTarget::Compression, mode);
    let mut artifact = compression_artifact(ProofTarget::Compression, 6);
    artifact.soundness_mode = mode;
    artifact.proof = fake_compression_proof_in_mode(0, 1, CompressionProfile::Step, mode);
    let family = CompressionProfile::Step.circuit().get_family_idx() as u32;
    let cap_size = CompressionProfile::Step.cap_size(mode);
    artifact.setups.insert(
        family,
        setups::UnrolledCircuitSetupParams {
            family_idx: family,
            capacity: CompressionProfile::Step.circuit().get_domain_size() as u32,
            setup_caps: prover::merkle_trees::MerkleTreeCapVarLength {
                cap: vec![[7; 8]; cap_size],
            },
        },
    );
    artifact.validate_expected_mode(mode).unwrap();
    validate_artifact_envelope(&artifact).unwrap();
    assert_eq!(chain_unrolled_layers(&artifact).unwrap(), 0);
    artifact.proof = fake_compression_proof_for_profile(0, 1, CompressionProfile::Step);
    assert!(validate_artifact_envelope(&artifact)
        .unwrap_err()
        .contains("WHIR schedule"));
}

#[test]
fn ethproofs_compression_history_keeps_repeated_recurrent_layers() {
    let mode = SoundnessMode::EthproofsSoundnessCalc;
    let expected = expected_chain_end_params(
        ProofTarget::Compression,
        mode,
        6,
        BlakeMode::Compression.tag(),
        BlakeMode::Compression.tag(),
        BlakeMode::Compression.tag(),
        &mut |program| {
            Ok(match program {
                ChainProgram::User => [1; 8],
                ChainProgram::Fsv(
                    FsvProgram::UnrolledBaseLayer,
                    FsvProfile::Standard,
                    _,
                    SetupMachine::Unified,
                ) => [2; 8],
                ChainProgram::Fsv(
                    FsvProgram::UnifiedRecursionLayer,
                    FsvProfile::Standard,
                    BlakeMode::Compression,
                    SetupMachine::Unified,
                ) => [3; 8],
                ChainProgram::Fsv(
                    FsvProgram::UnifiedRecursionLayer,
                    FsvProfile::Standard,
                    BlakeMode::BlakeSpecialOpcodes,
                    SetupMachine::Compression(CompressionProfile::Step),
                ) => [4; 8],
                ChainProgram::Fsv(
                    FsvProgram::UnifiedRecursionLayer,
                    FsvProfile::Compression,
                    BlakeMode::BlakeSpecialOpcodes,
                    SetupMachine::Compression(CompressionProfile::Step),
                ) => [5; 8],
                _ => panic!("unexpected Ethproofs chain program"),
            })
        },
    )
    .unwrap();
    assert_eq!(
        expected,
        vec![[1; 8], [2; 8], [3; 8], [4; 8], [5; 8], [5; 8]]
    );
    let chain = rebuild_chain(&expected).unwrap();
    let once = rebuild_chain(&expected[..5]).unwrap();
    assert_eq!(chain.hash(), once.hash());
    assert_eq!(chain.preimage(), once.preimage());
}
