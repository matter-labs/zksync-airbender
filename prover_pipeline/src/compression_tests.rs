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
    let family = profile.circuit().get_family_idx() as u32;
    let schedule = profile
        .config(SoundnessMode::PessimisticConjecture)
        .whir_schedule;
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
fn ethproofs_compression_gkr_security_margins() {
    use full_statement_verifier::unified_circuit_statement::ETHPROOFS_COMPRESSION_MAX_INSTANCES;
    use prover::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use prover::gkr::prover_config::{example_configs, pow_bits};

    let mode = SoundnessMode::EthproofsSoundnessCalc;
    let artifact: ProofArtifact = proof_fixtures::read_file(proof_fixtures::chain_artifact(
        mode.file_suffix(),
        "compression",
    ));
    let family = CompressionProfile::Step.circuit().get_family_idx() as u32;
    let circuit = &artifact.proof.compiled_riscv_circuits[&family];
    let entry = &example_configs::ethproofs_soundcalc::COMPRESSION_2_23;
    let example_configs::ProximityRegime::JohnsonBound { m } = entry.base_analysis.regime else {
        panic!("Ethproofs Compression uses a Johnson base");
    };
    let loss =
        ((f64::from(m) + 0.5) * 2.0_f64.powf(entry.base_lde_factor_log2 as f64 / 2.0)).log2();
    let challenge_bits = 128.0 - 81.0_f64.log2();
    assert_eq!(m, 3);

    let config = CompressionProfile::Step.config(mode);
    assert_eq!(circuit.trace_len, 1 << config.trace_len_log2);
    assert_eq!(
        config.lookup_challenges_pow_bits::<BabyBearField, BabyBearExt4>(circuit),
        14
    );
    let lookup_bits =
        challenge_bits + 14.0 - (pow_bits::lookup_identity_degree(circuit) as f64).log2() - loss;
    println!("Johnson base list loss: {loss:.9} bits; lookup: {lookup_bits:.9} bits");
    assert!(lookup_bits >= 100.0, "lookup: {lookup_bits:.9} bits");
    let pessimistic = CompressionProfile::Step.config(SoundnessMode::PessimisticConjecture);
    assert_eq!(
        pessimistic.lookup_challenges_pow_bits::<BabyBearField, BabyBearExt4>(circuit),
        9
    );

    let memory_pow_bits = verifier_common::MEMORY_DELEGATION_POW_BITS;
    assert_eq!(memory_pow_bits, 19);
    let keys_per_row =
        circuit.memory_layout.ram_access_sets.len() + 1 + circuit.memory_layout.teardown_sets.len();
    let boundary_keys = prover::cs::definitions::NUM_REGISTERS + 1;
    for (k, expected_degree) in [(1, 50_331_681), (2, 100_663_329), (3, 150_994_977)] {
        let degree = k * circuit.trace_len * keys_per_row + boundary_keys;
        let bits = challenge_bits - (degree as f64).log2() - 2.0 + memory_pow_bits as f64
            - k as f64 * loss;
        println!("memory k={k}, j={k}: {bits:.9} bits");
        assert_eq!(degree, expected_degree);
        assert!(bits >= 100.0, "memory k={k}, j={k}: {bits:.9} bits");
    }
    assert_eq!(ETHPROOFS_COMPRESSION_MAX_INSTANCES, 3);
    assert_eq!(
        compression_schedule(mode)
            .iter()
            .map(|&(_, _, count)| count)
            .collect::<Vec<_>>(),
        [3, 2, 1]
    );
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
    let mut artifact: ProofArtifact = proof_fixtures::read_file(proof_fixtures::chain_artifact(
        mode.file_suffix(),
        "compression",
    ));
    artifact.validate_expected_mode(mode).unwrap();
    validate_artifact_envelope(&artifact).unwrap();
    assert_eq!(chain_unrolled_layers(&artifact).unwrap(), 0);
    let family = CompressionProfile::Step.circuit().get_family_idx() as u32;
    artifact.proof.riscv_proofs.get_mut(&family).unwrap()[0]
        .whir_proof
        .whir_schedule = CompressionProfile::Step
        .config(SoundnessMode::PessimisticConjecture)
        .whir_schedule;
    assert!(validate_artifact_envelope(&artifact)
        .unwrap_err()
        .contains("WHIR schedule"));
}
