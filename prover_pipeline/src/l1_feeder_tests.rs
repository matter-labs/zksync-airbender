use super::*;
use prover::definitions::GKRExternalChallenges;
use prover::gkr::whir::{WhirBaseLayerCommitmentAndQueries, WhirPolyCommitProof};
use std::cell::RefCell;
use std::rc::Rc;

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
    FsvPrograms::load(ProofTarget::Base, blake)
}

pub(super) fn artifact(target: ProofTarget, n: usize) -> ProofArtifact {
    feeder_artifact(target, n, 0)
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

pub(super) fn feeder_artifact(target: ProofTarget, n: usize, feeder_layers: u32) -> ProofArtifact {
    finalize_artifact(
        &modes_only(compression_modes()),
        target,
        ProverBackend::Cpu,
        0,
        &program(),
        RecursionState {
            stage: target,
            l1: None,
            proof: if feeder_layers > 0 {
                fake_feeder_proof(0, 1)
            } else {
                empty_proof()
            },
            setups: BTreeMap::new(),
            chain_end_params: (1..=n).map(|i| [i as u32; 8]).collect(),
            input_is_base: target == ProofTarget::Base,
            timings: ProofTimingsMs::default(),
            program_cycles: 0,
            feeder_layers,
        },
    )
}

#[test]
fn feeder_registration_unions_profiles_for_the_same_binary() {
    for mode in [BlakeMode::Compression, BlakeMode::BlakeSpecialOpcodes] {
        let blake = PipelineBlakeModes {
            final_layer: mode,
            ..compression_modes()
        };
        let registrations = pipeline_registrations(
            &program(),
            None,
            ProofTarget::L1Feeder,
            Some(100),
            &FsvPrograms::load(ProofTarget::L1Feeder, blake),
        );
        // The special-opcodes unified binary is registered twice when it is
        // also the final layer: (Unified, Standard) and (Unified22, L1Feeder)
        // are distinct handles with distinct precomputations.
        assert_eq!(
            registrations.len(),
            if mode == BlakeMode::BlakeSpecialOpcodes {
                9
            } else {
                10
            }
        );
        for (i, fsv) in L1_FEEDER_PROGRAMS.into_iter().enumerate() {
            let (bin, text) = load_fsv_program(fsv_dir(), fsv, BlakeMode::BlakeSpecialOpcodes);
            let key = handle_key(ExecutionKind::Unified22, MachineType::Reduced, &bin, &text);
            let profiles = &registrations[&key].profiles;
            assert_eq!(profiles, &BTreeSet::from([ProofProfile::L1Feeder]));
            let standard_key =
                handle_key(ExecutionKind::Unified, MachineType::Reduced, &bin, &text);
            if i == 0 && mode == BlakeMode::BlakeSpecialOpcodes {
                assert_eq!(
                    registrations[&standard_key].profiles,
                    BTreeSet::from([ProofProfile::Standard, ProofProfile::L1FeederA])
                );
            } else {
                assert_eq!(
                    registrations[&standard_key].profiles,
                    BTreeSet::from([ProofProfile::L1FeederA])
                );
            }
        }
        let standard = pipeline_registrations(
            &program(),
            None,
            ProofTarget::RecursionUnified,
            Some(100),
            &FsvPrograms::load(ProofTarget::RecursionUnified, blake),
        );
        for (key, registration) in standard {
            assert_eq!(
                registration.profiles,
                BTreeSet::from([ProofProfile::Standard])
            );
            assert!(registrations[&key]
                .profiles
                .contains(&ProofProfile::Standard));
        }
    }
}

#[derive(Default)]
struct RecordingBackend {
    handles: BTreeMap<HandleKey, RegisteredBinary<Option<u32>>>,
    preparations: usize,
}

impl ProveBackend for RecordingBackend {
    fn register(
        &mut self,
        kind: ExecutionKind,
        machine: MachineType,
        bin: &[u32],
        text: &[u32],
        cycles_bound: Option<u32>,
        profiles: &[ProofProfile],
    ) {
        register_binary(
            &mut self.handles,
            handle_key(kind, machine, bin, text),
            profiles,
            || {
                self.preparations += 1;
                cycles_bound
            },
        );
    }

    fn prove(&mut self, _: ProveRequest<'_>) -> Result<(ProgramProof, Setups), String> {
        panic!("registration tests must not prove");
    }

    fn prove_l1_wrap(&mut self, _: L1WrapRequest<'_>) -> Result<L1WrapResult, String> {
        panic!("registration tests must not prove");
    }

    fn setups(
        &mut self,
        _: ExecutionKind,
        _: MachineType,
        _: &[u32],
        _: &[u32],
        _: ProofProfile,
    ) -> Option<Setups> {
        panic!("registration tests must not read setups");
    }
}

#[test]
fn registration_matches_remaining_stages_and_reuses_batch_setups() {
    use ProofTarget::{Base, L1Feeder, RecursionUnified, RecursionUnrolled, L1};
    let cases: &[(Option<ProofTarget>, ProofTarget, &[usize])] = &[
        (None, Base, &[0]),
        (None, RecursionUnrolled, &[0, 1, 2]),
        (None, RecursionUnified, &[0, 1, 2, 3, 4, 5]),
        (None, L1Feeder, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
        (None, L1, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
        (Some(Base), RecursionUnrolled, &[1, 2]),
        (Some(Base), RecursionUnified, &[1, 2, 3, 4, 5]),
        (Some(Base), L1Feeder, &[1, 2, 3, 4, 5, 6, 7, 8, 9]),
        (Some(Base), L1, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
        (Some(RecursionUnrolled), RecursionUnified, &[1, 2, 3, 4, 5]),
        (
            Some(RecursionUnrolled),
            L1Feeder,
            &[1, 2, 3, 4, 5, 6, 7, 8, 9],
        ),
        (
            Some(RecursionUnrolled),
            L1,
            &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        ),
        (Some(RecursionUnified), L1Feeder, &[6, 7, 8, 9]),
        (Some(RecursionUnified), L1, &[6, 7, 8, 9, 10]),
        (Some(L1Feeder), L1, &[10]),
    ];
    let loaded = program();
    let user_key = handle_key(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        &loaded.bin_u32,
        &loaded.text_u32,
    );
    for final_mode in [BlakeMode::Compression, BlakeMode::BlakeSpecialOpcodes] {
        let blake = PipelineBlakeModes {
            final_layer: final_mode,
            ..compression_modes()
        };
        let mut binaries = vec![(user_key, ProofProfile::Standard, Some(100))];
        for (fsv, mode, kind, profile) in [
            (
                FsvProgram::UnrolledBaseLayer,
                BlakeMode::Compression,
                ExecutionKind::Unrolled,
                ProofProfile::Standard,
            ),
            (
                FsvProgram::UnrolledRecursionLayer,
                BlakeMode::Compression,
                ExecutionKind::Unrolled,
                ProofProfile::Standard,
            ),
            (
                FsvProgram::UnrolledBaseLayer,
                BlakeMode::Compression,
                ExecutionKind::Unified,
                ProofProfile::Standard,
            ),
            (
                FsvProgram::UnrolledRecursionLayer,
                BlakeMode::Compression,
                ExecutionKind::Unified,
                ProofProfile::Standard,
            ),
            (
                FsvProgram::UnifiedRecursionLayer,
                final_mode,
                ExecutionKind::Unified,
                ProofProfile::Standard,
            ),
            (
                FsvProgram::UnifiedRecursionLayer,
                BlakeMode::BlakeSpecialOpcodes,
                ExecutionKind::Unified22,
                ProofProfile::L1Feeder,
            ),
            (
                FsvProgram::UnifiedRecursionLayerL1FeederA,
                BlakeMode::BlakeSpecialOpcodes,
                ExecutionKind::Unified22,
                ProofProfile::L1Feeder,
            ),
            (
                FsvProgram::UnifiedRecursionLayer,
                BlakeMode::BlakeSpecialOpcodes,
                ExecutionKind::Unified,
                ProofProfile::L1FeederA,
            ),
            (
                FsvProgram::UnifiedRecursionLayerL1FeederA,
                BlakeMode::BlakeSpecialOpcodes,
                ExecutionKind::Unified,
                ProofProfile::L1FeederA,
            ),
            (
                FsvProgram::UnifiedRecursionLayerL1FeederWrap,
                BlakeMode::BlakeSpecialOpcodes,
                L1_WRAP_KIND,
                ProofProfile::L1Wrap,
            ),
        ] {
            let (bin, text) = load_fsv_program(fsv_dir(), fsv, mode);
            binaries.push((
                handle_key(kind, MachineType::Reduced, &bin, &text),
                profile,
                None,
            ));
        }
        for &(start, target, required) in cases {
            let mut expected = BTreeMap::<_, (BTreeSet<_>, Option<u32>)>::new();
            for &index in required {
                let (key, profile, cycles_bound) = binaries[index];
                expected
                    .entry(key)
                    .or_insert_with(|| (BTreeSet::new(), cycles_bound))
                    .0
                    .insert(profile);
            }
            let mut backend = RecordingBackend::default();
            for _batch in 0..2 {
                register_pipeline_plan(
                    &mut backend,
                    pipeline_registrations(
                        &loaded,
                        start,
                        target,
                        Some(100),
                        &FsvPrograms::load(target, blake),
                    ),
                );
                let actual: BTreeMap<_, _> = backend
                    .handles
                    .iter()
                    .map(|(&key, binary)| (key, (binary.profiles.clone(), binary.handle)))
                    .collect();
                assert_eq!(
                    actual, expected,
                    "{start:?} -> {target:?}, final {final_mode:?}"
                );
                assert_eq!(
                    backend.preparations,
                    expected.len(),
                    "repeated registration must not prepare another setup"
                );
            }
        }
    }
}

#[test]
#[should_panic(expected = "pipeline binary was registered for a different profile set")]
fn changed_profile_registration_is_rejected_before_preparing_it() {
    let mut handles = BTreeMap::new();
    let key = (0, 0, [0; 32]);
    register_binary(&mut handles, key, &[ProofProfile::Standard], || ());
    register_binary(&mut handles, key, &[ProofProfile::L1Feeder], || {
        panic!("duplicate setup must not be prepared")
    });
}

#[test]
fn repeated_profile_registration_prepares_once_before_proving() {
    let mut handles = BTreeMap::new();
    let key = (0, 0, [0; 32]);
    let mut events = Vec::new();
    for profiles in [
        [ProofProfile::Standard, ProofProfile::L1Feeder],
        [ProofProfile::L1Feeder, ProofProfile::Standard],
    ] {
        register_binary(&mut handles, key, &profiles, || {
            events.push("prepare");
            7
        });
        let _start = Instant::now();
        assert_eq!(handles[&key].handle, 7);
        events.push("prove");
    }
    assert_eq!(events, ["prepare", "prove", "prove"]);
    assert_eq!(handles.len(), 1);
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
    let result = finalize_artifact(
        &modes_only(blake),
        ProofTarget::L1Feeder,
        ProverBackend::Cpu,
        0,
        &program(),
        RecursionState {
            stage: ProofTarget::L1Feeder,
            l1: None,
            proof: empty_proof(),
            setups: BTreeMap::new(),
            chain_end_params: checkpoint.chain_end_params.clone(),
            input_is_base: false,
            timings: ProofTimingsMs::default(),
            program_cycles: 0,
            feeder_layers: 1,
        },
    );
    assert_eq!(result.blake_final, checkpoint.blake_final);
    assert_eq!(result.blake_bridge, checkpoint.blake_bridge);
    assert_eq!(result.blake_unrolled, checkpoint.blake_unrolled);
}

#[test]
fn feeder_artifacts_claim_their_feeder_layers_after_the_final_layer() {
    for feeder_layers in 1..=MAX_FEEDER_LAYERS {
        let n = 3 + feeder_layers as usize + 1;
        assert_eq!(
            chain_unrolled_layers(&feeder_artifact(ProofTarget::L1Feeder, n, feeder_layers))
                .unwrap(),
            1
        );
        assert_eq!(
            chain_unrolled_layers(&feeder_artifact(ProofTarget::L1, n - 1, feeder_layers)).unwrap(),
            0
        );
        // an isolated length mismatch: one layer fewer than claimed
        assert!(chain_unrolled_layers(&feeder_artifact(
            ProofTarget::L1Feeder,
            n - 2,
            feeder_layers
        ))
        .is_err());
    }
    for feeder_layers in [0, MAX_FEEDER_LAYERS + 1] {
        assert!(
            chain_unrolled_layers(&feeder_artifact(ProofTarget::L1Feeder, 12, feeder_layers))
                .is_err()
        );
    }
    assert!(chain_unrolled_layers(&feeder_artifact(ProofTarget::RecursionUnified, 4, 1)).is_err());
    assert!(chain_unrolled_layers(&artifact(ProofTarget::L1, 3)).is_err());
}

#[test]
fn expected_chain_derives_a_prefix_and_the_last_proof_profile() {
    for last_profile in FeederProfile::ALL {
        for feeder_layers in 1..=4u32 {
            let mut programs = Vec::new();
            let expected = expected_chain_end_params(
                ProofTarget::L1Feeder,
                3 + feeder_layers as usize,
                feeder_layers,
                last_profile,
                BlakeMode::Compression.tag(),
                BlakeMode::Compression.tag(),
                BlakeMode::Compression.tag(),
                &mut |program| {
                    let entry = match program {
                        ChainProgram::Fsv(program, _, SetupMachine::L1Feeder(profile)) => {
                            let role = if program == FsvProgram::UnifiedRecursionLayer {
                                10
                            } else {
                                assert_eq!(program, FsvProgram::UnifiedRecursionLayerL1FeederA);
                                20
                            };
                            [role + if profile == FeederProfile::A { 1 } else { 2 }; 8]
                        }
                        _ => [1; 8],
                    };
                    programs.push(entry);
                    Ok(entry)
                },
            )
            .unwrap();
            assert_eq!(expected.len(), 3 + feeder_layers as usize);
            for (layer, entry) in expected[3..].iter().enumerate() {
                let profile = if layer + 1 == feeder_layers as usize {
                    last_profile
                } else {
                    FeederProfile::A
                };
                let role = if layer == 0 { 10 } else { 20 };
                assert_eq!(
                    *entry,
                    [role + if profile == FeederProfile::A { 1 } else { 2 }; 8]
                );
            }
            assert_eq!(programs, expected);
        }
    }
}

#[test]
fn stale_schema_feeder_artifacts_are_rejected_and_pre_feeder_ones_accepted() {
    let mut legacy = artifact(ProofTarget::RecursionUnified, 3);
    legacy.schema_version = LEGACY_ARTIFACT_SCHEMA_VERSION;
    validate_artifact_envelope(&legacy).unwrap();
    let mut stale = feeder_artifact(ProofTarget::L1Feeder, 4, 1);
    stale.schema_version = LEGACY_ARTIFACT_SCHEMA_VERSION;
    assert!(validate_artifact_envelope(&stale)
        .unwrap_err()
        .starts_with("stale L1Feeder proof artifact"));
    let mut unknown = artifact(ProofTarget::RecursionUnified, 3);
    unknown.schema_version = ARTIFACT_SCHEMA_VERSION + 1;
    assert!(validate_artifact_envelope(&unknown).is_err());
    assert_eq!(
        artifact(ProofTarget::Base, 1).schema_version,
        ARTIFACT_SCHEMA_VERSION
    );
}

#[test]
fn malformed_setup_caps_are_rejected_at_artifact_admission() {
    use prover::merkle_trees::MerkleTreeCapVarLength;
    let cap = |leaves: usize| MerkleTreeCapVarLength {
        cap: vec![[7; 8]; leaves],
    };
    let params = |leaves: usize| setups::UnrolledCircuitSetupParams {
        family_idx: 128,
        capacity: 1 << 22,
        setup_caps: cap(leaves),
    };
    for (target, feeder_layers, good, bad) in [
        (ProofTarget::RecursionUnified, 0, 16usize, 32usize),
        (ProofTarget::L1Feeder, 1, 16, 32),
    ] {
        let mut good_artifact = feeder_artifact(target, 4, feeder_layers);
        good_artifact.setups.insert(128, params(good));
        validate_artifact_envelope(&good_artifact).unwrap();
        for leaves in [bad, 0, good - 1, good + 1] {
            let mut artifact = feeder_artifact(target, 4, feeder_layers);
            artifact.setups.insert(128, params(leaves));
            assert!(validate_artifact_envelope(&artifact)
                .unwrap_err()
                .contains("leafs"));
        }
        let mut mixed = feeder_artifact(target, 4, feeder_layers);
        mixed.setups.insert(1, params(good));
        mixed.setups.insert(128, params(bad));
        assert!(validate_artifact_envelope(&mixed)
            .unwrap_err()
            .contains("leafs"));
    }
}

#[test]
fn feeder_setup_caps_match_the_resolved_profile() {
    use prover::merkle_trees::MerkleTreeCapVarLength;
    assert_eq!(FeederProfile::A.config().cap_size, 4);
    assert_eq!(FeederProfile::C.config().cap_size, 16);
    for (profile, other) in [
        (FeederProfile::A, FeederProfile::C),
        (FeederProfile::C, FeederProfile::A),
    ] {
        let config = profile.config();
        let setups = |leaves| {
            BTreeMap::from([(
                profile.circuit().get_family_idx() as u32,
                setups::UnrolledCircuitSetupParams {
                    family_idx: profile.circuit().get_family_idx() as u32,
                    capacity: 1 << config.trace_len_log2,
                    setup_caps: MerkleTreeCapVarLength {
                        cap: vec![[7; 8]; leaves],
                    },
                },
            )])
        };
        setups::validate_setups_cap_size(&setups(config.cap_size), config.cap_size).unwrap();
        assert!(setups::validate_setups_cap_size(
            &setups(other.config().cap_size),
            config.cap_size
        )
        .is_err());
    }
}

#[test]
fn l1_target_is_accepted_once_the_wrap_circuit_matches_the_wrap_program() {
    validate_l1_wrap_activation().unwrap();
    validate_continuation_targets(ProofTarget::L1Feeder, ProofTarget::L1).unwrap();
    validate_continuation_targets(ProofTarget::RecursionUnified, ProofTarget::L1Feeder).unwrap();
}

/// A feeder artifact is admitted against the trusted chain of the supplied
/// program before its continuation proves anything: a history that hashes
/// consistently but is not the program's chain is rejected.
#[test]
fn feeder_continuation_requires_the_trusted_chain() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/hashed_fibonacci");
    let source = ProgramSource::from_paths(
        dir.join("app_plain.bin").to_string_lossy().into_owned(),
        None,
    );
    let loaded = load_program(&source).unwrap();
    let mut artifact = feeder_artifact(ProofTarget::L1Feeder, 6, 3);
    artifact.program_bin_keccak = keccak256(&loaded.bin_bytes);
    artifact.program_text_keccak = keccak256(&loaded.text_bytes);
    validate_continuation_request(&artifact, ProofTarget::L1).unwrap();
    let error = admit_continuation(&artifact, &source, ProofTarget::L1).unwrap_err();
    assert!(
        error.contains("do not match the trusted per-layer end-params"),
        "{error}"
    );
}

/// A feeder-loop harness: the backend proves one fake feeder proof per
/// request with the scripted instance count; the verifier predicts the next
/// scripted count and verifies every proof against the chain the backend
/// extended.
struct ScriptedChain {
    /// Instance counts per layer, in order.
    instances: Vec<usize>,
    proven: Rc<RefCell<usize>>,
    chain_end_params: Rc<RefCell<Vec<[u32; 8]>>>,
}

impl ScriptedChain {
    /// `instances` is indexed by absolute layer; a resumed `state` starts at
    /// its `feeder_layers`.
    fn new(state: &RecursionState, instances: &[usize]) -> Self {
        Self {
            instances: instances.to_vec(),
            proven: Rc::new(RefCell::new(state.feeder_layers as usize)),
            chain_end_params: Rc::new(RefCell::new(state.chain_end_params.clone())),
        }
    }

    /// The verifier side of the same scripted chain.
    fn share(&self) -> Self {
        Self {
            instances: self.instances.clone(),
            proven: Rc::clone(&self.proven),
            chain_end_params: Rc::clone(&self.chain_end_params),
        }
    }

    fn state() -> RecursionState {
        RecursionState {
            stage: ProofTarget::RecursionUnified,
            l1: None,
            proof: empty_proof(),
            setups: BTreeMap::new(),
            chain_end_params: vec![[1; 8], [2; 8], [3; 8]],
            input_is_base: false,
            timings: ProofTimingsMs::default(),
            program_cycles: 0,
            feeder_layers: 0,
        }
    }

    fn profile(&self, layer: usize) -> FeederProfile {
        if layer + 1 == self.instances.len() && self.instances[layer] == 1 {
            FeederProfile::C
        } else {
            FeederProfile::A
        }
    }

    fn report(instances: usize) -> FsvRunReport {
        Self::report_for(FeederProfile::C, instances)
    }

    fn report_for(profile: FeederProfile, instances: usize) -> FsvRunReport {
        let cycles =
            (instances as u64 * profile.circuit().get_domain_size() as u64).saturating_sub(7);
        FsvRunReport {
            cycles,
            output: [0; 16],
            nd_words_remaining: 0,
            counters: riscv_transpiler::vm::DelegationsAndUnifiedCounters {
                cycles: cycles as usize,
                ..Default::default()
            },
            touched_windows: vec![0, 1],
            max_touched_address: 0,
            min_sp: 0x87f000,
            success_pc: 0,
            final_pc: 0,
        }
    }
}

impl ProveBackend for ScriptedChain {
    fn register(
        &mut self,
        _: ExecutionKind,
        _: MachineType,
        _: &[u32],
        _: &[u32],
        _: Option<u32>,
        _: &[ProofProfile],
    ) {
        panic!("feeder loop tests must not register");
    }

    fn prove(&mut self, request: ProveRequest<'_>) -> Result<(ProgramProof, Setups), String> {
        let layer = *self.proven.borrow();
        let profile = self.profile(layer);
        let spec = feeder_stage(FeederRole::Recurrent, profile);
        assert_eq!(request.kind, spec.kind);
        assert_eq!(request.profile, spec.profile);
        assert_eq!(request.machine, MachineType::Reduced);
        *self.proven.borrow_mut() += 1;
        let instances = self.instances[layer];
        // F1 and the recurrent layers are distinct programs; every recurrent
        // layer proves the same binary, so its end params repeat.
        let final_pc = if layer == 0 {
            1
        } else if profile == FeederProfile::A {
            2
        } else {
            3
        };
        let proof = fake_feeder_proof_for_profile(final_pc, instances, profile);
        self.chain_end_params
            .borrow_mut()
            .push(compute_end_params(&BTreeMap::new(), proof.final_pc));
        Ok((proof, BTreeMap::new()))
    }

    fn prove_l1_wrap(&mut self, _: L1WrapRequest<'_>) -> Result<L1WrapResult, String> {
        panic!("feeder loop tests must not wrap");
    }

    fn setups(
        &mut self,
        _: ExecutionKind,
        _: MachineType,
        _: &[u32],
        _: &[u32],
        _: ProofProfile,
    ) -> Option<Setups> {
        panic!("feeder loop tests must not read setups");
    }
}

impl FeederVerifier for ScriptedChain {
    fn native_verify_standard(&self, _: Vec<u32>) -> Result<[u32; 16], String> {
        Ok([0; 16])
    }

    fn predict(&self, _: &ProgramWords, _: Vec<u32>) -> Result<FsvRunReport, String> {
        let layer = *self.proven.borrow();
        let mut report = Self::report_for(self.profile(layer), self.instances[layer]);
        // the run reproduces the input's native output: the standard output
        // for F1, the previous feeder layer's output afterwards
        if layer > 0 {
            report.output = self.native_verify(FeederProfile::A, vec![])?;
        }
        Ok(report)
    }

    fn native_verify(&self, _: FeederProfile, _: Vec<u32>) -> Result<[u32; 16], String> {
        let mut output = [0; 16];
        output[8..].copy_from_slice(&rebuild_chain(&self.chain_end_params.borrow())?.hash());
        Ok(output)
    }

    fn wrap_run(&self, _: &ProgramWords, _: Vec<u32>) -> Result<FsvRunReport, String> {
        let mut report = Self::report(1);
        report.cycles = L1_WRAP_PROGRAM_CYCLE_LIMIT as u64 - 7;
        report.counters.cycles = report.cycles as usize;
        report.output = self.native_verify(FeederProfile::A, vec![])?;
        Ok(report)
    }
}

struct Layers(Vec<(u8, u32, usize)>);

impl FeederObserver for Layers {
    fn feeder_layer(
        &mut self,
        layer: u8,
        state: &RecursionState,
        _: &FsvRunReport,
    ) -> Result<(), String> {
        self.0.push((
            layer,
            state.feeder_layers,
            feeder_proof_instances(&state.proof, None).unwrap(),
        ));
        Ok(())
    }
}

fn run_scripted(
    script: &[usize],
    state: RecursionState,
) -> (Result<RecursionState, String>, Vec<(u8, u32, usize)>) {
    let fsv = modes_only(compression_modes());
    let mut backend = ScriptedChain::new(&state, script);
    let harness = backend.share();
    let mut layers = Layers(vec![]);
    let result = run_feeder_layers(
        &mut backend,
        &fsv,
        state,
        0,
        &mut layers,
        &|_, _| vec![],
        &harness,
    );
    (result, layers.0)
}

#[test]
fn feeder_loop_converges_and_records_one_history_entry_per_layer() {
    for script in [&[2usize, 1, 1][..], &[4, 2, 1], &[5, 3, 2, 1], &[1]] {
        let (state, layers) = run_scripted(script, ScriptedChain::state());
        let state = state.unwrap();
        assert_eq!(state.feeder_layers as usize, script.len());
        assert_eq!(state.chain_end_params.len(), 3 + script.len());
        assert_eq!(state.timings.l1_feeder_ms.len(), script.len());
        assert_eq!(
            layers,
            script
                .iter()
                .enumerate()
                .map(|(i, &n)| (i as u8, i as u32 + 1, n))
                .collect::<Vec<_>>()
        );
        assert_eq!(feeder_proof_instances(&state.proof, Some(1)).unwrap(), 1);
        assert_eq!(
            validate_feeder_proof(&state.proof, Some(1)).unwrap(),
            FeederProfile::C
        );
        // the wrap fit over the last feeder proof
        let fsv = modes_only(compression_modes());
        let harness = ScriptedChain::new(&state, script);
        let fitted = check_feeder_fit(&fsv, state, &|_, _| vec![], &harness).unwrap();
        assert_eq!(fitted.stage, ProofTarget::L1Feeder);
    }
}

#[test]
fn feeder_loop_rejects_non_decreasing_and_zero_predictions() {
    for (script, needle) in [
        (&[1usize, 1, 1][..], "not converging"),
        (&[2, 2, 1], "not converging"),
        (&[4, 4], "not converging"),
        (&[4, 5], "not converging"),
        (&[3, 0], "predicts no unified instance"),
    ] {
        let (result, _) = run_scripted(script, ScriptedChain::state());
        assert!(result.err().unwrap().contains(needle), "{script:?}");
    }
}

/// A resumed single-instance feeder whose claimed history differs from the
/// chain its proof authenticates is rejected on entry (no layer proven), and
/// the wrap fit binds its native output to the history as well.
#[test]
fn feeder_resume_rejects_a_history_its_proof_does_not_authenticate() {
    // a proven single-instance chain whose claimed history is then altered
    let tampered = || {
        let (state, _) = run_scripted(&[1], ScriptedChain::state());
        let mut state = state.unwrap();
        let backend = ScriptedChain::new(&state, &[1]);
        state.chain_end_params[0][0] ^= 1;
        (state, backend)
    };
    let fsv = modes_only(compression_modes());
    let (state, mut backend) = tampered();
    let verifier = backend.share();
    let error = run_feeder_layers(
        &mut backend,
        &fsv,
        state,
        0,
        &mut NoopObserver,
        &|_, _| vec![],
        &verifier,
    )
    .err()
    .unwrap();
    assert!(error.contains("recursion chain"), "{error}");
    assert_eq!(
        *backend.proven.borrow(),
        1,
        "resume must not prove another layer"
    );
    let (state, backend) = tampered();
    let verifier = backend.share();
    let error = check_feeder_fit(&fsv, state, &|_, _| vec![], &verifier)
        .err()
        .unwrap();
    assert!(error.contains("recursion chain"), "{error}");
}

/// A prediction run that leaves input unread or reproduces another output
/// is rejected before any proof is produced.
#[test]
fn feeder_loop_rejects_incomplete_or_mismatching_prediction_runs_before_proving() {
    struct Broken {
        inner: ScriptedChain,
        unread: usize,
        flip_output: bool,
    }
    impl FeederVerifier for Broken {
        fn native_verify_standard(&self, nd: Vec<u32>) -> Result<[u32; 16], String> {
            self.inner.native_verify_standard(nd)
        }
        fn predict(&self, program: &ProgramWords, nd: Vec<u32>) -> Result<FsvRunReport, String> {
            let mut report = self.inner.predict(program, nd)?;
            report.nd_words_remaining = self.unread;
            if self.flip_output {
                report.output[0] ^= 1;
            }
            Ok(report)
        }
        fn native_verify(&self, profile: FeederProfile, nd: Vec<u32>) -> Result<[u32; 16], String> {
            self.inner.native_verify(profile, nd)
        }
        fn wrap_run(&self, program: &ProgramWords, nd: Vec<u32>) -> Result<FsvRunReport, String> {
            self.inner.wrap_run(program, nd)
        }
    }
    for (unread, flip_output, needle) in [
        (3usize, false, "left 3 input words unread"),
        (0, true, "differs from the input's native output"),
    ] {
        let state = ScriptedChain::state();
        let fsv = modes_only(compression_modes());
        let mut backend = ScriptedChain::new(&state, &[4, 2, 1]);
        let verifier = Broken {
            inner: backend.share(),
            unread,
            flip_output,
        };
        let result = run_feeder_layers(
            &mut backend,
            &fsv,
            state,
            0,
            &mut NoopObserver,
            &|_, _| vec![],
            &verifier,
        );
        assert!(result.err().unwrap().contains(needle), "{needle}");
        assert_eq!(
            *backend.proven.borrow(),
            0,
            "no layer may be proven: {needle}"
        );
    }
}

#[test]
fn feeder_loop_stops_at_the_layer_cap() {
    let script: Vec<usize> = (0..MAX_FEEDER_LAYERS as usize + 2)
        .rev()
        .map(|n| n + 2)
        .collect();
    let (result, layers) = run_scripted(&script, ScriptedChain::state());
    assert!(result
        .err()
        .unwrap()
        .contains("did not reach one terminal C instance"));
    assert_eq!(layers.len(), MAX_FEEDER_LAYERS as usize);
}

#[test]
fn feeder_loop_rejects_a_proof_shape_that_misses_its_prediction() {
    let state = ScriptedChain::state();
    let fsv = modes_only(compression_modes());
    // the verifier predicts 2 instances, the backend proves 3
    let harness = ScriptedChain::new(&state, &[2, 1]);
    let mut backend = ScriptedChain::new(&state, &[3, 1]);
    let result = run_feeder_layers(
        &mut backend,
        &fsv,
        state,
        0,
        &mut NoopObserver,
        &|_, _| vec![],
        &harness,
    );
    assert!(result
        .err()
        .unwrap()
        .contains("carries 3 instance(s), predicted 2"));
}

#[test]
fn feeder_loop_resumes_both_a_boundaries_and_stops_only_at_c() {
    let script = [2usize, 1, 1];
    let (full, _) = run_scripted(&script, ScriptedChain::state());
    let full = full.unwrap();
    // resume after layer 0 (two A instances): layers 1 and 2 remain
    let mut after_first = ScriptedChain::state();
    after_first.feeder_layers = 1;
    after_first.proof = fake_feeder_proof_for_profile(1, 2, FeederProfile::A);
    after_first.chain_end_params = full.chain_end_params[..4].to_vec();
    let (resumed, layers) = run_scripted(&script, after_first);
    let resumed = resumed.unwrap();
    assert_eq!(layers, vec![(1, 2, 1), (2, 3, 1)]);
    assert_eq!(resumed.feeder_layers, full.feeder_layers);
    assert_eq!(resumed.chain_end_params, full.chain_end_params);
    assert_eq!(resumed.proof.final_pc, full.proof.final_pc);
    // A single A instance must still be followed by C.
    let mut after_second = ScriptedChain::state();
    after_second.feeder_layers = 2;
    after_second.proof = fake_feeder_proof_for_profile(2, 1, FeederProfile::A);
    after_second.chain_end_params = full.chain_end_params[..5].to_vec();
    let (resumed, layers) = run_scripted(&script, after_second);
    let resumed = resumed.unwrap();
    assert_eq!(layers, vec![(2, 3, 1)]);
    assert_eq!(resumed.chain_end_params, full.chain_end_params);
    // C is terminal: nothing to prove.
    let mut done = ScriptedChain::state();
    done.feeder_layers = 3;
    done.proof = fake_feeder_proof(3, 1);
    done.chain_end_params = full.chain_end_params.clone();
    let (skipped, layers) = run_scripted(&[], done);
    let skipped = skipped.unwrap();
    assert!(layers.is_empty());
    assert_eq!(skipped.feeder_layers, 3);
    assert_eq!(skipped.chain_end_params, full.chain_end_params);
    assert!(skipped.timings.l1_feeder_ms.is_empty());
}

/// The private feeder-checkpoint admission: feeder layer count, the feeder cap,
/// setups, the feeder proof shape and the trusted history.
#[test]
fn feeder_checkpoint_admission_checks_shape_caps_and_trusted_history() {
    use prover::merkle_trees::MerkleTreeCapVarLength;
    let trusted = |program: ChainProgram| -> Result<[u32; 8], String> {
        Ok(match program {
            ChainProgram::User => [1; 8],
            ChainProgram::Fsv(
                FsvProgram::UnifiedRecursionLayer,
                _,
                SetupMachine::L1Feeder(FeederProfile::A),
            ) => [10; 8],
            ChainProgram::Fsv(FsvProgram::UnifiedRecursionLayerL1FeederA, _, _) => [20; 8],
            ChainProgram::Fsv(..) => [2; 8],
        })
    };
    let caps = |leaves: usize| {
        BTreeMap::from([(
            128,
            setups::UnrolledCircuitSetupParams {
                family_idx: 128,
                capacity: 1 << 22,
                setup_caps: MerkleTreeCapVarLength {
                    cap: vec![[7; 8]; leaves],
                },
            },
        )])
    };
    let checkpoint = || RecursionState {
        stage: ProofTarget::L1Feeder,
        l1: None,
        proof: fake_feeder_proof_for_profile(2, 1, FeederProfile::A),
        setups: caps(4),
        chain_end_params: vec![[1; 8], [2; 8], [2; 8], [10; 8], [20; 8]],
        input_is_base: false,
        timings: ProofTimingsMs::default(),
        program_cycles: 0,
        feeder_layers: 2,
    };
    let admit = |state: &RecursionState| {
        validate_feeder_checkpoint(state, compression_modes(), &mut |program| trusted(program))
    };
    admit(&checkpoint()).unwrap();
    let mut wrong_history = checkpoint();
    wrong_history.chain_end_params[3][0] ^= 1;
    assert!(admit(&wrong_history).unwrap_err().contains("trusted chain"));
    let mut wrong_caps = checkpoint();
    wrong_caps.setups = caps(32);
    assert!(admit(&wrong_caps).unwrap_err().contains("leafs"));
    let mut no_layers = checkpoint();
    no_layers.feeder_layers = 0;
    assert!(admit(&no_layers).unwrap_err().contains("feeder layers"));
    let mut wrong_count = checkpoint();
    wrong_count.feeder_layers = 3;
    assert!(admit(&wrong_count).is_err());
    let mut no_proof = checkpoint();
    no_proof.proof = empty_proof();
    assert!(admit(&no_proof)
        .unwrap_err()
        .contains("reduced-machine family"));
}

#[test]
fn feeder_profile_selection_uses_the_c_chunk_boundary() {
    let c = UnrolledCircuitType::Unified22.get_domain_size();
    let a = UnrolledCircuitType::Unified.get_domain_size();
    for (cycles, expected) in [
        (c - 1, (FeederProfile::C, 1)),
        (c, (FeederProfile::C, 1)),
        (c + 1, (FeederProfile::A, 1)),
        (a, (FeederProfile::A, 1)),
        (a + 1, (FeederProfile::A, 2)),
    ] {
        let mut report = ScriptedChain::report(1);
        report.cycles = cycles as u64;
        report.counters.cycles = cycles;
        assert_eq!(predicted_feeder_shape(&report).unwrap(), expected);
    }
}

#[test]
fn feeder_proof_profile_requires_the_trace_and_every_instance_schedule() {
    for profile in FeederProfile::ALL {
        let proof = fake_feeder_proof_for_profile(0, 1, profile);
        assert_eq!(validate_feeder_proof(&proof, Some(1)).unwrap(), profile);
    }
    let mut proof = fake_feeder_proof_for_profile(0, 2, FeederProfile::A);
    let family = UnrolledCircuitType::Unified.get_family_idx() as u32;
    proof.riscv_proofs.get_mut(&family).unwrap()[1]
        .whir_proof
        .whir_schedule = FeederProfile::C.config().whir_schedule;
    assert!(validate_feeder_proof(&proof, None)
        .unwrap_err()
        .contains("WHIR schedule"));
    let proof = fake_feeder_proof_for_profile(0, 2, FeederProfile::C);
    assert!(validate_feeder_proof(&proof, None)
        .unwrap_err()
        .contains("C is terminal"));
    let proof = fake_feeder_proof_for_profile(0, 1, FeederProfile::A);
    assert!(l1_wrap::validate_last_feeder_proof(&proof)
        .unwrap_err()
        .contains("one C instance"));
}

#[test]
fn stale_v5_c_only_history_is_rejected_by_the_derived_trusted_chain() {
    let mut artifact = feeder_artifact(ProofTarget::L1Feeder, 6, 3);
    // Today's old chain: F1@C, rec-C@C, rec-C@C. Its internal hash is valid.
    artifact.chain_end_params[3..].copy_from_slice(&[[71; 8], [72; 8], [72; 8]]);
    let old_chain = rebuild_chain(&artifact.chain_end_params).unwrap();
    artifact.chain_hash = old_chain.hash();
    artifact.chain_preimage = old_chain.preimage();
    validate_continuation_request(&artifact, ProofTarget::L1).unwrap();
    let expected = expected_chain_end_params(
        artifact.target,
        artifact.chain_end_params.len(),
        artifact.feeder_layers,
        FeederProfile::C,
        &artifact.blake_unrolled,
        &artifact.blake_bridge,
        &artifact.blake_final,
        &mut |program| {
            Ok(match program {
                ChainProgram::Fsv(_, _, SetupMachine::L1Feeder(FeederProfile::A)) => [81; 8],
                ChainProgram::Fsv(_, _, SetupMachine::L1Feeder(FeederProfile::C)) => [82; 8],
                ChainProgram::User => [1; 8],
                ChainProgram::Fsv(FsvProgram::UnrolledBaseLayer, _, _) => [2; 8],
                _ => [3; 8],
            })
        },
    )
    .unwrap();
    let error = verify_against_chain(&artifact, &expected).unwrap_err();
    assert!(error.contains("do not match the trusted per-layer end-params"));
    assert_eq!(artifact.schema_version, ARTIFACT_SCHEMA_VERSION);
}

#[test]
fn public_feeder_artifact_requires_terminal_c() {
    let mut artifact = feeder_artifact(ProofTarget::L1Feeder, 5, 2);
    artifact.proof = fake_feeder_proof_for_profile(2, 1, FeederProfile::A);
    assert!(validate_artifact_envelope(&artifact)
        .unwrap_err()
        .contains("one C instance"));
}
