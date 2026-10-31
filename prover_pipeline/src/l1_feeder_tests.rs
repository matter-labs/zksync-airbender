use super::*;
use prover::definitions::{GKRExternalChallenges, ProvingSelection};
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
    FsvPrograms::load(ProofTarget::Base, ProvingSelection::default(), blake).unwrap()
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
    use ProofTarget::{Base, L1Feeder, RecursionUnified, L1};
    let cases: &[(Option<ProofTarget>, ProofTarget, &[usize])] = &[
        (None, L1, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
        (Some(Base), RecursionUnified, &[1, 2, 3, 4, 5]),
        (Some(RecursionUnified), L1Feeder, &[6, 7, 8, 9]),
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
        use BlakeMode::{BlakeSpecialOpcodes as Special, Compression};
        use ExecutionKind::{Unified, Unified22, Unrolled};
        use FsvProfile::{L1FeederA as FeederA, L1FeederWrap as FeederWrap, Standard as Std};
        use FsvProgram::{UnifiedRecursionLayer, UnrolledBaseLayer, UnrolledRecursionLayer};
        use ProofProfile::{L1Feeder as C, L1FeederA as A, L1Wrap, Standard};
        for (fsv, fsv_profile, mode, kind, profile) in [
            (UnrolledBaseLayer, Std, Compression, Unrolled, Standard),
            (UnrolledRecursionLayer, Std, Compression, Unrolled, Standard),
            (UnrolledBaseLayer, Std, Compression, Unified, Standard),
            (UnrolledRecursionLayer, Std, Compression, Unified, Standard),
            (UnifiedRecursionLayer, Std, final_mode, Unified, Standard),
            (UnifiedRecursionLayer, Std, Special, Unified22, C),
            (UnifiedRecursionLayer, FeederA, Special, Unified22, C),
            (UnifiedRecursionLayer, Std, Special, Unified, A),
            (UnifiedRecursionLayer, FeederA, Special, Unified, A),
            (
                UnifiedRecursionLayer,
                FeederWrap,
                Special,
                L1_WRAP_KIND,
                L1Wrap,
            ),
        ] {
            let descriptor = FsvDescriptor {
                profile: fsv_profile,
                ..FsvDescriptor::new(
                    prover::definitions::SecurityLevel::Sec100,
                    SoundnessMode::PessimisticConjecture,
                    fsv,
                    mode,
                )
            };
            let (bin, text) = load_fsv_exact(fsv_dir(), &descriptor)
                .unwrap_or_else(|error| panic!("{error}"))
                .into_words();
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
                        &FsvPrograms::load(target, ProvingSelection::default(), blake).unwrap(),
                    )
                    .unwrap(),
                )
                .unwrap();
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
fn feeder_artifacts_claim_their_feeder_layers_after_the_final_layer() {
    let feeder_layers = 3;
    let n = 3 + feeder_layers as usize + 1;
    assert_eq!(
        chain_unrolled_layers(&feeder_artifact(ProofTarget::L1Feeder, n, feeder_layers)).unwrap(),
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
fn expected_chain_ends_with_c_after_the_a_prefix() {
    for feeder_layers in 1..=4u32 {
        let mut programs = Vec::new();
        let expected = expected_chain_end_params(
            ProofTarget::L1Feeder,
            3 + feeder_layers as usize,
            feeder_layers,
            BlakeMode::Compression.tag(),
            BlakeMode::Compression.tag(),
            BlakeMode::Compression.tag(),
            &mut |program| {
                let entry = match program {
                    ChainProgram::Fsv(program, fsv_profile, _, SetupMachine::L1Feeder(profile)) => {
                        assert_eq!(program, FsvProgram::UnifiedRecursionLayer);
                        let role = if fsv_profile == FsvProfile::Standard {
                            10
                        } else {
                            assert_eq!(fsv_profile, FsvProfile::L1FeederA);
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
                FeederProfile::C
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

#[test]
fn terminal_c_rejects_profile_a_sized_setup_caps() {
    let family = FeederProfile::C.circuit().get_family_idx() as u32;
    let mut artifact = feeder_artifact(ProofTarget::L1Feeder, 4, 1);
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
    // A v4 artifact cannot carry an L1 target; v5 is the retired pre-rebase L1 layout.
    let mut v4_l1 = artifact(ProofTarget::L1Feeder, 4);
    v4_l1.schema_version = 4;
    let mut v5 = artifact(ProofTarget::Base, 1);
    v5.schema_version = 5;
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
            v4_l1,
            "UnsupportedArtifactTarget: schema v4 cannot carry the L1 target L1Feeder",
        ),
        (
            &missing,
            v5,
            "pre-rebase L1 artifact; unsupported; regenerate",
        ),
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
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/hashed_fibonacci");
    let source = ProgramSource::legacy_binaries_from_bin(dir.join("app_plain.bin"));
    let loaded = load_program(&source).unwrap();
    let mut artifact = feeder_artifact(ProofTarget::L1Feeder, 6, 3);
    artifact.program_bin_keccak = keccak256(&loaded.bin_bytes);
    artifact.program_text_keccak = keccak256(&loaded.text_bytes);
    validate_continuation_request(&artifact, ProofTarget::L1).unwrap();
    let error = verify_artifact_in_mode(&artifact, &source, SoundnessMode::PessimisticConjecture)
        .unwrap_err();
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
    unread: usize,
    flip_output: bool,
    calls: Rc<RefCell<(usize, usize)>>,
    proven: Rc<RefCell<usize>>,
    chain_end_params: Rc<RefCell<Vec<[u32; 8]>>>,
}

impl ScriptedChain {
    /// `instances` is indexed by absolute layer; a resumed `state` starts at
    /// its `feeder_layers`.
    fn new(state: &RecursionState, instances: &[usize]) -> Self {
        Self {
            instances: instances.to_vec(),
            unread: 0,
            flip_output: false,
            calls: Rc::default(),
            proven: Rc::new(RefCell::new(state.feeder_layers as usize)),
            chain_end_params: Rc::new(RefCell::new(state.chain_end_params.clone())),
        }
    }

    /// The verifier side of the same scripted chain.
    fn share(&self) -> Self {
        Self {
            instances: self.instances.clone(),
            unread: self.unread,
            flip_output: self.flip_output,
            calls: Rc::clone(&self.calls),
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
        Ok(L1WrapResult {
            proof: empty_gkr_proof(),
            operation_mode: execution_prover::OperationMode::SingleChunk {
                external_challenges_pow_bits: prover::gkr::prover_config::example_configs::l1_wrap_2p21::EXTERNAL_CHALLENGES_POW_BITS,
                register_final_state: [prover::definitions::FinalRegisterValue { value: 0, last_access_timestamp: 0 }; 32],
                final_pc: 4, final_timestamp: 16,
            },
        })
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

    fn predict(&self, _: &ProgramWords, nd: Vec<u32>) -> Result<FsvRunReport, String> {
        let layer = *self.proven.borrow();
        let mut report = Self::report_for(self.profile(layer), self.instances[layer]);
        // the run reproduces the input's native output: the standard output
        // for F1, the previous feeder layer's output afterwards
        if layer > 0 {
            report.output = self.native_verify(FeederProfile::A, nd)?;
        }
        report.nd_words_remaining = self.unread;
        if self.flip_output {
            report.output[0] ^= 1;
        }
        Ok(report)
    }

    fn native_verify(&self, profile: FeederProfile, nd: Vec<u32>) -> Result<[u32; 16], String> {
        if profile == FeederProfile::C {
            self.calls.borrow_mut().0 += 1;
        }
        let mut output = [0; 16];
        output[8..].copy_from_slice(&nd);
        Ok(output)
    }

    fn wrap_run(&self, _: &ProgramWords, nd: Vec<u32>) -> Result<FsvRunReport, String> {
        self.calls.borrow_mut().1 += 1;
        let mut report = Self::report(1);
        report.cycles = L1_WRAP_PROGRAM_CYCLE_LIMIT as u64 - 7;
        report.counters.cycles = report.cycles as usize;
        report.output = self.native_verify(FeederProfile::A, nd)?;
        Ok(report)
    }
}

/// Derive the authenticated chain from the proof, independently of its claimed history.
fn scripted_stream(setups: &Setups, proof: &ProgramProof) -> Vec<u32> {
    let Some(preimage) = proof.recursion_chain_preimage else {
        return vec![0; 8];
    };
    let mut chain = FsvRecursionChain::resume(preimage);
    chain.extend(&compute_end_params(setups, proof.final_pc));
    chain.hash().to_vec()
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
        &scripted_stream,
        &harness,
    );
    (result.map(|(state, _)| state), layers.0)
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
        let mut output = [0; 16];
        output[8..].copy_from_slice(&scripted_stream(&state.setups, &state.proof));
        let (fitted, _) =
            check_feeder_fit(&fsv, state, output, &scripted_stream, &harness).unwrap();
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

/// An external C proof must authenticate its claimed history before wrapping.
#[test]
fn external_feeder_rejects_a_history_its_proof_does_not_authenticate() {
    let (state, _) = run_scripted(&[1], ScriptedChain::state());
    let mut state = state.unwrap();
    let verifier = ScriptedChain::new(&state, &[1]);
    state.chain_end_params[0][0] ^= 1;
    let error = prepare_external_feeder(
        &modes_only(compression_modes()),
        state,
        &scripted_stream,
        &verifier,
    )
    .err()
    .unwrap();
    assert!(error.contains("recursion chain"), "{error}");
    assert_eq!(
        verifier.calls.borrow().1,
        0,
        "invalid history must fail before the wrap run"
    );
}

#[test]
fn in_process_feeder_wrap_verifies_c_and_runs_the_wrap_once() {
    let fsv = modes_only(compression_modes());
    let state = ScriptedChain::state();
    let mut backend = ScriptedChain::new(&state, &[2, 1, 1]);
    let verifier = backend.share();
    let mut wrapped = advance_to_target(
        &mut backend,
        &fsv,
        state,
        ProofTarget::L1,
        0,
        &mut NoopObserver,
        &scripted_stream,
        &verifier,
    )
    .unwrap();
    assert_eq!(wrapped.stage, ProofTarget::L1);
    assert_eq!(*verifier.calls.borrow(), (1, 1));
    // A separately supplied C artifact has no prepared receipt and must authenticate again.
    wrapped.stage = ProofTarget::L1Feeder;
    wrapped.l1 = None;
    advance_to_target(
        &mut backend,
        &fsv,
        wrapped,
        ProofTarget::L1,
        0,
        &mut NoopObserver,
        &scripted_stream,
        &verifier,
    )
    .unwrap();
    assert_eq!(*verifier.calls.borrow(), (2, 2));
}

/// A prediction run that leaves input unread or reproduces another output
/// is rejected before any proof is produced.
#[test]
fn feeder_loop_rejects_incomplete_or_mismatching_prediction_runs_before_proving() {
    for (unread, flip_output, needle) in [
        (3usize, false, "left 3 input words unread"),
        (0, true, "differs from the input's native output"),
    ] {
        let state = ScriptedChain::state();
        let fsv = modes_only(compression_modes());
        let mut backend = ScriptedChain::new(&state, &[4, 2, 1]);
        let mut verifier = backend.share();
        verifier.unread = unread;
        verifier.flip_output = flip_output;
        let result = run_feeder_layers(
            &mut backend,
            &fsv,
            state,
            0,
            &mut NoopObserver,
            &scripted_stream,
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
        &scripted_stream,
        &harness,
    );
    assert!(result
        .err()
        .unwrap()
        .contains("carries 3 instance(s), predicted 2"));
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
