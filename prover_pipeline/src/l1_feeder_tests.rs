use super::*;

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

fn empty_proof() -> ProgramProof {
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
    finalize_artifact(
        &modes_only(compression_modes()),
        target,
        ProverBackend::Cpu,
        0,
        &program(),
        RecursionState {
            stage: target,
            l1: None,
            proof: empty_proof(),
            setups: BTreeMap::new(),
            chain_end_params: (1..=n).map(|i| [i as u32; 8]).collect(),
            input_is_base: target == ProofTarget::Base,
            timings: ProofTimingsMs::default(),
            program_cycles: 0,
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
        assert_eq!(
            registrations.len(),
            if mode == BlakeMode::Compression { 8 } else { 7 }
        );
        for (i, fsv) in L1_FEEDER_PROGRAMS.into_iter().enumerate() {
            let (bin, text) = load_fsv_program(&fsv_dir(), fsv, BlakeMode::BlakeSpecialOpcodes);
            let key = handle_key(ExecutionKind::Unified, MachineType::Reduced, &bin, &text);
            let profiles = &registrations[&key].profiles;
            let expected = if i == 0 && mode == BlakeMode::BlakeSpecialOpcodes {
                BTreeSet::from([ProofProfile::Standard, ProofProfile::L1Feeder])
            } else {
                BTreeSet::from([ProofProfile::L1Feeder])
            };
            assert_eq!(profiles, &expected);
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
        (None, L1Feeder, &[0, 1, 2, 3, 4, 5, 6, 7]),
        (None, L1, &[0, 1, 2, 3, 4, 5, 6, 7, 8]),
        (Some(Base), RecursionUnrolled, &[1, 2]),
        (Some(Base), RecursionUnified, &[1, 2, 3, 4, 5]),
        (Some(Base), L1Feeder, &[1, 2, 3, 4, 5, 6, 7]),
        (Some(Base), L1, &[1, 2, 3, 4, 5, 6, 7, 8]),
        (Some(RecursionUnrolled), RecursionUnified, &[1, 2, 3, 4, 5]),
        (Some(RecursionUnrolled), L1Feeder, &[1, 2, 3, 4, 5, 6, 7]),
        (Some(RecursionUnrolled), L1, &[1, 2, 3, 4, 5, 6, 7, 8]),
        (Some(RecursionUnified), L1Feeder, &[6, 7]),
        (Some(RecursionUnified), L1, &[6, 7, 8]),
        (Some(L1Feeder), L1, &[8]),
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
                ExecutionKind::Unified,
                ProofProfile::L1Feeder,
            ),
            (
                FsvProgram::UnifiedRecursionLayerL1Feeder,
                BlakeMode::BlakeSpecialOpcodes,
                ExecutionKind::Unified,
                ProofProfile::L1Feeder,
            ),
            (
                FsvProgram::UnifiedRecursionLayerL1Feeder,
                BlakeMode::BlakeSpecialOpcodes,
                ExecutionKind::L1Wrap,
                ProofProfile::L1Wrap,
            ),
        ] {
            let (bin, text) = load_fsv_program(&fsv_dir(), fsv, mode);
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
        },
    );
    assert_eq!(result.blake_final, checkpoint.blake_final);
    assert_eq!(result.blake_bridge, checkpoint.blake_bridge);
    assert_eq!(result.blake_unrolled, checkpoint.blake_unrolled);
}

#[test]
fn feeder_artifacts_claim_f1_and_f2_after_the_final_layer() {
    assert_eq!(
        chain_unrolled_layers(&artifact(ProofTarget::L1Feeder, 6)).unwrap(),
        1
    );
    assert!(chain_unrolled_layers(&artifact(ProofTarget::L1, 4)).is_err());
}
