//! GPU reproductions consume only the canonical CPU manifest inventory.
use super::*;

fn checked<T: DeserializeOwned>(name: &str) -> T {
    let reference = fixture_dir();
    let manifest = validated_manifest(&reference).expect("CPU reference manifest");
    assert!(
        manifest.files.iter().any(|file| file.name == name),
        "CPU manifest omits {name}"
    );
    read_typed(&reference.join(name)).expect("CPU reference")
}

fn gpu_config(target: ProofTarget) -> ProgramProverConfig {
    ProgramProverConfig {
        target,
        backend: ProverBackend::Gpu,
        gpu_memory_preset: MemoryPreset::GiB30,
        ..config(target)
    }
}

/// Re-serialization keeps every u128 proof value exact. Only artifact backend
/// and timings differ between CPU and GPU; proof, setup and chain bytes do not.
fn compare_artifact(expected: &ProofArtifact, actual: &ProofArtifact) {
    let mut actual = actual.clone();
    actual.backend = expected.backend;
    actual.timings_ms = expected.timings_ms.clone();
    assert_eq!(
        serde_json::to_vec(expected).unwrap(),
        serde_json::to_vec(&actual).unwrap()
    );
}

impl StepCheckpoint {
    fn into_state(self) -> Result<RecursionState, String> {
        let CheckpointStep::Feeder { layer } = self.step;
        if self.fixture_schema_version != CHECKPOINT_SCHEMA_VERSION
            || self.feeder_layers != u32::from(layer) + 1
            || !(1..=MAX_FEEDER_LAYERS).contains(&self.feeder_layers)
            || self.input_is_base
            || self.chain_end_params.len() < 3 + self.feeder_layers as usize
        {
            return Err("invalid feeder checkpoint".into());
        }
        rebuild_chain(&self.chain_end_params)?;
        Ok(RecursionState {
            stage: ProofTarget::RecursionUnified,
            l1: None,
            proof: self.proof,
            setups: self.setups,
            chain_end_params: self.chain_end_params,
            input_is_base: self.input_is_base,
            timings: ProofTimingsMs::default(),
            program_cycles: self.program_cycles,
            feeder_layers: self.feeder_layers,
        })
    }
}

struct CompareLayers {
    next: u8,
}

impl FeederObserver for CompareLayers {
    fn feeder_layer(
        &mut self,
        layer: u8,
        state: &RecursionState,
        report: &FsvRunReport,
    ) -> Result<(), String> {
        assert_eq!(layer, self.next);
        self.next += 1;
        let expected_report: FsvRunReport = checked(&feeder_report_name(layer));
        assert_eq!(
            serde_json::to_vec(report).unwrap(),
            serde_json::to_vec(&expected_report).unwrap()
        );
        if validate_feeder_proof(&state.proof, None)? == FeederProfile::A {
            let expected: StepCheckpoint = checked(&feeder_checkpoint_name(layer));
            assert_eq!(
                serde_json::to_vec(&StepCheckpoint::from_state(layer, state)).unwrap(),
                serde_json::to_vec(&expected).unwrap(),
            );
        } else {
            let expected: ProofArtifact = checked("l1_feeder.json");
            assert_eq!(
                serde_json::to_vec(&(&state.proof, &state.setups, &state.chain_end_params))
                    .unwrap(),
                serde_json::to_vec(&(
                    &expected.proof,
                    &expected.setups,
                    &expected.chain_end_params
                ))
                .unwrap(),
            );
        }
        Ok(())
    }
}

fn assert_wrap(actual: &ProofArtifact) {
    verify_artifact(actual, &source()).expect("GPU feeder proof and trusted chain");
    let expected: L1Bundle = checked("l1_bundle.json");
    assert_eq!(
        serde_json::to_vec(&actual.l1.as_ref().expect("GPU wrap")).unwrap(),
        serde_json::to_vec(&expected).unwrap(),
    );
}

fn wrap(feeder: ProofArtifact) -> ProofArtifact {
    let mut prover =
        ProgramProver::for_continuation(source(), gpu_config(ProofTarget::L1), &feeder)
            .expect("GPU wrap registration");
    prover.continue_artifact(feeder).expect("GPU wrap proof")
}

#[test]
#[ignore = "proves the full program and L1 chain on the GPU"]
fn gpu_l1_reference_matches_committed() {
    deterministic_pow_required();
    let mut prover = ProgramProver::new(source(), gpu_config(ProofTarget::L1)).unwrap();
    let actual = prover.prove_words(0, vec![]).unwrap();
    assert_wrap(&actual);
}

#[test]
#[ignore = "proves every feeder layer and the wrap on the GPU"]
fn gpu_l1_feeder_chain_matches_committed() {
    deterministic_pow_required();
    let seed: ProofArtifact = checked("recursion_unified.json");
    let mut prover =
        ProgramProver::for_continuation(source(), gpu_config(ProofTarget::L1), &seed).unwrap();
    let mut observer = CompareLayers { next: 0 };
    let actual = prover
        .continue_artifact_observed(seed, &mut observer)
        .unwrap();
    assert_eq!(observer.next, 3);
    assert_wrap(&actual);
}

#[test]
#[ignore = "resumes each nonterminal CPU checkpoint and wraps on the GPU"]
fn gpu_l1_feeder_mid_chain_resume_matches_committed() {
    deterministic_pow_required();
    for layer in [0, 1] {
        let checkpoint: StepCheckpoint = checked(&feeder_checkpoint_name(layer));
        let mut prover = ProgramProver::for_feeder_checkpoint(
            source(),
            gpu_config(ProofTarget::L1Feeder),
            PipelineBlakeModes::from_env(),
        )
        .unwrap();
        let mut observer = CompareLayers { next: layer + 1 };
        let feeder = prover
            .resume_feeder_checkpoint(checkpoint.into_state().unwrap(), 0, &mut observer)
            .unwrap();
        assert_eq!(observer.next, 3);
        compare_artifact(&checked("l1_feeder.json"), &feeder);
        drop(prover);
        assert_wrap(&wrap(feeder));
    }
}

#[test]
#[ignore = "proves the feeder chain twice on the GPU and compares the CPU reference"]
fn l1_feeder_gpu_chain_gate() {
    deterministic_pow_required();
    let seed: ProofArtifact = checked("recursion_unified.json");
    let mut prover =
        ProgramProver::for_continuation(source(), gpu_config(ProofTarget::L1Feeder), &seed)
            .unwrap();
    for pass in ["cold", "warm"] {
        let mut observer = CompareLayers { next: 0 };
        let actual = prover
            .continue_artifact_observed(seed.clone(), &mut observer)
            .unwrap();
        assert_eq!(observer.next, 3, "{pass} chain");
        compare_artifact(&checked("l1_feeder.json"), &actual);
    }
}
