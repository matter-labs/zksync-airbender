//! The selected, digest-verified guests and the inputs whose executions recursion proves.

use super::{feeder_stage, fsv_dir, FeederProfile, FeederRole, PipelineBlakeModes, ProofTarget, SetupMachine};
use full_statement_verifier::host_utils::{
    append_fsv_ledger, build_unified_stream, build_unrolled_stream, fsv_stream, load_fsv_exact,
    load_l1_fsv_program, measure_fsv_execution, try_native_verify_unified_in_mode,
    try_native_verify_unrolled_in_mode, VerifiedFsvProgram,
};
use full_statement_verifier::program_proof::ProgramProof;
use prover::definitions::{ProvingSelection, SoundnessMode};
use setups::Setups;
use std::path::Path;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProgram};

pub(super) type ProgramWords = (Vec<u32>, Vec<u32>);

/// Loaded once, before backend initialization. Unused guests remain absent.
pub(super) struct FsvPrograms {
    pub(super) selection: ProvingSelection,
    pub(super) unrolled_blake: BlakeMode,
    pub(super) bridge_blake: BlakeMode,
    pub(super) final_blake: BlakeMode,
    unrolled_base: Option<VerifiedFsvProgram>,
    unrolled_recursion: Option<VerifiedFsvProgram>,
    bridge_base: Option<VerifiedFsvProgram>,
    bridge_recursion: Option<VerifiedFsvProgram>,
    unified: Option<VerifiedFsvProgram>,
    /// F1: the special-opcodes unified verifier proved at the L1 feeder profile (a standard
    /// registry guest).
    feeder_first: ProgramWords,
    /// Every later feeder layer verifies A proofs (regular 4 MiB ROM link).
    feeder_a: ProgramWords,
    /// The same feeder statement linked for the L1 wrap ROM: the program the
    /// wrap executes over the last feeder proof.
    pub(super) feeder_wrap: ProgramWords,
}

impl FsvPrograms {
    pub(super) fn load(
        target: ProofTarget,
        selection: ProvingSelection,
        blake: PipelineBlakeModes,
    ) -> Result<Self, String> {
        Self::load_from_dir(
            &fsv_dir(),
            target,
            selection,
            blake.unrolled,
            blake.bridge,
            blake.final_layer,
        )
    }

    fn load_from_dir(
        dir: &Path,
        target: ProofTarget,
        selection: ProvingSelection,
        unrolled_blake: BlakeMode,
        bridge_blake: BlakeMode,
        final_blake: BlakeMode,
    ) -> Result<Self, String> {
        let recursion = target != ProofTarget::Base;
        let unified = target >= ProofTarget::RecursionUnified;
        let feeder = target >= ProofTarget::L1Feeder;
        let load = |needed: bool, program, blake| {
            if needed {
                let descriptor = FsvDescriptor::new(
                    selection.security_level,
                    selection.soundness_mode,
                    program,
                    blake,
                );
                load_fsv_exact(dir, &descriptor)
                    .map(Some)
                    .map_err(|error| error.to_string())
            } else {
                Ok(None)
            }
        };
        Ok(Self {
            selection,
            unrolled_base: load(recursion, FsvProgram::UnrolledBaseLayer, unrolled_blake)?,
            unrolled_recursion: load(
                recursion,
                FsvProgram::UnrolledRecursionLayer,
                unrolled_blake,
            )?,
            bridge_base: load(unified, FsvProgram::UnrolledBaseLayer, bridge_blake)?,
            bridge_recursion: load(unified, FsvProgram::UnrolledRecursionLayer, bridge_blake)?,
            unified: load(unified, FsvProgram::UnifiedRecursionLayer, final_blake)?,
            feeder_first: load(
                feeder,
                feeder_stage(FeederRole::First, FeederProfile::A).program,
                BlakeMode::BlakeSpecialOpcodes,
            )?
            .map_or_else(ProgramWords::default, VerifiedFsvProgram::into_words),
            feeder_a: if feeder {
                load_l1_fsv_program(
                    dir,
                    feeder_stage(FeederRole::Recurrent, FeederProfile::A).program,
                    BlakeMode::BlakeSpecialOpcodes,
                )
            } else {
                ProgramWords::default()
            },
            feeder_wrap: if feeder {
                load_l1_fsv_program(
                    dir,
                    FsvProgram::UnifiedRecursionLayerL1FeederWrap,
                    BlakeMode::BlakeSpecialOpcodes,
                )
            } else {
                ProgramWords::default()
            },
            unrolled_blake,
            bridge_blake,
            final_blake,
        })
    }

    pub(super) fn modes(&self) -> PipelineBlakeModes {
        PipelineBlakeModes {
            unrolled: self.unrolled_blake,
            bridge: self.bridge_blake,
            final_layer: self.final_blake,
        }
    }

    pub(super) fn feeder_program(&self, role: FeederRole) -> &ProgramWords {
        match role {
            FeederRole::First => &self.feeder_first,
            FeederRole::Recurrent => &self.feeder_a,
        }
    }

    /// The words of a chain program: a selected guest, or a feeder program.
    pub(super) fn words(
        &self,
        program: FsvProgram,
        machine: SetupMachine,
    ) -> Result<(&[u32], &[u32]), String> {
        let feeder = match (program, machine) {
            (FsvProgram::UnifiedRecursionLayer, SetupMachine::L1Feeder(_)) => &self.feeder_first,
            (FsvProgram::UnifiedRecursionLayerL1FeederA, SetupMachine::L1Feeder(_)) => {
                &self.feeder_a
            }
            _ => {
                let guest = self.get(program, machine)?;
                return Ok((guest.bin(), guest.text()));
            }
        };
        Ok((&feeder.0, &feeder.1))
    }

    pub(super) fn get(
        &self,
        program: FsvProgram,
        machine: SetupMachine,
    ) -> Result<&VerifiedFsvProgram, String> {
        let guest = match (program, machine) {
            (FsvProgram::UnrolledBaseLayer, SetupMachine::UnrolledReduced) => &self.unrolled_base,
            (FsvProgram::UnrolledRecursionLayer, SetupMachine::UnrolledReduced) => {
                &self.unrolled_recursion
            }
            (FsvProgram::UnrolledBaseLayer, SetupMachine::Unified) => &self.bridge_base,
            (FsvProgram::UnrolledRecursionLayer, SetupMachine::Unified) => &self.bridge_recursion,
            (FsvProgram::UnifiedRecursionLayer, SetupMachine::Unified) => &self.unified,
            other => return Err(format!("unsupported pipeline guest {other:?}")),
        };
        guest.as_ref().ok_or_else(|| {
            format!("pipeline guest {program:?}/{machine:?} was not loaded for this target")
        })
    }
}

/// A census estimate has no stream. A measured cost owns the exact input to prove next.
pub(super) struct VerifierCost {
    pub(super) cycles: u64,
    pub(super) measured_input: Option<Vec<u32>>,
}

pub(super) fn unrolled_verifier_cost(
    guest: &VerifiedFsvProgram,
    setups: &Setups,
    proof: &ProgramProof,
    label: &str,
) -> Result<VerifierCost, String> {
    match guest.descriptor().soundness_mode {
        SoundnessMode::PessimisticConjecture => {
            let cycles =
                full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles_for(
                    proof,
                    guest.descriptor(),
                )
                .map_err(|error| format!("cannot estimate selected verifier cycles: {error}"))?;
            Ok(VerifierCost {
                cycles,
                measured_input: None,
            })
        }
        SoundnessMode::EthproofsSoundnessCalc => {
            let (words, cycles) = measured_input(guest, setups, proof, label)?;
            Ok(VerifierCost {
                cycles,
                measured_input: Some(words),
            })
        }
    }
}

/// Build the input once; ethproofs execution and proving consume identical words.
pub(super) fn fsv_input(
    guest: &VerifiedFsvProgram,
    setups: &Setups,
    proof: &ProgramProof,
    label: &str,
) -> Result<Vec<u32>, String> {
    match guest.descriptor().soundness_mode {
        SoundnessMode::PessimisticConjecture => {
            fsv_stream(setups, proof, guest.descriptor()).map_err(|error| error.to_string())
        }
        SoundnessMode::EthproofsSoundnessCalc => {
            measured_input(guest, setups, proof, label).map(|(words, _)| words)
        }
    }
}

fn measured_input(
    guest: &VerifiedFsvProgram,
    setups: &Setups,
    proof: &ProgramProof,
    label: &str,
) -> Result<(Vec<u32>, u64), String> {
    let words = fsv_stream(setups, proof, guest.descriptor()).map_err(|error| error.to_string())?;
    let result = measure_fsv_execution(guest, words.clone());
    if let Some(path) = std::env::var_os("FSV_EXECUTION_LEDGER") {
        append_fsv_ledger(Path::new(&path), label, &result)
            .map_err(|error| format!("cannot append FSV execution ledger: {error}"))?;
    }
    // A guest rejection fails cost selection; there is no census fallback.
    let record = result.map_err(|error| format!("SelectedFsvExecutionFailed: {error}"))?;
    let descriptor = guest.descriptor();
    let native = match descriptor.program {
        FsvProgram::UnrolledBaseLayer | FsvProgram::UnrolledRecursionLayer => {
            try_native_verify_unrolled_in_mode(
                build_unrolled_stream(setups, proof, verifier_common::BLAKE_MODE),
                descriptor.program == FsvProgram::UnrolledBaseLayer,
                descriptor.soundness_mode,
            )
        }
        FsvProgram::UnifiedBaseLayer | FsvProgram::UnifiedRecursionLayer => {
            try_native_verify_unified_in_mode(
                build_unified_stream(setups, proof, verifier_common::BLAKE_MODE),
                descriptor.program == FsvProgram::UnifiedBaseLayer,
                descriptor.soundness_mode,
            )
        }
        FsvProgram::UnifiedRecursionLayerL1FeederWrap | FsvProgram::UnifiedRecursionLayerL1FeederA => {
            return Err(format!("SelectedFsvUnsupported: {descriptor} is not a measured pipeline guest"))
        }
    }
    .map_err(|error| format!("SelectedFsvNativeVerificationFailed: {error}"))?;
    if record.output != native {
        return Err(format!(
            "SelectedFsvOutputMismatch: {} (digest {})",
            descriptor, record.digest
        ));
    }
    log::info!(
        "selected FSV {} (digest {}, stream {}) executed {} cycles",
        descriptor,
        record.digest,
        record.stream_digest,
        record.cycles
    );
    Ok((words, record.cycles))
}

#[cfg(test)]
mod tests {
    use super::*;
    use full_statement_verifier::host_utils::{canonical_fsv_dir, fsv_manifest_entry};

    #[test]
    fn pipeline_guests_are_exactly_bound_to_selection_and_blake() {
        for &mode in SoundnessMode::ALL {
            let selection = ProvingSelection {
                soundness_mode: mode,
                ..ProvingSelection::default()
            };
            for blake in [BlakeMode::Compression, BlakeMode::BlakeSpecialOpcodes] {
                let guests = FsvPrograms::load_from_dir(
                    &canonical_fsv_dir(),
                    ProofTarget::RecursionUnified,
                    selection,
                    BlakeMode::Compression,
                    BlakeMode::Compression,
                    blake,
                )
                .unwrap();
                assert_eq!(guests.selection, selection);
                for (program, machine, expected_blake) in [
                    (
                        FsvProgram::UnrolledBaseLayer,
                        SetupMachine::UnrolledReduced,
                        BlakeMode::Compression,
                    ),
                    (
                        FsvProgram::UnrolledRecursionLayer,
                        SetupMachine::UnrolledReduced,
                        BlakeMode::Compression,
                    ),
                    (
                        FsvProgram::UnrolledBaseLayer,
                        SetupMachine::Unified,
                        BlakeMode::Compression,
                    ),
                    (
                        FsvProgram::UnrolledRecursionLayer,
                        SetupMachine::Unified,
                        BlakeMode::Compression,
                    ),
                    (
                        FsvProgram::UnifiedRecursionLayer,
                        SetupMachine::Unified,
                        blake,
                    ),
                ] {
                    let guest = guests.get(program, machine).unwrap();
                    let expected =
                        FsvDescriptor::new(selection.security_level, mode, program, expected_blake);
                    assert_eq!(*guest.descriptor(), expected);
                    assert_eq!(
                        guest.digest(),
                        fsv_manifest_entry(&expected).unwrap().digest
                    );
                }
            }
        }
    }

    #[test]
    fn missing_selected_guest_cannot_load_a_different_mode() {
        let selection = ProvingSelection {
            soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
            ..ProvingSelection::default()
        };
        let error = FsvPrograms::load_from_dir(
            Path::new("/missing/task-s-fsv"),
            ProofTarget::RecursionUnified,
            selection,
            BlakeMode::Compression,
            BlakeMode::Compression,
            BlakeMode::Compression,
        )
        .err()
        .expect("selected guest is absent");
        assert!(error.contains("ethproofs_soundcalc"), "{error}");
    }

    #[test]
    #[ignore = "requires the preserved real v3 base and unified CPU CLI artifacts"]
    fn pessimistic_pipeline_roles_match_legacy_words_and_streams() {
        use full_statement_verifier::host_utils::load_fsv_program;
        let dir =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../target/soundness-mode/v3-compat-inputs");
        let read = |name| {
            serde_json::from_reader::<_, crate::ProofArtifact>(std::io::BufReader::new(
                std::fs::File::open(dir.join(name)).unwrap(),
            ))
            .unwrap()
        };
        let base = read("base.json");
        let unified = read("recursion_unified.json");
        for final_blake in [BlakeMode::Compression, BlakeMode::BlakeSpecialOpcodes] {
            let guests = FsvPrograms::load_from_dir(
                &canonical_fsv_dir(),
                ProofTarget::RecursionUnified,
                ProvingSelection::default(),
                BlakeMode::Compression,
                BlakeMode::Compression,
                final_blake,
            )
            .unwrap();
            for (program, machine, blake, input) in [
                (
                    FsvProgram::UnrolledBaseLayer,
                    SetupMachine::UnrolledReduced,
                    BlakeMode::Compression,
                    &base,
                ),
                (
                    FsvProgram::UnrolledRecursionLayer,
                    SetupMachine::UnrolledReduced,
                    BlakeMode::Compression,
                    &base,
                ),
                (
                    FsvProgram::UnrolledBaseLayer,
                    SetupMachine::Unified,
                    BlakeMode::Compression,
                    &base,
                ),
                (
                    FsvProgram::UnrolledRecursionLayer,
                    SetupMachine::Unified,
                    BlakeMode::Compression,
                    &base,
                ),
                (
                    FsvProgram::UnifiedRecursionLayer,
                    SetupMachine::Unified,
                    final_blake,
                    &unified,
                ),
            ] {
                let guest = guests.get(program, machine).unwrap();
                let (bin, text) = load_fsv_program(canonical_fsv_dir(), program, blake);
                assert_eq!(guest.bin(), bin, "{program:?}/{machine:?}/{blake:?}");
                assert_eq!(guest.text(), text, "{program:?}/{machine:?}/{blake:?}");
                // Serializer identity only: the base payload exercises both unrolled guest roles.
                let legacy = match program {
                    FsvProgram::UnifiedRecursionLayer => {
                        build_unified_stream(&input.setups, &input.proof, blake)
                    }
                    _ => build_unrolled_stream(&input.setups, &input.proof, blake),
                };
                assert_eq!(
                    fsv_input(guest, &input.setups, &input.proof, "pessimistic-identity").unwrap(),
                    legacy,
                    "{program:?}/{machine:?}/{blake:?}"
                );
            }
        }
    }

    #[test]
    #[ignore = "requires the recovered real ethproofs base proof; executes its selected FSV"]
    fn ethproofs_switch_cost_measures_the_selected_guest_input() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/soundness-mode/ethproofs-base-recovered-v1.json");
        let bundle = program_prover::bundle::read_program_proof_bundle(
            &path,
            SoundnessMode::EthproofsSoundnessCalc,
        )
        .unwrap();
        let guest = load_fsv_exact(
            canonical_fsv_dir(),
            &FsvDescriptor::new(
                bundle.security_level,
                bundle.soundness_mode,
                FsvProgram::UnrolledBaseLayer,
                BlakeMode::Compression,
            ),
        )
        .unwrap();
        assert!(
            full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles_for(
                &bundle.proof,
                guest.descriptor()
            )
            .is_err()
        );
        let cost = unrolled_verifier_cost(
            &guest,
            &bundle.setups,
            &bundle.proof,
            "saved-ethproofs-base-cost",
        )
        .unwrap();
        assert!(cost.cycles > 0);
        assert_eq!(
            cost.measured_input.unwrap(),
            fsv_stream(&bundle.setups, &bundle.proof, guest.descriptor()).unwrap()
        );
    }
}
