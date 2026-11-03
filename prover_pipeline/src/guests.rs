//! The selected, digest-verified guests and the inputs whose executions recursion proves.

use super::{fsv_dir, ProofTarget, SetupMachine};
use full_statement_verifier::host_utils::cost_model::census::census_table;
use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles_for;
use full_statement_verifier::host_utils::{
    bridge_blake_mode, final_blake_mode, fsv_stream, load_fsv_exact, unrolled_blake_mode,
    VerifiedFsvProgram,
};
use full_statement_verifier::program_proof::ProgramProof;
use prover::definitions::ProvingSelection;
use setups::Setups;
use std::path::Path;
use std::sync::Arc;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProgram};

/// Loaded once, before backend initialization. Unused guests remain absent.
pub(super) struct FsvPrograms {
    pub(super) selection: ProvingSelection,
    pub(super) unrolled_blake: BlakeMode,
    pub(super) bridge_blake: BlakeMode,
    pub(super) final_blake: BlakeMode,
    unrolled_base: Option<Arc<VerifiedFsvProgram>>,
    unrolled_recursion: Option<Arc<VerifiedFsvProgram>>,
    bridge_base: Option<Arc<VerifiedFsvProgram>>,
    bridge_recursion: Option<Arc<VerifiedFsvProgram>>,
    unified: Option<Arc<VerifiedFsvProgram>>,
}

impl FsvPrograms {
    pub(super) fn load(target: ProofTarget, selection: ProvingSelection) -> Result<Self, String> {
        Self::load_from_dir(
            &fsv_dir(),
            target,
            selection,
            unrolled_blake_mode(),
            bridge_blake_mode(),
            final_blake_mode(),
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
        let unified = target == ProofTarget::RecursionUnified;
        let mut loaded: Vec<Arc<VerifiedFsvProgram>> = Vec::new();
        let mut load =
            |needed: bool, program, blake| -> Result<Option<Arc<VerifiedFsvProgram>>, String> {
                if !needed {
                    return Ok(None);
                }
                let descriptor = FsvDescriptor::new(
                    selection.security_level,
                    selection.soundness_mode,
                    program,
                    blake,
                );
                if let Some(guest) = loaded
                    .iter()
                    .find(|guest| *guest.descriptor() == descriptor)
                {
                    return Ok(Some(Arc::clone(guest)));
                }
                let guest =
                    Arc::new(load_fsv_exact(dir, &descriptor).map_err(|error| error.to_string())?);
                loaded.push(Arc::clone(&guest));
                Ok(Some(guest))
            };
        let programs = Self {
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
            unrolled_blake,
            bridge_blake,
            final_blake,
        };
        // The switch prices these guests; a missing table fails before any proving.
        for guest in [&programs.unrolled_base, &programs.unrolled_recursion]
            .into_iter()
            .flatten()
        {
            census_table(guest.descriptor()).map_err(|error| error.to_string())?;
        }
        Ok(programs)
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
        guest.as_deref().ok_or_else(|| {
            format!("pipeline guest {program:?}/{machine:?} was not loaded for this target")
        })
    }
}

/// Census estimate of the selected guest's cycles on `proof`, from the table of its descriptor.
pub(super) fn unrolled_verifier_cost(
    guest: &VerifiedFsvProgram,
    proof: &ProgramProof,
) -> Result<u64, String> {
    estimate_verifier_cycles_for(proof, guest.descriptor())
        .map_err(|error| format!("cannot estimate selected verifier cycles: {error}"))
}

/// The ND words the selected guest reads for `proof`: the input of the next recursion layer.
pub(super) fn fsv_input(
    guest: &VerifiedFsvProgram,
    setups: &Setups,
    proof: &ProgramProof,
) -> Result<Vec<u32>, String> {
    fsv_stream(setups, proof, guest.descriptor()).map_err(|error| error.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use full_statement_verifier::host_utils::{canonical_fsv_dir, fsv_manifest_entry};
    use prover::definitions::SoundnessMode;

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
                for program in [
                    FsvProgram::UnrolledBaseLayer,
                    FsvProgram::UnrolledRecursionLayer,
                ] {
                    assert!(std::ptr::eq(
                        guests.get(program, SetupMachine::UnrolledReduced).unwrap(),
                        guests.get(program, SetupMachine::Unified).unwrap(),
                    ));
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
        use full_statement_verifier::host_utils::{
            build_unified_stream, build_unrolled_stream, load_fsv_program,
        };
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
                    fsv_input(guest, &input.setups, &input.proof).unwrap(),
                    legacy,
                    "{program:?}/{machine:?}/{blake:?}"
                );
            }
        }
    }

    #[test]
    fn every_mode_prices_its_switch_guests_from_its_own_census() {
        for &mode in SoundnessMode::ALL {
            let selection = ProvingSelection {
                soundness_mode: mode,
                ..ProvingSelection::default()
            };
            let guests = FsvPrograms::load_from_dir(
                &canonical_fsv_dir(),
                ProofTarget::RecursionUnified,
                selection,
                unrolled_blake_mode(),
                bridge_blake_mode(),
                final_blake_mode(),
            )
            .unwrap();
            for program in [
                FsvProgram::UnrolledBaseLayer,
                FsvProgram::UnrolledRecursionLayer,
            ] {
                let descriptor = *guests
                    .get(program, SetupMachine::UnrolledReduced)
                    .unwrap()
                    .descriptor();
                assert_eq!(descriptor.soundness_mode, mode);
                census_table(&descriptor).unwrap_or_else(|error| panic!("{error}"));
            }
        }
    }

    #[test]
    #[ignore = "requires the recovered real ethproofs base proof; executes its selected FSV"]
    fn ethproofs_switch_estimate_matches_the_executed_guest() {
        use full_statement_verifier::host_utils::cost_model::proof_counts;
        use full_statement_verifier::host_utils::measure_fsv_execution;
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
        let estimate = unrolled_verifier_cost(&guest, &bundle.proof).unwrap();
        let words = fsv_input(&guest, &bundle.setups, &bundle.proof).unwrap();
        let measured = measure_fsv_execution(&guest, words).unwrap().cycles;
        // The census acceptance budget of the total row (`tests/trace/calibrate.rs`).
        let table = census_table(guest.descriptor()).unwrap();
        let proofs: u64 = proof_counts(&bundle.proof)
            .iter()
            .map(|(_, n)| *n as u64)
            .sum();
        let spread = proofs * table.per_proof_spread[table.per_proof_spread.len() - 1];
        let budget = measured.saturating_sub(spread) / 2000 + spread;
        assert!(
            estimate.abs_diff(measured) <= budget,
            "estimate {estimate} vs measured {measured}: budget {budget}"
        );
    }
}
