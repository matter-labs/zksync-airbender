//! The selected, digest-verified guests and the inputs whose executions recursion proves.

use super::{
    feeder_stage, fsv_dir, FeederProfile, FeederRole, PipelineBlakeModes, ProofTarget, SetupMachine,
};
use full_statement_verifier::host_utils::cost_model::census::census_table;
use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles_for;
use full_statement_verifier::host_utils::{fsv_stream, load_fsv_exact, VerifiedFsvProgram};
use full_statement_verifier::program_proof::ProgramProof;
use prover::definitions::ProvingSelection;
use setups::Setups;
use std::path::Path;
use std::sync::Arc;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProfile, FsvProgram};

pub(super) type ProgramWords = (Vec<u32>, Vec<u32>);

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
    /// F1: the special-opcodes unified verifier proved at the L1 feeder profile (a standard
    /// registry guest).
    feeder_first: ProgramWords,
    /// Every later feeder layer verifies A proofs (`FsvProfile::L1FeederA`).
    feeder_a: ProgramWords,
    /// The feeder statement linked for the L1 wrap ROM (`FsvProfile::L1FeederWrap`, words
    /// padded to that ROM): the program the wrap executes over the last feeder proof.
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
        let mut loaded: Vec<Arc<VerifiedFsvProgram>> = Vec::new();
        let mut load = |needed: bool, program, profile, blake| -> Option<Arc<VerifiedFsvProgram>> {
            if !needed {
                return None;
            }
            let descriptor = FsvDescriptor {
                profile,
                ..FsvDescriptor::new(
                    selection.security_level,
                    selection.soundness_mode,
                    program,
                    blake,
                )
            };
            if let Some(guest) = loaded
                .iter()
                .find(|guest| *guest.descriptor() == descriptor)
            {
                return Some(Arc::clone(guest));
            }
            let guest = Arc::new(load_fsv_exact(dir, &descriptor));
            loaded.push(Arc::clone(&guest));
            Some(guest)
        };
        // The feeder programs are owned words, copied out of the shared guests.
        let words = |guest: Option<Arc<VerifiedFsvProgram>>| {
            guest.map_or_else(ProgramWords::default, |guest| {
                (guest.bin().to_vec(), guest.text().to_vec())
            })
        };
        let standard = FsvProfile::Standard;
        let first = feeder_stage(FeederRole::First, FeederProfile::A);
        let recurrent = feeder_stage(FeederRole::Recurrent, FeederProfile::A);
        let programs = Self {
            selection,
            unrolled_base: load(
                recursion,
                FsvProgram::UnrolledBaseLayer,
                standard,
                unrolled_blake,
            ),
            unrolled_recursion: load(
                recursion,
                FsvProgram::UnrolledRecursionLayer,
                standard,
                unrolled_blake,
            ),
            bridge_base: load(
                unified,
                FsvProgram::UnrolledBaseLayer,
                standard,
                bridge_blake,
            ),
            bridge_recursion: load(
                unified,
                FsvProgram::UnrolledRecursionLayer,
                standard,
                bridge_blake,
            ),
            unified: load(
                unified,
                FsvProgram::UnifiedRecursionLayer,
                standard,
                final_blake,
            ),
            feeder_first: words(load(
                feeder,
                first.program,
                first.fsv_profile,
                BlakeMode::BlakeSpecialOpcodes,
            )),
            feeder_a: words(load(
                feeder,
                recurrent.program,
                recurrent.fsv_profile,
                BlakeMode::BlakeSpecialOpcodes,
            )),
            feeder_wrap: words(load(
                feeder,
                FsvProgram::UnifiedRecursionLayer,
                FsvProfile::L1FeederWrap,
                BlakeMode::BlakeSpecialOpcodes,
            )),
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
        profile: FsvProfile,
        machine: SetupMachine,
    ) -> Result<(&[u32], &[u32]), String> {
        let feeder = match (program, profile, machine) {
            (
                FsvProgram::UnifiedRecursionLayer,
                FsvProfile::Standard,
                SetupMachine::L1Feeder(_),
            ) => &self.feeder_first,
            (
                FsvProgram::UnifiedRecursionLayer,
                FsvProfile::L1FeederA,
                SetupMachine::L1Feeder(_),
            ) => &self.feeder_a,
            (_, FsvProfile::Standard, _) => {
                let guest = self.get(program, machine)?;
                return Ok((guest.bin(), guest.text()));
            }
            other => return Err(format!("unsupported pipeline guest {other:?}")),
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
    use full_statement_verifier::host_utils::{
        bridge_blake_mode, canonical_fsv_dir, final_blake_mode, fsv_manifest_entry,
        unrolled_blake_mode,
    };
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
                    assert_eq!(guest.digest(), fsv_manifest_entry(&expected).digest);
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
    #[should_panic(
        expected = "MissingArtifact: missing full-statement verifier sec_100/ethproofs_soundcalc/unrolled_base_layer/standard/blake2_with_compression at /missing/fsv/"
    )]
    fn missing_selected_guest_cannot_load_a_different_mode() {
        let selection = ProvingSelection {
            soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
            ..ProvingSelection::default()
        };
        let _ = FsvPrograms::load_from_dir(
            Path::new("/missing/fsv"),
            ProofTarget::RecursionUnified,
            selection,
            BlakeMode::Compression,
            BlakeMode::Compression,
            BlakeMode::Compression,
        );
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
}
