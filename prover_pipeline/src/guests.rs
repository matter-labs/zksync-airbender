//! Selected guests and the inputs whose executions recursion proves.

use super::{
    feeder_stage, fsv_dir, FeederProfile, FeederRole, PipelineBlakeModes, ProofTarget, SetupMachine,
};
use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles_for;
use full_statement_verifier::host_utils::{fsv_stream, load_fsv_exact, VerifiedFsvProgram};
use full_statement_verifier::program_proof::ProgramProof;
use prover::definitions::SoundnessMode;
use setups::Setups;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProfile, FsvProgram};

pub(super) type ProgramWords = (Vec<u32>, Vec<u32>);

/// Loaded once, before backend initialization. Unused guests remain absent.
pub(super) struct FsvPrograms {
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
    /// Every later feeder layer verifies A proofs (`FsvProfile::L1FeederA`).
    feeder_a: ProgramWords,
    /// The feeder statement linked for the L1 wrap ROM (`FsvProfile::L1FeederWrap`, words
    /// padded to that ROM): the program the wrap executes over the last feeder proof.
    pub(super) feeder_wrap: ProgramWords,
}

impl FsvPrograms {
    pub(super) fn load(
        target: ProofTarget,
        soundness_mode: SoundnessMode,
        blake: PipelineBlakeModes,
    ) -> Self {
        let dir = fsv_dir();
        let unrolled_blake = blake.unrolled;
        let bridge_blake = blake.bridge;
        let final_blake = blake.final_layer;
        let recursion = target != ProofTarget::Base;
        let unified = target >= ProofTarget::RecursionUnified;
        let feeder = target >= ProofTarget::L1Feeder;
        let load = |needed: bool, program, profile, blake| {
            needed.then(|| {
                load_fsv_exact(
                    &dir,
                    &FsvDescriptor {
                        profile,
                        ..FsvDescriptor::new(soundness_mode, program, blake)
                    },
                )
            })
        };
        // The feeder programs are owned words, copied out of the loaded guests.
        let words = |guest: Option<VerifiedFsvProgram>| {
            guest.map_or_else(ProgramWords::default, |guest| {
                (guest.bin().to_vec(), guest.text().to_vec())
            })
        };
        let standard = FsvProfile::Standard;
        let first = feeder_stage(FeederRole::First, FeederProfile::A);
        let recurrent = feeder_stage(FeederRole::Recurrent, FeederProfile::A);
        Self {
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
        }
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
    ) -> (&[u32], &[u32]) {
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
                let guest = self.get(program, machine);
                return (guest.bin(), guest.text());
            }
            other => unreachable!("unsupported pipeline guest {other:?}"),
        };
        (&feeder.0, &feeder.1)
    }

    pub(super) fn get(&self, program: FsvProgram, machine: SetupMachine) -> &VerifiedFsvProgram {
        let guest = match (program, machine) {
            (FsvProgram::UnrolledBaseLayer, SetupMachine::UnrolledReduced) => &self.unrolled_base,
            (FsvProgram::UnrolledRecursionLayer, SetupMachine::UnrolledReduced) => {
                &self.unrolled_recursion
            }
            (FsvProgram::UnrolledBaseLayer, SetupMachine::Unified) => &self.bridge_base,
            (FsvProgram::UnrolledRecursionLayer, SetupMachine::Unified) => &self.bridge_recursion,
            (FsvProgram::UnifiedRecursionLayer, SetupMachine::Unified) => &self.unified,
            other => unreachable!("unsupported pipeline guest {other:?}"),
        };
        guest
            .as_ref()
            .expect("pipeline guest was not loaded for this target")
    }
}

/// Census estimate of the selected guest's cycles on `proof`.
pub(super) fn unrolled_verifier_cost(guest: &VerifiedFsvProgram, proof: &ProgramProof) -> u64 {
    estimate_verifier_cycles_for(proof, guest.descriptor())
        .unwrap_or_else(|error| panic!("cannot estimate selected verifier cycles: {error}"))
}

/// The ND words the selected guest reads for `proof`.
pub(super) fn fsv_input(
    guest: &VerifiedFsvProgram,
    setups: &Setups,
    proof: &ProgramProof,
) -> Vec<u32> {
    fsv_stream(setups, proof, guest.descriptor())
}
