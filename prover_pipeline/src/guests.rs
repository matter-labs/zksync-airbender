//! Selected guests and the inputs whose executions recursion proves.

use super::{
    feeder_stage, fsv_dir, FeederProfile, FeederRole, PipelineBlakeModes, ProofTarget, SetupMachine,
};
use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles_for;
use full_statement_verifier::host_utils::{
    fsv_stream, load_fsv_exact, load_l1_fsv_program, VerifiedFsvProgram,
};
use full_statement_verifier::program_proof::ProgramProof;
use prover::definitions::SoundnessMode;
use setups::Setups;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProgram};

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
    /// Every later feeder layer verifies A proofs (regular 4 MiB ROM link).
    feeder_a: ProgramWords,
    /// The same feeder statement linked for the L1 wrap ROM: the program the
    /// wrap executes over the last feeder proof.
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
        let load = |needed: bool, program, blake| {
            needed
                .then(|| load_fsv_exact(&dir, &FsvDescriptor::new(soundness_mode, program, blake)))
        };
        Self {
            unrolled_base: load(recursion, FsvProgram::UnrolledBaseLayer, unrolled_blake),
            unrolled_recursion: load(
                recursion,
                FsvProgram::UnrolledRecursionLayer,
                unrolled_blake,
            ),
            bridge_base: load(unified, FsvProgram::UnrolledBaseLayer, bridge_blake),
            bridge_recursion: load(unified, FsvProgram::UnrolledRecursionLayer, bridge_blake),
            unified: load(unified, FsvProgram::UnifiedRecursionLayer, final_blake),
            feeder_first: load(
                feeder,
                feeder_stage(FeederRole::First, FeederProfile::A).program,
                BlakeMode::BlakeSpecialOpcodes,
            )
            .map_or_else(ProgramWords::default, |guest| {
                (guest.bin().to_vec(), guest.text().to_vec())
            }),
            feeder_a: if feeder {
                load_l1_fsv_program(
                    &dir,
                    feeder_stage(FeederRole::Recurrent, FeederProfile::A).program,
                    BlakeMode::BlakeSpecialOpcodes,
                )
            } else {
                ProgramWords::default()
            },
            feeder_wrap: if feeder {
                load_l1_fsv_program(
                    &dir,
                    FsvProgram::UnifiedRecursionLayerL1FeederWrap,
                    BlakeMode::BlakeSpecialOpcodes,
                )
            } else {
                ProgramWords::default()
            },
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
    pub(super) fn words(&self, program: FsvProgram, machine: SetupMachine) -> (&[u32], &[u32]) {
        let feeder = match (program, machine) {
            (FsvProgram::UnifiedRecursionLayer, SetupMachine::L1Feeder(_)) => &self.feeder_first,
            (FsvProgram::UnifiedRecursionLayerL1FeederA, SetupMachine::L1Feeder(_)) => {
                &self.feeder_a
            }
            _ => {
                let guest = self.get(program, machine);
                return (guest.bin(), guest.text());
            }
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
