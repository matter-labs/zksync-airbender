//! Selected guests and the inputs whose executions recursion proves.

use super::{
    compression_stage, fsv_dir, CompressionProfile, CompressionRole, PipelineBlakeModes,
    ProofTarget, SetupMachine,
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
    /// F1: the special-opcodes unified verifier proved at the compression profile (a standard
    /// registry guest).
    compression_first: ProgramWords,
    /// Every later compression layer verifies A proofs (`FsvProfile::Compression`).
    compression_step: ProgramWords,
    /// The compression statement linked for the L1 wrap ROM (`FsvProfile::CompressionFinalWrap`, words
    /// padded to that ROM): the program the wrap executes over the last compression proof.
    pub(super) compression_wrap: ProgramWords,
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
        let compression = target >= ProofTarget::Compression;
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
        // The compression programs are owned words, copied out of the loaded guests.
        let words = |guest: Option<VerifiedFsvProgram>| {
            guest.map_or_else(ProgramWords::default, |guest| {
                (guest.bin().to_vec(), guest.text().to_vec())
            })
        };
        let standard = FsvProfile::Standard;
        let first = compression_stage(CompressionRole::First, CompressionProfile::Step);
        let recurrent = compression_stage(CompressionRole::Recurrent, CompressionProfile::Step);
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
            compression_first: words(load(
                compression,
                first.program,
                first.fsv_profile,
                BlakeMode::BlakeSpecialOpcodes,
            )),
            compression_step: words(load(
                compression,
                recurrent.program,
                recurrent.fsv_profile,
                BlakeMode::BlakeSpecialOpcodes,
            )),
            compression_wrap: words(load(
                target == ProofTarget::L1,
                FsvProgram::UnifiedRecursionLayer,
                FsvProfile::CompressionFinalWrap,
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

    pub(super) fn compression_program(&self, role: CompressionRole) -> &ProgramWords {
        match role {
            CompressionRole::First => &self.compression_first,
            CompressionRole::Recurrent => &self.compression_step,
        }
    }

    /// The words of a chain program: a selected guest, or a compression program.
    pub(super) fn words(
        &self,
        program: FsvProgram,
        profile: FsvProfile,
        machine: SetupMachine,
    ) -> (&[u32], &[u32]) {
        let compression = match (program, profile, machine) {
            (
                FsvProgram::UnifiedRecursionLayer,
                FsvProfile::Standard,
                SetupMachine::Compression(_),
            ) => &self.compression_first,
            (
                FsvProgram::UnifiedRecursionLayer,
                FsvProfile::Compression,
                SetupMachine::Compression(_),
            ) => &self.compression_step,
            (_, FsvProfile::Standard, _) => {
                let guest = self.get(program, machine);
                return (guest.bin(), guest.text());
            }
            other => unreachable!("unsupported pipeline guest {other:?}"),
        };
        (&compression.0, &compression.1)
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
