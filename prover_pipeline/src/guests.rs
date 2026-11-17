//! Selected guests and the inputs whose executions recursion proves.

use super::{
    compression_stage, fsv_dir, CompressionProfile, CompressionRole, ProofTarget, SetupMachine,
};
use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles_for;
use full_statement_verifier::host_utils::{fsv_stream, load_fsv_exact, VerifiedFsvProgram};
use full_statement_verifier::program_proof::ProgramProof;
use prover::definitions::SoundnessMode;
use setups::Setups;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProfile, FsvProgram};

/// Loaded once, before backend initialization. Unused guests remain absent.
pub(super) struct FsvPrograms {
    unrolled_base: Option<VerifiedFsvProgram>,
    unrolled_recursion: Option<VerifiedFsvProgram>,
    bridge_base: Option<VerifiedFsvProgram>,
    bridge_recursion: Option<VerifiedFsvProgram>,
    unified: Option<VerifiedFsvProgram>,
    /// The Standard special-opcodes unified verifier used by the first compression layer.
    compression_first: Option<VerifiedFsvProgram>,
    /// Every later compression layer verifies Compression proofs (`FsvProfile::Compression`).
    compression_step: Option<VerifiedFsvProgram>,
    /// The compression statement linked for the L1 wrap ROM (`FsvProfile::CompressionFinalWrap`, linked
    /// for that ROM): the program the wrap executes over the last compression proof.
    pub(super) compression_wrap: Option<VerifiedFsvProgram>,
}

impl FsvPrograms {
    pub(super) fn load(target: ProofTarget, soundness_mode: SoundnessMode) -> Self {
        let dir = fsv_dir();
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
        let standard = FsvProfile::Standard;
        let first = compression_stage(CompressionRole::First, CompressionProfile::Step);
        let recurrent = compression_stage(CompressionRole::Recurrent, CompressionProfile::Step);
        Self {
            unrolled_base: load(
                recursion,
                FsvProgram::UnrolledBaseLayer,
                standard,
                BlakeMode::Compression,
            ),
            unrolled_recursion: load(
                recursion,
                FsvProgram::UnrolledRecursionLayer,
                standard,
                BlakeMode::Compression,
            ),
            bridge_base: load(
                unified,
                FsvProgram::UnrolledBaseLayer,
                standard,
                BlakeMode::Compression,
            ),
            bridge_recursion: load(
                unified,
                FsvProgram::UnrolledRecursionLayer,
                standard,
                BlakeMode::Compression,
            ),
            unified: load(
                unified,
                FsvProgram::UnifiedRecursionLayer,
                standard,
                BlakeMode::Compression,
            ),
            compression_first: load(
                compression,
                first.program,
                first.fsv_profile,
                BlakeMode::BlakeSpecialOpcodes,
            ),
            compression_step: load(
                compression,
                recurrent.program,
                recurrent.fsv_profile,
                BlakeMode::BlakeSpecialOpcodes,
            ),
            compression_wrap: load(
                target == ProofTarget::L1,
                FsvProgram::UnifiedRecursionLayer,
                FsvProfile::CompressionFinalWrap,
                BlakeMode::BlakeSpecialOpcodes,
            ),
        }
    }

    pub(super) fn compression_program(&self, role: CompressionRole) -> (&[u32], &[u32]) {
        let guest = match role {
            CompressionRole::First => &self.compression_first,
            CompressionRole::Recurrent => &self.compression_step,
        }
        .as_ref()
        .expect("compression guest was not loaded for this target");
        (guest.bin(), guest.text())
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
        let guest = compression
            .as_ref()
            .expect("compression guest was not loaded for this target");
        (guest.bin(), guest.text())
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
