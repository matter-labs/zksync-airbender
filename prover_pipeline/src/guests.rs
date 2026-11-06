//! Selected guests and the inputs whose executions recursion proves.

use super::{fsv_dir, ProofTarget, SetupMachine};
use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles_for;
use full_statement_verifier::host_utils::{
    bridge_blake_mode, final_blake_mode, fsv_stream, load_fsv_exact, unrolled_blake_mode,
    VerifiedFsvProgram,
};
use full_statement_verifier::program_proof::ProgramProof;
use prover::definitions::SoundnessMode;
use setups::Setups;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProgram};

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
}

impl FsvPrograms {
    pub(super) fn load(target: ProofTarget, soundness_mode: SoundnessMode) -> Self {
        let dir = fsv_dir();
        let unrolled_blake = unrolled_blake_mode();
        let bridge_blake = bridge_blake_mode();
        let final_blake = final_blake_mode();
        let recursion = target != ProofTarget::Base;
        let unified = target == ProofTarget::RecursionUnified;
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
            unrolled_blake,
            bridge_blake,
            final_blake,
        }
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
