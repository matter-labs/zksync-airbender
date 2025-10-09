use crate::Machine;
use crate::ProofMetadata;
use clap::ValueEnum;

/// We have two layers of recursion:
/// 1. Reduced machine (2^22 cycles) + blake delegation
/// 2. Here we have two options:
///   - Final reduced machine (2^25 cycles)
///   - Reduced log23 machine (2^23 cycles) + blake delegation
/// Note: end_params constant differs if we do 1 or multiple repetitions of the 2nd layer.
/// So we need to run the 2nd layer exactly one time or at least twice.
/// Then we can define four recursion strategies:
#[derive(Clone, Copy, Debug, ValueEnum, PartialEq, Eq)]
pub enum RecursionStrategy {
    /// Does 1st layer until 2 reduced + 1 delegation then 1 reduced 2^23 + 1 delegation (one repetition)
    UseReducedLog23Machine,
    /// Does 1st layer until N reduced + M delegation then reduced 2^23 + delegation (at least two repetitions)
    UseReducedLog23MachineMultiple,
    /// Skips 1st layer and does reduced 2^23 + delegation (at least two repetitions)
    UseReducedLog23MachineOnly,
}

impl RecursionStrategy {
    pub fn skip_first_layer(&self) -> bool {
        match self {
            RecursionStrategy::UseReducedLog23MachineOnly => true,
            _ => false,
        }
    }

    pub fn switch_to_second_recursion_layer(&self, proof_metadata: &ProofMetadata) -> bool {
        const N: usize = 5;
        const M: usize = 2;

        let continue_first_layer = match self {
            RecursionStrategy::UseReducedLog23Machine => {
                proof_metadata.reduced_proof_count > 2
                    || proof_metadata
                        .delegation_proof_count
                        .iter()
                        .any(|(_, x)| *x > 1)
            }
            RecursionStrategy::UseReducedLog23MachineMultiple => {
                proof_metadata.reduced_proof_count > N
                    || proof_metadata
                        .delegation_proof_count
                        .iter()
                        .any(|(_, x)| *x > M)
            }
            RecursionStrategy::UseReducedLog23MachineOnly => false,
        };

        !continue_first_layer
    }

    pub fn finish_second_recursion_layer(
        &self,
        proof_metadata: &ProofMetadata,
        proof_level: usize,
    ) -> bool {
        let continue_second_layer = match self {
            RecursionStrategy::UseReducedLog23Machine => {
                // In this strategy we should run only one repetition of 2nd layer
                assert!(proof_level == 0);
                assert!(proof_metadata.reduced_log_23_proof_count == 1);

                false
            }
            RecursionStrategy::UseReducedLog23MachineMultiple
            | RecursionStrategy::UseReducedLog23MachineOnly => {
                proof_metadata.reduced_log_23_proof_count > 1
                    || proof_metadata
                        .delegation_proof_count
                        .iter()
                        .any(|(_, x)| *x > 1)
                    || proof_level == 0
            }
        };

        !continue_second_layer
    }

    pub fn get_second_layer_machine(&self) -> Machine {
        Machine::ReducedLog23
    }

    #[cfg(feature = "verifier_binaries")]
    pub fn get_second_layer_binary(&self) -> Vec<u32> {
        use crate::get_padded_binary;
        match self {
            RecursionStrategy::UseReducedLog23Machine
            | RecursionStrategy::UseReducedLog23MachineMultiple
            | RecursionStrategy::UseReducedLog23MachineOnly => {
                get_padded_binary(crate::verifier_binaries::UNIVERSAL_CIRCUIT_VERIFIER)
            }
        }
    }
}
