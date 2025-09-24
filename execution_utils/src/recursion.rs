use crate::{get_padded_binary, Machine, ProofMetadata, UNIVERSAL_CIRCUIT_VERIFIER};
use clap::ValueEnum;
use std::alloc::Global;

use crate::{
    compute_chain_encoding, recursion_layer_verifier_vk, recursion_log_23_layer_verifier_vk,
    universal_circuit_log_23_verifier_vk, universal_circuit_verifier_vk,
};
use verifier_common::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;

/// We have two layers of recursion:
/// 1. Reduced machine (2^22 cycles) + blake delegation
/// 2. Here we have two options:
///   - Final reduced machine (2^25 cycles) - no longer supported.
///   - Reduced log23 machine (2^23 cycles) + blake delegation
/// Note: end_params constant differs if we do 1 or multiple repetitions of the 2nd layer.
/// So we need to run the 2nd layer exactly one time or at least twice.
/// Then we can define four recursion strategies:
#[derive(Clone, Copy, Debug, ValueEnum, PartialEq, Eq)]
pub enum RecursionStrategy {
    /// UseFinalMachine is no longer supported.
    // UseFinalMachine,
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
        match self {
            RecursionStrategy::UseReducedLog23Machine
            | RecursionStrategy::UseReducedLog23MachineMultiple
            | RecursionStrategy::UseReducedLog23MachineOnly => Machine::ReducedLog23,
        }
    }

    pub fn get_second_layer_binary(&self) -> Vec<u32> {
        match self {
            RecursionStrategy::UseReducedLog23Machine
            | RecursionStrategy::UseReducedLog23MachineMultiple
            | RecursionStrategy::UseReducedLog23MachineOnly => {
                get_padded_binary(UNIVERSAL_CIRCUIT_VERIFIER)
            }
        }
    }

    pub fn use_final_machine(&self) -> bool {
        false
    }
}

pub fn generate_constants_for_binary(
    base_layer_bin: &[u8],
    recursion_mode: RecursionStrategy,
    universal_verifier: bool,
    recompute: bool,
) -> (
    [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
    [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
) {
    let (end_params, aux_values) = if universal_verifier {
        if recompute {
            match recursion_mode {
                RecursionStrategy::UseReducedLog23Machine => generate_params_and_register_values(
                    &[
                        (&base_layer_bin, Machine::Standard),
                        (&crate::UNIVERSAL_CIRCUIT_VERIFIER, Machine::Reduced),
                    ],
                    (&crate::UNIVERSAL_CIRCUIT_VERIFIER, Machine::ReducedLog23),
                ),
                RecursionStrategy::UseReducedLog23MachineMultiple => {
                    generate_params_and_register_values(
                        &[
                            (&base_layer_bin, Machine::Standard),
                            (&crate::UNIVERSAL_CIRCUIT_VERIFIER, Machine::Reduced),
                            (&crate::UNIVERSAL_CIRCUIT_VERIFIER, Machine::ReducedLog23),
                        ],
                        (&crate::UNIVERSAL_CIRCUIT_VERIFIER, Machine::ReducedLog23),
                    )
                }
                RecursionStrategy::UseReducedLog23MachineOnly => {
                    generate_params_and_register_values(
                        &[
                            (&base_layer_bin, Machine::Standard),
                            (&crate::UNIVERSAL_CIRCUIT_VERIFIER, Machine::ReducedLog23),
                        ],
                        (&crate::UNIVERSAL_CIRCUIT_VERIFIER, Machine::ReducedLog23),
                    )
                }
            }
        } else {
            let base_params = generate_params_for_binary(&base_layer_bin, Machine::Standard);

            match recursion_mode {
                RecursionStrategy::UseReducedLog23Machine => {
                    let aux_values = compute_chain_encoding(vec![
                        [0u32; 8],
                        base_params,
                        universal_circuit_verifier_vk().params,
                    ]);

                    (universal_circuit_log_23_verifier_vk().params, aux_values)
                }
                RecursionStrategy::UseReducedLog23MachineMultiple => {
                    let aux_values = compute_chain_encoding(vec![
                        [0u32; 8],
                        base_params,
                        universal_circuit_verifier_vk().params,
                        universal_circuit_log_23_verifier_vk().params,
                    ]);

                    (universal_circuit_log_23_verifier_vk().params, aux_values)
                }
                RecursionStrategy::UseReducedLog23MachineOnly => {
                    let aux_values = compute_chain_encoding(vec![
                        [0u32; 8],
                        base_params,
                        universal_circuit_log_23_verifier_vk().params,
                    ]);

                    (universal_circuit_log_23_verifier_vk().params, aux_values)
                }
            }
        }
    } else {
        if recompute {
            match recursion_mode {
                RecursionStrategy::UseReducedLog23Machine => generate_params_and_register_values(
                    &[
                        (&base_layer_bin, Machine::Standard),
                        (&crate::BASE_LAYER_VERIFIER, Machine::Reduced),
                        (&crate::RECURSION_LAYER_VERIFIER, Machine::Reduced),
                    ],
                    (&crate::RECURSION_LAYER_VERIFIER, Machine::ReducedLog23),
                ),
                _ => panic!("This recursion strategy is not supported for non-universal verifier."),
            }
        } else {
            let base_params = generate_params_for_binary(&base_layer_bin, Machine::Standard);

            match recursion_mode {
                RecursionStrategy::UseReducedLog23Machine => {
                    let aux_values = compute_chain_encoding(vec![
                        [0u32; 8],
                        base_params,
                        recursion_layer_verifier_vk().params,
                        recursion_log_23_layer_verifier_vk().params,
                    ]);

                    (recursion_log_23_layer_verifier_vk().params, aux_values)
                }
                _ => panic!("This recursion strategy is not supported for non-universal verifier."),
            }
        }
    };

    (end_params, aux_values)
}

pub fn generate_params_and_register_values(
    machines_chain: &[(&[u8], Machine)],
    last_machine: (&[u8], Machine),
) -> (
    [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
    [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
) {
    let end_params = generate_params_for_binary(last_machine.0, last_machine.1);

    let aux_registers_values = compute_commitment_for_chain_of_programs(machines_chain);
    (end_params, aux_registers_values)
}

fn compute_commitment_for_chain_of_programs(
    binaries_and_machines: &[(&[u8], Machine)],
) -> [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] {
    let mut end_params = binaries_and_machines
        .iter()
        .map(|(bin, machine)| generate_params_for_binary(bin, machine.clone()))
        .collect::<Vec<_>>();

    end_params.insert(0, [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]);

    compute_chain_encoding(end_params)
}

pub fn generate_params_for_binary(bin: &[u8], machine: Machine) -> [u32; 8] {
    let worker = verifier_common::prover::worker::Worker::new();

    let expected_final_pc = crate::find_binary_exit_point(&bin);
    let binary: Vec<u32> = crate::get_padded_binary(&bin);
    match machine {
        Machine::Standard => crate::compute_end_parameters(
            expected_final_pc,
            &trace_and_split::setups::get_main_riscv_circuit_setup::<Global, Global>(
                &binary, &worker,
            ),
        ),
        Machine::Reduced => crate::compute_end_parameters(
            expected_final_pc,
            &trace_and_split::setups::get_reduced_riscv_circuit_setup::<Global, Global>(
                &binary, &worker,
            ),
        ),
        Machine::ReducedLog23 => crate::compute_end_parameters(
            expected_final_pc,
            &trace_and_split::setups::get_reduced_riscv_log_23_circuit_setup::<Global, Global>(
                &binary, &worker,
            ),
        ),
        Machine::ReducedFinal => crate::compute_end_parameters(
            expected_final_pc,
            &trace_and_split::setups::get_final_reduced_riscv_circuit_setup::<Global, Global>(
                &binary, &worker,
            ),
        ),
    }
}
