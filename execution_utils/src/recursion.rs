use crate::verifier_binaries::{
    compute_chain_encoding, compute_end_parameters, recursion_layer_verifier_vk,
    recursion_log_23_layer_verifier_vk, universal_circuit_log_23_verifier_vk,
    universal_circuit_verifier_vk, BASE_LAYER_VERIFIER, RECURSION_LAYER_VERIFIER,
    UNIVERSAL_CIRCUIT_VERIFIER,
};
use crate::{Machine, RecursionStrategy};
use std::alloc::Global;

use verifier_common::blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;

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
                        (&UNIVERSAL_CIRCUIT_VERIFIER, Machine::Reduced),
                    ],
                    (&UNIVERSAL_CIRCUIT_VERIFIER, Machine::ReducedLog23),
                ),
                RecursionStrategy::UseReducedLog23MachineMultiple => {
                    generate_params_and_register_values(
                        &[
                            (&base_layer_bin, Machine::Standard),
                            (&UNIVERSAL_CIRCUIT_VERIFIER, Machine::Reduced),
                            (&UNIVERSAL_CIRCUIT_VERIFIER, Machine::ReducedLog23),
                        ],
                        (&UNIVERSAL_CIRCUIT_VERIFIER, Machine::ReducedLog23),
                    )
                }
                RecursionStrategy::UseReducedLog23MachineOnly => {
                    generate_params_and_register_values(
                        &[
                            (&base_layer_bin, Machine::Standard),
                            (&UNIVERSAL_CIRCUIT_VERIFIER, Machine::ReducedLog23),
                        ],
                        (&UNIVERSAL_CIRCUIT_VERIFIER, Machine::ReducedLog23),
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
                        (&BASE_LAYER_VERIFIER, Machine::Reduced),
                        (&RECURSION_LAYER_VERIFIER, Machine::Reduced),
                    ],
                    (&RECURSION_LAYER_VERIFIER, Machine::ReducedLog23),
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
        Machine::Standard => compute_end_parameters(
            expected_final_pc,
            &trace_and_split::setups::get_main_riscv_circuit_setup::<Global, Global>(
                &binary, &worker,
            ),
        ),
        Machine::Reduced => compute_end_parameters(
            expected_final_pc,
            &trace_and_split::setups::get_reduced_riscv_circuit_setup::<Global, Global>(
                &binary, &worker,
            ),
        ),
        Machine::ReducedLog23 => compute_end_parameters(
            expected_final_pc,
            &trace_and_split::setups::get_reduced_riscv_log_23_circuit_setup::<Global, Global>(
                &binary, &worker,
            ),
        ),
    }
}
