use crate::{prover_utils::RecursionStrategy, vk::generate_params_for_binary, Machine};
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use execution_utils::{
    base_layer_verifier_vk, compute_chain_encoding, final_recursion_layer_verifier_vk,
    recursion_layer_no_delegation_verifier_vk, recursion_layer_verifier_vk,
    recursion_log_23_layer_verifier_vk, universal_circuit_log_23_verifier_vk,
    universal_circuit_no_delegation_verifier_vk, universal_circuit_verifier_vk,
};

pub fn generate_constants_for_binary(
    bin: &String,
    recursion_mode: &RecursionStrategy,
    universal_verifier: &bool,
    recompute: &bool,
) {
    let base_layer_bin = std::fs::read(bin).expect("Failed to read base layer binary file");

    let (end_params, aux_values) = if *universal_verifier {
        if *recompute {
            match recursion_mode {
                RecursionStrategy::UseFinalMachine => generate_params_and_register_values(
                    &[
                        (&base_layer_bin, Machine::Standard),
                        (
                            &execution_utils::UNIVERSAL_CIRCUIT_VERIFIER,
                            Machine::Reduced,
                        ),
                        (
                            &execution_utils::UNIVERSAL_CIRCUIT_NO_DELEGATION_VERIFIER,
                            Machine::ReducedFinal,
                        ),
                    ],
                    (
                        &execution_utils::UNIVERSAL_CIRCUIT_NO_DELEGATION_VERIFIER,
                        Machine::ReducedFinal,
                    ),
                ),
                RecursionStrategy::UseReducedLog23Machine => generate_params_and_register_values(
                    &[
                        (&base_layer_bin, Machine::Standard),
                        (
                            &execution_utils::UNIVERSAL_CIRCUIT_VERIFIER,
                            Machine::Reduced,
                        ),
                    ],
                    (
                        &execution_utils::UNIVERSAL_CIRCUIT_VERIFIER,
                        Machine::ReducedLog23,
                    ),
                ),
                RecursionStrategy::UseReducedLog23MachineMultiple => {
                    generate_params_and_register_values(
                        &[
                            (&base_layer_bin, Machine::Standard),
                            (
                                &execution_utils::UNIVERSAL_CIRCUIT_VERIFIER,
                                Machine::Reduced,
                            ),
                            (
                                &execution_utils::UNIVERSAL_CIRCUIT_VERIFIER,
                                Machine::ReducedLog23,
                            ),
                        ],
                        (
                            &execution_utils::UNIVERSAL_CIRCUIT_VERIFIER,
                            Machine::ReducedLog23,
                        ),
                    )
                }
                RecursionStrategy::UseReducedLog23MachineOnly => {
                    generate_params_and_register_values(
                        &[
                            (&base_layer_bin, Machine::Standard),
                            (
                                &execution_utils::UNIVERSAL_CIRCUIT_VERIFIER,
                                Machine::ReducedLog23,
                            ),
                        ],
                        (
                            &execution_utils::UNIVERSAL_CIRCUIT_VERIFIER,
                            Machine::ReducedLog23,
                        ),
                    )
                }
            }
        } else {
            let base_params = generate_params_for_binary(&base_layer_bin, Machine::Standard);

            match recursion_mode {
                RecursionStrategy::UseFinalMachine => {
                    let aux_values = compute_chain_encoding(vec![
                        [0u32; 8],
                        base_params,
                        universal_circuit_verifier_vk().params,
                        universal_circuit_no_delegation_verifier_vk().params,
                    ]);

                    (
                        universal_circuit_no_delegation_verifier_vk().params,
                        aux_values,
                    )
                }
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
        if *recompute {
            match recursion_mode {
                RecursionStrategy::UseFinalMachine => generate_params_and_register_values(
                    &[
                        (&base_layer_bin, Machine::Standard),
                        (&execution_utils::BASE_LAYER_VERIFIER, Machine::Reduced),
                        (&execution_utils::RECURSION_LAYER_VERIFIER, Machine::Reduced),
                        (
                            &execution_utils::RECURSION_LAYER_NO_DELEGATION_VERIFIER,
                            Machine::ReducedFinal,
                        ),
                    ],
                    (
                        &execution_utils::FINAL_RECURSION_LAYER_VERIFIER,
                        Machine::ReducedFinal,
                    ),
                ),
                RecursionStrategy::UseReducedLog23Machine => generate_params_and_register_values(
                    &[
                        (&base_layer_bin, Machine::Standard),
                        (&execution_utils::BASE_LAYER_VERIFIER, Machine::Reduced),
                        (&execution_utils::RECURSION_LAYER_VERIFIER, Machine::Reduced),
                    ],
                    (
                        &execution_utils::RECURSION_LAYER_VERIFIER,
                        Machine::ReducedLog23,
                    ),
                ),
                _ => panic!("This recursion strategy is not supported for non-universal verifier."),
            }
        } else {
            let base_params = generate_params_for_binary(&base_layer_bin, Machine::Standard);

            match recursion_mode {
                RecursionStrategy::UseFinalMachine => {
                    let aux_values = compute_chain_encoding(vec![
                        [0u32; 8],
                        base_params,
                        base_layer_verifier_vk().params,
                        recursion_layer_verifier_vk().params,
                        recursion_layer_no_delegation_verifier_vk().params,
                    ]);

                    (final_recursion_layer_verifier_vk().params, aux_values)
                }
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

    println!("End params: {:?}", end_params);
    println!("Aux values: {:?}", aux_values);
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
