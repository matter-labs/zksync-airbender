#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(array_chunks)]
#![feature(allocator_api)]

use std::collections::BTreeMap;

use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use risc_v_simulator::cycle::MachineConfig;
use serde::{Deserialize, Serialize};
use trace_and_split::FinalRegisterValue;
use verifier_common::cs::utils::split_timestamp;
use verifier_common::prover::definitions::MerkleTreeCap;
use verifier_common::prover::fft::GoodAllocator;
use verifier_common::prover::prover_stages::{flatten_merkle_caps, Proof};
use verifier_common::transcript::Blake2sBufferingTranscript;

mod constants;

use self::constants::*;

// pub const RUN_VERIFIERS_WITH_OUTPUT: bool = false;
pub const RUN_VERIFIERS_WITH_OUTPUT: bool = true;

pub const BASE_PROGRAM: &[u8] = include_bytes!("../../examples/hashed_fibonacci/app.bin");
pub const BASE_PROGRAM_TEXT_SECTION: &[u8] =
    include_bytes!("../../examples/hashed_fibonacci/app.text");

pub const BASE_LAYER_VERIFIER: &[u8] = include_bytes!("../../tools/verifier/base_layer.bin");
pub const RECURSION_LAYER_VERIFIER: &[u8] =
    include_bytes!("../../tools/verifier/recursion_layer.bin");
pub const RECURSION_LAYER_NO_DELEGATION_VERIFIER: &[u8] =
    include_bytes!("../../tools/verifier/recursion_layer_no_delegation.bin");
pub const FINAL_RECURSION_LAYER_VERIFIER: &[u8] =
    include_bytes!("../../tools/verifier/final_recursion_layer.bin");

pub const BASE_LAYER_VERIFIER_WITH_OUTPUT: &[u8] =
    include_bytes!("../../tools/verifier/base_layer_with_output.bin");
pub const RECURSION_LAYER_VERIFIER_WITH_OUTPUT: &[u8] =
    include_bytes!("../../tools/verifier/recursion_layer_with_output.bin");
pub const RECURSION_LAYER_NO_DELEGATION_VERIFIER_WITH_OUTPUT: &[u8] =
    include_bytes!("../../tools/verifier/recursion_layer_no_delegation_with_output.bin");
pub const FINAL_RECURSION_LAYER_VERIFIER_WITH_OUTPUT: &[u8] =
    include_bytes!("../../tools/verifier/final_recursion_layer_with_output.bin");

pub const UNIVERSAL_CIRCUIT_VERIFIER: &[u8] = include_bytes!("../../tools/verifier/universal.bin");

pub const UNIVERSAL_CIRCUIT_NO_DELEGATION_VERIFIER: &[u8] =
    include_bytes!("../../tools/verifier/universal_no_delegation.bin");

// Methods to fetch the verification keys for the binaries above.
// They are usually refreshed with build_vk.sh
pub fn recursion_layer_verifier_vk() -> VerificationKey {
    serde_json::from_slice::<VerificationKey>(include_bytes!(
        "../../tools/verifier/recursion_layer.reduced.vk.json"
    ))
    .unwrap()
}

pub fn recursion_layer_no_delegation_verifier_vk() -> VerificationKey {
    serde_json::from_slice::<VerificationKey>(include_bytes!(
        "../../tools/verifier/recursion_layer_no_delegation.final.vk.json"
    ))
    .unwrap()
}

pub fn final_recursion_layer_verifier_vk() -> VerificationKey {
    serde_json::from_slice::<VerificationKey>(include_bytes!(
        "../../tools/verifier/final_recursion_layer.final.vk.json"
    ))
    .unwrap()
}

pub fn universal_circuit_verifier_vk() -> VerificationKey {
    serde_json::from_slice::<VerificationKey>(include_bytes!(
        "../../tools/verifier/universal.reduced.vk.json"
    ))
    .unwrap()
}

pub fn universal_circuit_no_delegation_verifier_vk() -> VerificationKey {
    serde_json::from_slice::<VerificationKey>(include_bytes!(
        "../../tools/verifier/universal_no_delegation.final.vk.json"
    ))
    .unwrap()
}

pub fn get_padded_binary(binary: &[u8]) -> Vec<u32> {
    let mut bytecode = binary
        .array_chunks::<4>()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    trace_and_split::setups::pad_bytecode_for_proving(&mut bytecode);

    bytecode
}

pub const BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS: &[(
    u32,
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
)] = &[
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[0].0,
        &ALL_DELEGATION_CIRCUITS_PARAMS[0].2,
    ),
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[1].0,
        &ALL_DELEGATION_CIRCUITS_PARAMS[1].2,
    ),
];

pub const RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS: &[(
    u32,
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
)] = &[(
    ALL_DELEGATION_CIRCUITS_PARAMS[0].0,
    &ALL_DELEGATION_CIRCUITS_PARAMS[0].2,
)];

pub const FINAL_RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS: &[(
    u32,
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
)] = &[];

pub const EXIT_SEQUENCE: &[u32] = &[
    0x000d2503, //	lw	a0, 0x0(s10)
    0x004d2583, //	lw	a1, 0x4(s10)
    0x008d2603, //	lw	a2, 0x8(s10)
    0x00cd2683, //	lw	a3, 0xc(s10)
    0x010d2703, //	lw	a4, 0x10(s10)
    0x014d2783, //	lw	a5, 0x14(s10)
    0x018d2803, //	lw	a6, 0x18(s10)
    0x01cd2883, //	lw	a7, 0x1c(s10)
    0x020d2903, //	lw	s2, 0x20(s10)
    0x024d2983, //	lw	s3, 0x24(s10)
    0x028d2a03, //	lw	s4, 0x28(s10)
    0x02cd2a83, //	lw	s5, 0x2c(s10)
    0x030d2b03, //	lw	s6, 0x30(s10)
    0x034d2b83, //	lw	s7, 0x34(s10)
    0x038d2c03, //	lw	s8, 0x38(s10)
    0x03cd2c83, //	lw	s9, 0x3c(s10)
    0x0000006f, //	loop
];

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct ProgramProof {
    pub base_layer_proofs: Vec<Proof>,
    pub delegation_proofs: BTreeMap<u32, Vec<Proof>>,
    pub register_final_values: Vec<FinalRegisterValue>,
    pub end_params: [u32; 8],
    pub recursion_chain_preimage: Option<[u32; 16]>,
    pub recursion_chain_hash: Option<[u32; 8]>,
}

impl ProgramProof {
    pub fn get_num_delegation_proofs_for_type(&self, delegation_type: u32) -> u32 {
        if let Some(proofs) = self.delegation_proofs.get(&delegation_type) {
            proofs.len() as u32
        } else {
            0
        }
    }

    pub fn flatten_for_delegation_circuits_set(
        &self,
        allowed_delegation_circuits: &[u32],
    ) -> Vec<u32> {
        let mut responses = Vec::with_capacity(32 + 32 * 2);

        assert_eq!(self.register_final_values.len(), 32);
        // registers
        for final_values in self.register_final_values.iter() {
            responses.push(final_values.value);
            let (low, high) = split_timestamp(final_values.last_access_timestamp);
            responses.push(low);
            responses.push(high);
        }

        // basic ones
        responses.push(self.base_layer_proofs.len() as u32);
        for proof in self.base_layer_proofs.iter() {
            let t = verifier_common::proof_flattener::flatten_full_proof(proof, true);
            responses.extend(t);
        }
        // then for every allowed delegation circuit
        for delegation_type in allowed_delegation_circuits.iter() {
            if let Some(proofs) = self.delegation_proofs.get(&delegation_type) {
                responses.push(proofs.len() as u32);
                for proof in proofs.iter() {
                    let t = verifier_common::proof_flattener::flatten_full_proof(proof, false);
                    responses.extend(t);
                }
            } else {
                responses.push(0);
            }
        }

        if let Some(preimage) = self.recursion_chain_preimage {
            responses.extend(preimage);
        }

        // check that we didn't have unexpected ones
        for t in self.delegation_proofs.keys() {
            assert!(
                allowed_delegation_circuits.contains(t),
                "allowed set of delegation circuits {:?} doesn't contain circuit type {}",
                allowed_delegation_circuits,
                t
            );
        }

        responses
    }
}

/// VerificationKey represents the verification key for a specific machine type and bytecode hash.
#[derive(Serialize, Deserialize, Debug)]
pub struct VerificationKey {
    /// Type of the machine (standard, reduced, final)
    pub machine_type: String,
    /// Keccak of the bytecode
    pub bytecode_hash_hex: String,
    /// Verification key (a.k.a params that are used in the verifier)
    pub params: [u32; 8],
    /// Same as above, but in a single hex format (for easier debugging)
    pub params_hex: String,
}

pub fn run_verifier_binary(binary: &[u8], reads: Vec<u32>) -> Option<[u32; 16]> {
    use risc_v_simulator::cycle::IMIsaConfigWithAllDelegations;

    let final_pc = find_binary_exit_point(binary);
    println!("Expected final PC = 0x{:08x}", final_pc);

    let source = QuasiUARTSource::new_with_reads(reads);

    let final_state = risc_v_simulator::runner::run_simple_for_num_cycles::<
        _,
        IMIsaConfigWithAllDelegations,
    >(binary, 0, 1 << 30, source);

    if final_state.pc != final_pc {
        println!(
            "Execution ended on the unexpected PC: was expecting 0x{:08x}, but ended at {:08x}",
            final_pc, final_state.pc
        );
        return None;
    }

    // our convention is to return 32 bytes placed into registers x10-x26

    let regs = final_state.registers[10..26].try_into().unwrap();

    Some(regs)
}

pub fn find_binary_exit_point(binary: &[u8]) -> u32 {
    assert!(binary.len() % 4 == 0);

    let binary: Vec<u32> = binary
        .array_chunks::<4>()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let mut candidates = vec![];

    for (start_offset, window) in binary.windows(EXIT_SEQUENCE.len()).enumerate() {
        if window == EXIT_SEQUENCE {
            candidates.push(start_offset);
        }
    }

    assert_eq!(candidates.len(), 1, "too many candidates for exit sequence");
    let start = candidates[0];
    let final_pc = (start + EXIT_SEQUENCE.len() - 1) * core::mem::size_of::<u32>();

    final_pc as u32
}

pub fn verify_base_layer(full_proof: &ProgramProof) -> bool {
    println!("Verifying base layer proof using RISC-V simulator and the verifier program");
    let allowed_delegation_types: Vec<_> = BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS
        .iter()
        .map(|el| el.0)
        .collect();
    let responses = full_proof.flatten_for_delegation_circuits_set(&allowed_delegation_types);
    let binary = if RUN_VERIFIERS_WITH_OUTPUT {
        BASE_LAYER_VERIFIER_WITH_OUTPUT
    } else {
        BASE_LAYER_VERIFIER
    };

    run_verifier_binary(binary, responses).is_some()
}

pub fn verify_recursion_layer(full_proof: &ProgramProof) -> bool {
    println!("Verifying recursion layer proof using RISC-V simulator and the verifier program");
    let allowed_delegation_types: Vec<_> = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS
        .iter()
        .map(|el| el.0)
        .collect();
    let responses = full_proof.flatten_for_delegation_circuits_set(&allowed_delegation_types);
    let binary = if RUN_VERIFIERS_WITH_OUTPUT {
        RECURSION_LAYER_VERIFIER_WITH_OUTPUT
    } else {
        RECURSION_LAYER_VERIFIER
    };

    run_verifier_binary(binary, responses).is_some()
}

pub fn verify_final_recursion_layer(full_proof: &ProgramProof) -> bool {
    println!(
        "Verifying final recursion layer proof using RISC-V simulator and the verifier program"
    );
    let allowed_delegation_types: Vec<_> = FINAL_RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS
        .iter()
        .map(|el| el.0)
        .collect();
    let responses = full_proof.flatten_for_delegation_circuits_set(&allowed_delegation_types);
    let binary = if RUN_VERIFIERS_WITH_OUTPUT {
        FINAL_RECURSION_LAYER_VERIFIER_WITH_OUTPUT
    } else {
        FINAL_RECURSION_LAYER_VERIFIER
    };

    run_verifier_binary(binary, responses).is_some()
}

pub fn compute_end_parameters<C: MachineConfig, A: GoodAllocator>(
    expected_final_pc: u32,
    setup: &trace_and_split::setups::MainCircuitPrecomputations<C, A, impl GoodAllocator>,
) -> [u32; 8] {
    let mut result_hasher = Blake2sBufferingTranscript::new();
    result_hasher.absorb(&[expected_final_pc]);

    let caps = flatten_merkle_caps(&setup.setup.trees);
    result_hasher.absorb(&caps);
    let end_params_output = result_hasher.finalize_reset();

    end_params_output.0
}

pub fn create_initial_chain_encoding_encoding(
    base_layer_end_params: &[u32; 8],
) -> ([u32; 16], [u32; 8]) {
    let mut chain_hasher = Blake2sBufferingTranscript::new();
    let mut preimage = [0u32; 16];
    preimage[8..].copy_from_slice(base_layer_end_params);
    chain_hasher.absorb(&preimage);
    let new_chain = chain_hasher.finalize_reset();

    (preimage, new_chain.0)
}

pub fn continue_chain_encoding(
    previous_chain_hash: &[u32; 8],
    previous_chain_preimage: &[u32; 16],
    verifier_step_end_parameters: &[u32; 8],
) -> ([u32; 16], [u32; 8]) {
    if &previous_chain_preimage[8..] == &verifier_step_end_parameters[..] {
        // we chain the same circuit, so we do not need to chain further
        (*previous_chain_preimage, *previous_chain_hash)
    } else {
        // we should continue the chain
        let mut chain_hasher = Blake2sBufferingTranscript::new();
        let mut preimage = [0u32; 16];
        preimage[..8].copy_from_slice(previous_chain_hash);
        preimage[8..].copy_from_slice(verifier_step_end_parameters);
        chain_hasher.absorb(&preimage);
        let new_chain = chain_hasher.finalize_reset();

        (preimage, new_chain.0)
    }
}

pub fn compute_chain_encoding(data: Vec<[u32; 8]>) -> [u32; 8] {
    let mut hasher = Blake2sBufferingTranscript::new();
    let mut previous = data[0];

    for index in 1..data.len() {
        // continue the chain, only if the data is different
        if data[index] != data[index - 1] {
            hasher.absorb(&previous);
            hasher.absorb(&data[index]);
            previous = hasher.finalize_reset().0;
        }
    }

    previous
}

#[cfg(test)]
mod test {
    use risc_v_simulator::cycle::IMStandardIsaConfig;
    use std::alloc::Global;
    use std::io::Read;
    use verifier_common::cs::machine::Machine;
    use verifier_common::field::Mersenne31Field;
    use verifier_common::prover;

    use super::*;

    fn run_on_binary(path: &str) -> u32 {
        let mut data = vec![];
        let mut file = std::fs::File::open(path).unwrap();
        file.read_to_end(&mut data).unwrap();

        find_binary_exit_point(&data)
    }

    #[test]
    fn test_binaries() {
        run_on_binary("../tools/verifier/base_layer.bin");
        run_on_binary("../tools/verifier/recursion_layer.bin");
        run_on_binary("../tools/verifier/base_layer_with_output.bin");
        run_on_binary("../tools/verifier/recursion_layer_with_output.bin");
        run_on_binary("../tools/verifier/individual.bin");
    }

    #[test]
    fn test_prove_fib() {
        let binary = BASE_PROGRAM;
        let text_section = BASE_PROGRAM_TEXT_SECTION;
        assert!(text_section.len() % 4 == 0);
        let text_section: Vec<u32> = text_section
            .array_chunks::<4>()
            .map(|el| u32::from_le_bytes(*el))
            .collect();

        // let unsupported_opcodes = <prover::cs::machine::machine_configurations::full_isa_with_delegation_no_exceptions::FullIsaMachineWithDelegationNoExceptionHandling as Machine<Mersenne31Field>>::verify_bytecode_base(&text_section);
        let unsupported_opcodes = <prover::cs::machine::machine_configurations::full_isa_with_delegation_no_exceptions_no_signed_mul_div::FullIsaMachineWithDelegationNoExceptionHandlingNoSignedMulDiv as Machine<Mersenne31Field>>::verify_bytecode_base(&text_section);
        // let unsupported_opcodes = <prover::cs::machine::machine_configurations::minimal_no_exceptions_with_delegation::MinimalMachineNoExceptionHandlingWithDelegation as Machine<Mersenne31Field>>::verify_bytecode_base(&text_section);
        for (pc, opcode) in unsupported_opcodes {
            println!(
                "Potentially unsupported opcode 0x{:08x} at PC = 0x{:08x}",
                opcode, pc
            );
        }

        let worker = prover::worker::Worker::new_with_num_threads(8);

        let delegation_precomputations =
            trace_and_split::setups::all_delegation_circuits_precomputations::<Global, Global>(
                &worker,
            );

        let expected_final_pc = find_binary_exit_point(&binary);
        println!(
            "Expected final PC for base program is 0x{:08x}",
            expected_final_pc
        );

        let binary = get_padded_binary(&binary);

        let main_circuit_precomputations = trace_and_split::setups::get_main_riscv_circuit_setup::<
            Global,
            Global,
        >(&binary, &worker);

        let end_params = compute_end_parameters(expected_final_pc, &main_circuit_precomputations);

        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![123, 10]);

        let (main_proofs, delegation_proofs, register_values) =
            prover_examples::prove_image_execution(
                10,
                &binary,
                non_determinism_source,
                &main_circuit_precomputations,
                &delegation_precomputations,
                &worker,
            );

        let total_delegation_proofs: usize = delegation_proofs.iter().map(|(_, x)| x.len()).sum();

        println!(
            "Created {} basic proofs and {} delegation proofs.",
            main_proofs.len(),
            total_delegation_proofs
        );

        let mut proofs_map = BTreeMap::new();
        for (delegation_type, proofs) in delegation_proofs.into_iter() {
            proofs_map.insert(delegation_type, proofs);
        }

        // base layer proofs know nothing about further recursion

        let program_proof = ProgramProof {
            base_layer_proofs: main_proofs,
            delegation_proofs: proofs_map,
            register_final_values: register_values,
            end_params,
            recursion_chain_preimage: None,
            recursion_chain_hash: None,
        };

        let is_valid = verify_base_layer(&program_proof);

        assert!(is_valid);

        let mut dst = std::fs::File::create("base_layer.json").unwrap();
        serde_json::to_writer_pretty(&mut dst, &program_proof).unwrap();
    }

    #[test]
    fn test_prove_recursion_over_base() {
        let worker = prover::worker::Worker::new_with_num_threads(8);

        let delegation_precomputations =
            trace_and_split::setups::all_delegation_circuits_precomputations::<Global, Global>(
                &worker,
            );

        let binary = BASE_LAYER_VERIFIER;

        let expected_final_pc = find_binary_exit_point(&binary);
        println!(
            "Expected final PC for recursion program is 0x{:08x}",
            expected_final_pc
        );

        let binary = get_padded_binary(&binary);

        let mut src = std::fs::File::open("base_layer.json").unwrap();
        let proofs: ProgramProof = serde_json::from_reader(&mut src).unwrap();

        dbg!(proofs.end_params);
        dbg!(proofs.recursion_chain_hash);
        dbg!(proofs.recursion_chain_preimage);

        let main_circuit_precomputations = trace_and_split::setups::get_reduced_riscv_circuit_setup::<
            Global,
            Global,
        >(&binary, &worker);

        let base_layer_verifier_end_params =
            compute_end_parameters(expected_final_pc, &main_circuit_precomputations);
        let (preimage, chain_hash) = create_initial_chain_encoding_encoding(&proofs.end_params);

        dbg!(base_layer_verifier_end_params);
        dbg!(preimage);
        dbg!(chain_hash);

        let allowed_delegations: Vec<_> = BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS
            .iter()
            .map(|el| el.0)
            .collect();
        let non_determinism_source = QuasiUARTSource::new_with_reads(
            proofs.flatten_for_delegation_circuits_set(&allowed_delegations),
        );

        let (main_proofs, delegation_proofs, register_values) =
            prover_examples::prove_image_execution_on_reduced_machine(
                10,
                &binary,
                non_determinism_source,
                &main_circuit_precomputations,
                &delegation_precomputations,
                &worker,
            );

        let total_delegation_proofs: usize = delegation_proofs.iter().map(|(_, x)| x.len()).sum();

        println!(
            "Created {} basic proofs and {} delegation proofs.",
            main_proofs.len(),
            total_delegation_proofs
        );

        let mut proofs_map = BTreeMap::new();
        for (delegation_type, proofs) in delegation_proofs.into_iter() {
            proofs_map.insert(delegation_type, proofs);
        }

        let program_proof = ProgramProof {
            base_layer_proofs: main_proofs,
            delegation_proofs: proofs_map,
            register_final_values: register_values,
            end_params: base_layer_verifier_end_params,
            recursion_chain_preimage: Some(preimage),
            recursion_chain_hash: Some(chain_hash),
        };

        let mut dst = std::fs::File::create("recursion_layer.json").unwrap();
        serde_json::to_writer_pretty(&mut dst, &program_proof).unwrap();

        let is_valid = verify_recursion_layer(&program_proof);
        assert!(is_valid);
    }

    #[test]
    fn test_prove_recursion_over_recursion() {
        let worker = prover::worker::Worker::new_with_num_threads(8);

        let delegation_precomputations =
            trace_and_split::setups::all_delegation_circuits_precomputations::<Global, Global>(
                &worker,
            );

        let binary = RECURSION_LAYER_VERIFIER;

        let expected_final_pc = find_binary_exit_point(&binary);
        println!(
            "Expected final PC for recursion program is 0x{:08x}",
            expected_final_pc
        );

        let binary = get_padded_binary(&binary);

        let mut src = std::fs::File::open("recursion_layer.json").unwrap();
        let proofs: ProgramProof = serde_json::from_reader(&mut src).unwrap();

        dbg!(proofs.end_params);
        dbg!(proofs.recursion_chain_hash);
        dbg!(proofs.recursion_chain_preimage);

        let main_circuit_precomputations = trace_and_split::setups::get_reduced_riscv_circuit_setup::<
            Global,
            Global,
        >(&binary, &worker);

        let new_end_params =
            compute_end_parameters(expected_final_pc, &main_circuit_precomputations);
        let (preimage, chain_hash) = continue_chain_encoding(
            &proofs.recursion_chain_hash.unwrap(),
            &proofs.recursion_chain_preimage.unwrap(),
            &proofs.end_params,
        );

        dbg!(new_end_params);
        dbg!(preimage);
        dbg!(chain_hash);

        let allowed_delegations: Vec<_> = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS
            .iter()
            .map(|el| el.0)
            .collect();
        let non_determinism_source = QuasiUARTSource::new_with_reads(
            proofs.flatten_for_delegation_circuits_set(&allowed_delegations),
        );

        let (main_proofs, delegation_proofs, register_values) =
            prover_examples::prove_image_execution_on_reduced_machine(
                10,
                &binary,
                non_determinism_source,
                &main_circuit_precomputations,
                &delegation_precomputations,
                &worker,
            );

        let total_delegation_proofs: usize = delegation_proofs.iter().map(|(_, x)| x.len()).sum();

        println!(
            "Created {} basic proofs and {} delegation proofs.",
            main_proofs.len(),
            total_delegation_proofs
        );

        let mut proofs_map = BTreeMap::new();
        for (delegation_type, proofs) in delegation_proofs.into_iter() {
            proofs_map.insert(delegation_type, proofs);
        }

        let program_proof = ProgramProof {
            base_layer_proofs: main_proofs,
            delegation_proofs: proofs_map,
            register_final_values: register_values,
            end_params: new_end_params,
            recursion_chain_preimage: Some(preimage),
            recursion_chain_hash: Some(chain_hash),
        };

        let is_valid = verify_recursion_layer(&program_proof);
        assert!(is_valid);

        let mut dst = std::fs::File::create("recursion_over_recursion_layer.json").unwrap();
        serde_json::to_writer_pretty(&mut dst, &program_proof).unwrap();
    }

    #[test]
    fn test_prove_final_recursion_over_recursion() {
        let worker = prover::worker::Worker::new_with_num_threads(8);

        let binary = RECURSION_LAYER_NO_DELEGATION_VERIFIER;

        let expected_final_pc = find_binary_exit_point(&binary);
        println!(
            "Expected final PC for recursion program is 0x{:08x}",
            expected_final_pc
        );

        let binary = get_padded_binary(&binary);

        let mut src = std::fs::File::open("recursion_over_recursion_layer.json").unwrap();
        let proofs: ProgramProof = serde_json::from_reader(&mut src).unwrap();

        dbg!(proofs.end_params);
        dbg!(proofs.recursion_chain_hash);
        dbg!(proofs.recursion_chain_preimage);

        let main_circuit_precomputations =
            trace_and_split::setups::get_final_reduced_riscv_circuit_setup::<Global, Global>(
                &binary, &worker,
            );

        let new_end_params =
            compute_end_parameters(expected_final_pc, &main_circuit_precomputations);
        let (preimage, chain_hash) = continue_chain_encoding(
            &proofs.recursion_chain_hash.unwrap(),
            &proofs.recursion_chain_preimage.unwrap(),
            &proofs.end_params,
        );

        dbg!(new_end_params);
        dbg!(preimage);
        dbg!(chain_hash);

        let allowed_delegations: Vec<_> = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS
            .iter()
            .map(|el| el.0)
            .collect();
        let non_determinism_source = QuasiUARTSource::new_with_reads(
            proofs.flatten_for_delegation_circuits_set(&allowed_delegations),
        );

        let (main_proofs, delegation_proofs, register_values) =
            prover_examples::prove_image_execution_on_final_reduced_machine(
                10,
                &binary,
                non_determinism_source,
                &main_circuit_precomputations,
                &[],
                &worker,
            );

        let total_delegation_proofs: usize = delegation_proofs.iter().map(|(_, x)| x.len()).sum();

        println!(
            "Created {} basic proofs and {} delegation proofs.",
            main_proofs.len(),
            total_delegation_proofs
        );

        let mut proofs_map = BTreeMap::new();
        for (delegation_type, proofs) in delegation_proofs.into_iter() {
            proofs_map.insert(delegation_type, proofs);
        }

        let program_proof = ProgramProof {
            base_layer_proofs: main_proofs,
            delegation_proofs: proofs_map,
            register_final_values: register_values,
            end_params: new_end_params,
            recursion_chain_preimage: Some(preimage),
            recursion_chain_hash: Some(chain_hash),
        };

        let is_valid = verify_final_recursion_layer(&program_proof);
        assert!(is_valid);

        let mut dst = std::fs::File::create("final_recursion_layer.json").unwrap();
        serde_json::to_writer_pretty(&mut dst, &program_proof).unwrap();
    }

    #[test]
    fn test_prove_final_recursion_over_final_recursion() {
        let worker = prover::worker::Worker::new_with_num_threads(8);

        let binary = FINAL_RECURSION_LAYER_VERIFIER;

        let expected_final_pc = find_binary_exit_point(&binary);
        println!(
            "Expected final PC for recursion program is 0x{:08x}",
            expected_final_pc
        );

        let binary = get_padded_binary(&binary);

        let mut src = std::fs::File::open("final_recursion_layer.json").unwrap();
        let proofs: ProgramProof = serde_json::from_reader(&mut src).unwrap();

        dbg!(proofs.end_params);
        dbg!(proofs.recursion_chain_hash);
        dbg!(proofs.recursion_chain_preimage);

        let main_circuit_precomputations =
            trace_and_split::setups::get_final_reduced_riscv_circuit_setup::<Global, Global>(
                &binary, &worker,
            );

        let new_end_params =
            compute_end_parameters(expected_final_pc, &main_circuit_precomputations);
        let (preimage, chain_hash) = continue_chain_encoding(
            &proofs.recursion_chain_hash.unwrap(),
            &proofs.recursion_chain_preimage.unwrap(),
            &proofs.end_params,
        );

        dbg!(new_end_params);
        dbg!(preimage);
        dbg!(chain_hash);

        let allowed_delegations: Vec<_> = FINAL_RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS
            .iter()
            .map(|el| el.0)
            .collect();
        let non_determinism_source = QuasiUARTSource::new_with_reads(
            proofs.flatten_for_delegation_circuits_set(&allowed_delegations),
        );

        let (main_proofs, delegation_proofs, register_values) =
            prover_examples::prove_image_execution_on_final_reduced_machine(
                10,
                &binary,
                non_determinism_source,
                &main_circuit_precomputations,
                &[],
                &worker,
            );

        let total_delegation_proofs: usize = delegation_proofs.iter().map(|(_, x)| x.len()).sum();

        println!(
            "Created {} basic proofs and {} delegation proofs.",
            main_proofs.len(),
            total_delegation_proofs
        );
        assert_eq!(main_proofs.len(), 1);
        assert_eq!(total_delegation_proofs, 0);

        let mut proofs_map = BTreeMap::new();
        for (delegation_type, proofs) in delegation_proofs.into_iter() {
            proofs_map.insert(delegation_type, proofs);
        }

        let program_proof = ProgramProof {
            base_layer_proofs: main_proofs,
            delegation_proofs: proofs_map,
            register_final_values: register_values,
            end_params: new_end_params,
            recursion_chain_preimage: Some(preimage),
            recursion_chain_hash: Some(chain_hash),
        };

        let is_valid = verify_final_recursion_layer(&program_proof);
        assert!(is_valid);

        let mut dst =
            std::fs::File::create("final_recursion_over_final_recursion_layer.json").unwrap();
        serde_json::to_writer_pretty(&mut dst, &program_proof).unwrap();
    }

    // use verifier_common::VerifierFunctionPointer;
    // pub fn verify_risc_v_proof(single_proof: &Proof, verification_fn_ptr: VerifierFunctionPointer<
    //     CAP_SIZE,
    //     NUM_COSETS,
    //     NUM_DELEGATION_CHALLENGES,
    //     1,
    //     2,
    // >) -> bool {
    //     let responses = flatten_full_proof(single_proof, true);

    //     println!("Verifying recursion layer proof using RISC-V simulator and the verifier program");
    //     let allowed_delegation_types: Vec<_> = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS
    //         .iter()
    //         .map(|el| el.0)
    //         .collect();
    //     let responses = full_proof.flatten_for_delegation_circuits_set(&allowed_delegation_types);
    //     let binary = if RUN_VERIFIERS_WITH_OUTPUT {
    //         RECURSION_LAYER_VERIFIER_WITH_OUTPUT
    //     } else {
    //         RECURSION_LAYER_VERIFIER
    //     };

    //     run_verifier_binary(binary, responses).is_some()
    // }

    #[cfg(feature = "extended_tests")]
    #[test]
    fn debug_verification() {
        let mut src = std::fs::File::open("recursion_layer.json").unwrap();
        let proofs: ProgramProof = serde_json::from_reader(&mut src).unwrap();
        let allowed_delegations: Vec<_> = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS
            .iter()
            .map(|el| el.0)
            .collect();
        let source = proofs.flatten_for_delegation_circuits_set(&allowed_delegations);

        verifier_common::prover::nd_source_std::set_iterator(source.into_iter());

        let _ = full_statement_verifier::verify_recursion_layer();
    }

    #[cfg(feature = "extended_tests")]
    #[test]
    fn debug_single_risc_v_proof_verification() {
        use std::mem::MaybeUninit;
        use verifier_common::proof_flattener::flatten_full_proof;
        use verifier_common::ProofPublicInputs;

        let mut src = std::fs::File::open("recursion_layer.json").unwrap();
        let proofs: ProgramProof = serde_json::from_reader(&mut src).unwrap();

        // let fn_ptr = full_statement_verifier::RISC_V_REDUCED_MACHINE_VERIFIER_PTR;
        let fn_ptr = full_statement_verifier::RISC_V_REDUCED_MACHINE_VERIFIER_PTR;

        let proof = &proofs.base_layer_proofs[1];
        let source = flatten_full_proof(proof, true);

        // we have a problem with a stack size in debug, so let's cheat
        std::thread::Builder::new()
            .stack_size(1 << 27)
            .spawn(move || {
                verifier_common::prover::nd_source_std::set_iterator(source.into_iter());
                unsafe {
                    fn_ptr(
                        &mut MaybeUninit::uninit().assume_init(),
                        &mut ProofPublicInputs::uninit(),
                    );
                }
            })
            .unwrap()
            .join()
            .unwrap();

        // verifier_common::prover::nd_source_std::set_iterator(source.into_iter());
        // unsafe {
        //     fn_ptr(
        //         &mut MaybeUninit::uninit().assume_init(),
        //         &mut ProofPublicInputs::uninit(),
        //     );
        // }
    }

    // #[test]
    // fn compare_witness() {
    //     use verifier_common::prover::tracers::main_cycle_optimized::CycleData;

    //     let reference_file = std::fs::File::open("./riscv_witness_chunk_0_reference.bin").unwrap();
    //     let new_file = std::fs::File::open("./riscv_witness_chunk_0.bin").unwrap();

    //     let reference_witness: CycleData<IMStandardIsaConfig, Global> = bincode::deserialize_from(reference_file).unwrap();
    //     println!("Deserialized reference one");
    //     let new_witness: CycleData<IMStandardIsaConfig, Global> = bincode::deserialize_from(new_file).unwrap();
    //     println!("Deserialized new one");

    //     assert_eq!(reference_witness.per_cycle_data.len(), new_witness.per_cycle_data.len());

    //     for (i, (reference, new)) in reference_witness.per_cycle_data.iter().zip(new_witness.per_cycle_data.iter()).enumerate() {
    //         if reference != new {
    //             println!("Diverged at cycle {}:", i);
    //             println!("Reference = {:?}", reference);
    //             println!("New = {:?}", new);
    //             panic!();
    //         }
    //     }
    // }

    // #[test]
    // fn compare_inits_and_teardowns() {
    // use verifier_common::prover::ShuffleRamSetupAndTeardown;

    //     let reference_file = std::fs::File::open("./riscv_shuffle_ram_inits_chunk_0_reference.bin").unwrap();
    //     let new_file = std::fs::File::open("./riscv_shuffle_ram_inits_chunk_0.bin").unwrap();

    //     let reference_witness: ShuffleRamSetupAndTeardown = bincode::deserialize_from(reference_file).unwrap();
    //     println!("Deserialized reference one");
    //     let new_witness: ShuffleRamSetupAndTeardown = bincode::deserialize_from(new_file).unwrap();
    //     println!("Deserialized new one");

    //     assert_eq!(reference_witness.lazy_init_data.len(), new_witness.lazy_init_data.len());

    //     for (i, (reference, new)) in reference_witness.lazy_init_data.iter().zip(new_witness.lazy_init_data.iter()).enumerate() {
    //         if reference != new {
    //             println!("Diverged at cycle {}:", i);
    //             println!("Reference = {:?}", reference);
    //             println!("New = {:?}", new);
    //             panic!();
    //         }
    //     }
    // }

    // #[test]
    // fn debug_poseidon2() {
    //     use verifier_common::ProofPublicInputs;

    //     let mut src = std::fs::File::open("../prover/poseidon2_proof").unwrap();
    //     let proofs: Proof = serde_json::from_reader(&mut src).unwrap();
    //     let source = flatten_full_proof(&proofs, false);
    //     verifier_common::prover::nd_source_std::set_iterator(source.into_iter());

    //     let verifier_fn =
    //         full_statement_verifier::RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS[1].2;
    //     unsafe {
    //         (verifier_fn)(
    //             &mut std::mem::MaybeUninit::uninit().assume_init(),
    //             &mut ProofPublicInputs::uninit(),
    //         );
    //     }
    // }
}
