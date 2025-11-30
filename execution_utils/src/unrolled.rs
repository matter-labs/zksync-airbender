use riscv_transpiler::common_constants;
use sha3::Digest;
use std::collections::BTreeMap;
use trace_and_split::prover;
use trace_and_split::setups;

use super::*;
use prover::common_constants::TimestampScalar;
use prover::cs::utils::split_timestamp;
use prover::field::*;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::prover_stages::Proof;
use prover::risc_v_simulator;
use setups::CompiledCircuitsSet;
use trace_and_split::FinalRegisterValue;

pub use setups::unrolled_circuits::get_unrolled_circuits_artifacts_for_machine_type;

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct UnrolledProgramSetup {
    pub expected_final_pc: u32,
    pub binary_hash: [u8; 32],
    pub circuit_families_setups: BTreeMap<u8, [MerkleTreeCap<CAP_SIZE>; NUM_COSETS]>,
    pub inits_and_teardowns_setup: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    pub end_params: [u32; 8],
}

impl UnrolledProgramSetup {
    pub fn new_from_setups_and_binary(
        binary: &[u8],
        circuit_families_setups: &[(u8, [MerkleTreeCap<CAP_SIZE>; NUM_COSETS])],
        inits_and_teardowns_setup: &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    ) -> Self {
        assert!(circuit_families_setups.is_sorted_by(|a, b| a.0 < b.0));
        let final_pc = find_binary_exit_point(binary);

        let setups: Vec<_> = circuit_families_setups.iter().map(|el| &el.1).collect();

        let end_params = if setups.len() > 1 {
            compute_end_parameters_for_unrolled_circuits(
                final_pc,
                &setups,
                inits_and_teardowns_setup,
            )
        } else {
            assert!(inits_and_teardowns_setup.iter().all(|el| el.cap.iter().all(|el| *el == [0u32; 8])), "single setup is for unified circuits, where inits and teardowns setup is conventional all zeroes here");
            compute_end_parameters_for_unified_circuit(final_pc, &setups[0])
        };

        // binary hash can be anything - it's just for bookkeeping
        let binary_hash = sha3::Keccak256::digest(binary).into();

        Self {
            expected_final_pc: final_pc,
            binary_hash,
            circuit_families_setups: BTreeMap::from_iter(
                circuit_families_setups.iter().map(|el| (el.0, el.1)),
            ),
            inits_and_teardowns_setup: *inits_and_teardowns_setup,
            end_params,
        }
    }

    pub fn flatten_for_recursion(&self) -> Vec<u32> {
        // we just need to dump merkle caps, without any circuit IDs
        let mut result = vec![];
        for (_, caps) in self.circuit_families_setups.iter() {
            result.extend_from_slice(MerkleTreeCap::flatten(caps));
        }
        result.extend_from_slice(MerkleTreeCap::flatten(&self.inits_and_teardowns_setup));

        result
    }

    pub fn flatten_unified_for_recursion(&self) -> Vec<u32> {
        assert_eq!(self.circuit_families_setups.len(), 1);
        // we just need to dump merkle caps, without any circuit IDs
        let mut result = vec![];
        for (_, caps) in self.circuit_families_setups.iter() {
            result.extend_from_slice(MerkleTreeCap::flatten(caps));
        }

        result
    }

    pub fn begin_recursion_chain(base_layer_end_params: &[u32; 8]) -> ([u32; 8], [u32; 16]) {
        let mut preimage = [0u32; 16];
        preimage[8..].copy_from_slice(base_layer_end_params);
        let mut result_hasher = Blake2sBufferingTranscript::new();
        result_hasher.absorb(&preimage);
        let hash_chain = result_hasher.finalize().0;
        (hash_chain, preimage)
    }

    pub fn continue_recursion_chain(
        end_params: &[u32; 8],
        previous_step_hash_chain: &[u32; 8],
        previous_step_chain_preimage: &[u32; 16],
    ) -> ([u32; 8], [u32; 16]) {
        {
            let mut result_hasher = Blake2sBufferingTranscript::new();
            result_hasher.absorb(previous_step_chain_preimage);
            let t = result_hasher.finalize().0;
            assert_eq!(&t, previous_step_hash_chain);
        }
        if &previous_step_hash_chain[8..] == &end_params[..] {
            // do not repeat
            assert!(&previous_step_hash_chain[..8] != &[0u32; 8]);
            (*previous_step_hash_chain, *previous_step_chain_preimage)
        } else {
            let mut preimage = [0u32; 16];
            preimage[..8].copy_from_slice(previous_step_hash_chain);
            preimage[8..].copy_from_slice(end_params);
            let mut result_hasher = Blake2sBufferingTranscript::new();
            result_hasher.absorb(&preimage);
            let hash_chain = result_hasher.finalize().0;
            (hash_chain, preimage)
        }
    }
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct UnrolledProgramProof {
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub circuit_families_proofs: BTreeMap<u8, Vec<UnrolledModeProof>>,
    pub inits_and_teardowns_proofs: Vec<UnrolledModeProof>,
    pub delegation_proofs: BTreeMap<u32, Vec<Proof>>,
    pub register_final_values: [FinalRegisterValue; 32],
    pub recursion_chain_preimage: Option<[u32; 16]>,
    pub recursion_chain_hash: Option<[u32; 8]>,
}

impl UnrolledProgramProof {
    pub fn get_proof_counts(&self) -> (usize, usize, usize) {
        let family_proofs: usize = self
            .circuit_families_proofs
            .iter()
            .map(|(_, v)| v.len())
            .sum();
        let inits_and_teardowns_proofs = self.inits_and_teardowns_proofs.len();
        let delegation_proofs: usize = self.delegation_proofs.iter().map(|(_, v)| v.len()).sum();
        (family_proofs, inits_and_teardowns_proofs, delegation_proofs)
    }

    pub fn debug_info(&self) -> String {
        let (family_proofs, inits_and_teardowns_proofs, delegation_proofs) =
            self.get_proof_counts();
        format!("Proofs: {family_proofs} circuit family proof(s), {inits_and_teardowns_proofs} inits and teardowns proof(s), {delegation_proofs} delegation proof(s)")
    }

    pub fn flatten_into_responses(
        &self,
        allowed_delegation_circuits: &[u32],
        compiled_layouts: &CompiledCircuitsSet,
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

        // final PC and timestamp
        {
            responses.push(self.final_pc);
            let (low, high) = split_timestamp(self.final_timestamp);
            responses.push(low);
            responses.push(high);
        }

        // families ones
        for (family, proofs) in self.circuit_families_proofs.iter() {
            responses.push(proofs.len() as u32);
            for proof in proofs.iter() {
                let Some(artifact) = &compiled_layouts.compiled_circuit_families.get(family) else {
                    panic!("Proofs file has a proof for circuit type {}, but there is no matching compiled circuit in the set", family);
                };
                let t =
                    verifier_common::proof_flattener::flatten_full_unrolled_proof(proof, artifact);
                responses.extend(t);
            }
        }

        // inits and teardowns
        {
            if let Some(compiled_inits_and_teardowns) =
                compiled_layouts.compiled_inits_and_teardowns.as_ref()
            {
                responses.push(self.inits_and_teardowns_proofs.len() as u32);
                for proof in self.inits_and_teardowns_proofs.iter() {
                    let t = verifier_common::proof_flattener::flatten_full_unrolled_proof(
                        proof,
                        &compiled_inits_and_teardowns,
                    );
                    responses.extend(t);
                }
            } else {
                responses.push(0u32);
            }
        }

        // then for every allowed delegation circuit
        for delegation_type in allowed_delegation_circuits.iter() {
            if *delegation_type == common_constants::NON_DETERMINISM_CSR {
                continue;
            }
            if let Some(proofs) = self.delegation_proofs.get(&delegation_type) {
                responses.push(proofs.len() as u32);
                for proof in proofs.iter() {
                    let t = verifier_common::proof_flattener::flatten_full_proof(proof, 0);
                    responses.extend(t);
                }
            } else {
                responses.push(0);
            }
        }

        if let Some(preimage) = self.recursion_chain_preimage {
            responses.extend(preimage);
        }

        responses
    }
}

pub fn compute_setup_for_machine_configuration<C: MachineConfig>(
    binary_image: &[u8],
    text_section: &[u8],
) -> UnrolledProgramSetup {
    assert_eq!(binary_image.len() % 4, 0);
    assert_eq!(text_section.len() % 4, 0);

    let binary_image_u32: Vec<_> = binary_image
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let text_section_u32: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    assert_eq!(
        binary_image_u32.len(),
        riscv_transpiler::common_constants::ROM_WORD_SIZE
    );
    assert_eq!(
        text_section_u32.len(),
        riscv_transpiler::common_constants::ROM_WORD_SIZE
    );

    let families_setups = setups::compute_unrolled_circuits_params_for_machine_configuration::<C>(
        &binary_image_u32,
        &text_section_u32,
    );
    let inits_and_teardowns_setup =
        setups::compute_inits_and_teardowns_params(&binary_image_u32, &text_section_u32);

    UnrolledProgramSetup::new_from_setups_and_binary(
        binary_image,
        &families_setups
            .into_iter()
            .map(|el| (el.family_idx as u8, el.setup_caps))
            .collect::<Vec<_>>(),
        &inits_and_teardowns_setup,
    )
}

pub fn flatten_proof_into_responses_for_unrolled_recursion(
    proof: &UnrolledProgramProof,
    setup: &UnrolledProgramSetup,
    compiled_layouts: &CompiledCircuitsSet,
    is_base_layer: bool,
) -> Vec<u32> {
    let mut responses = vec![];
    let op = if is_base_layer {
        full_statement_verifier::definitions::OP_VERIFY_BASE_LAYER_IN_UNROLLED_CIRCUITS
    } else {
        full_statement_verifier::definitions::OP_VERIFY_RECURSIVE_LAYER_IN_UNROLLED_CIRCUITS
    };
    responses.push(op);
    responses.extend(setup.flatten_for_recursion());
    if is_base_layer {
        responses.extend(proof.flatten_into_responses(&[
            common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
            common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
            common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
        ], compiled_layouts));
    } else {
        responses.extend(proof.flatten_into_responses(&[
            common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
        ], compiled_layouts));
    }

    responses
}

#[cfg(any(feature = "verifier_80", feature = "verifier_100"))]
pub fn verify_unrolled_layer_proof(
    proof: &UnrolledProgramProof,
    setup: &UnrolledProgramSetup,
    compiled_layouts: &CompiledCircuitsSet,
    is_base_layer: bool,
) -> Result<[u32; 16], ()> {
    for (k, v) in proof.circuit_families_proofs.iter() {
        println!("{} proofs for family {}", v.len(), k);
    }

    let responses = flatten_proof_into_responses_for_unrolled_recursion(
        proof,
        setup,
        compiled_layouts,
        is_base_layer,
    );

    println!("Running the verifier");

    #[cfg(target_arch = "wasm32")]
    {
        let result = std::panic::catch_unwind(move || {
            let it = responses.into_iter();
            prover::nd_source_std::set_iterator(it);

            let regs = full_statement_verifier::unrolled_proof_statement::verify_base_or_recursion_unrolled_circuits();

            regs
        }).map_err(|_| ());

        result
    }

    #[cfg(not(target_arch = "wasm32"))]
    {
        let result = std::thread::Builder::new()
            .name("verifier thread".to_string())
            .stack_size(1 << 27)
            .spawn(move || {
                let it = responses.into_iter();
                prover::nd_source_std::set_iterator(it);

                let regs = full_statement_verifier::unrolled_proof_statement::verify_base_or_recursion_unrolled_circuits();

                regs
            })
            .expect("must spawn verifier thread")
            .join();

        result.map_err(|_| ())
    }
}

use common_constants::rom::ROM_SECOND_WORD_BITS;

#[cfg(feature = "prover")]
pub fn prove_unrolled_for_machine_configuration_into_program_proof<C: MachineConfig>(
    binary_image: &[u32],
    text_section: &[u32],
    cycles_bound: usize,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &prover::worker::Worker,
) -> UnrolledProgramProof {
    use riscv_transpiler::common_constants::ROM_WORD_SIZE;

    assert_eq!(binary_image.len(), ROM_WORD_SIZE);
    assert_eq!(text_section.len(), ROM_WORD_SIZE);

    let proofs = prove_unrolled_with_replayer_for_machine_configuration::<C>(
        &binary_image,
        &text_section,
        cycles_bound,
        non_determinism,
        ram_bound,
        &worker,
    );

    let (
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
    ) = proofs;

    let program_proofs = UnrolledProgramProof {
        final_pc,
        final_timestamp,
        circuit_families_proofs: main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs: BTreeMap::from_iter(delegation_proofs.into_iter()),
        register_final_values: register_final_state,
        recursion_chain_hash: None,
        recursion_chain_preimage: None,
    };

    program_proofs
}

#[cfg(feature = "prover")]
pub fn prove_unrolled_with_replayer_for_machine_configuration<C: MachineConfig>(
    binary_image: &[u32],
    text_section: &[u32],
    cycles_bound: usize,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &prover::worker::Worker,
) -> (
    BTreeMap<u8, Vec<UnrolledModeProof>>,
    Vec<UnrolledModeProof>,
    Vec<(u32, Vec<Proof>)>,
    [FinalRegisterValue; 32],
    (u32, TimestampScalar),
) {
    use std::alloc::Global;
    println!("Performing precomputations for circuit families");
    let families_precomps =
        setups::unrolled_circuits::get_unrolled_circuits_setups_for_machine_type::<C, Global, Global>(
            binary_image,
            &text_section,
            &worker,
        );

    println!("Performing precomputations for inits and teardowns");
    let inits_and_teardowns_precomps = setups::unrolled_circuits::inits_and_teardowns_circuit_setup(
        &binary_image,
        &text_section,
        worker,
    );

    println!("Performing precomputations for delegation circuits");
    let delegation_precomputations = setups::all_delegation_circuits_precomputations(worker);

    let (
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
    ) = prover_examples::unrolled::prove_unrolled_execution_with_replayer::<
        C,
        Global,
        ROM_SECOND_WORD_BITS,
    >(
        cycles_bound,
        &binary_image,
        &text_section,
        non_determinism,
        &families_precomps,
        &inits_and_teardowns_precomps,
        &delegation_precomputations,
        ram_bound,
        worker,
    );

    (
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
    )
}

#[cfg(any(feature = "verifier_80", feature = "verifier_100"))]
#[cfg(test)]
mod test {
    use super::*;
    use std::path::Path;

    use crate::unrolled::prover::VectorMemoryImplWithRom;
    use risc_v_simulator::abstractions::non_determinism::NonDeterminismCSRSource;
    use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
    use risc_v_simulator::cycle::IMStandardIsaConfigWithUnsignedMulDiv;
    use risc_v_simulator::cycle::MachineConfig;
    use std::alloc::Global;

    #[test]
    fn test_prove_unrolled_fibonacci() {
        let (_, binary_image) =
            setups::read_and_pad_binary(&Path::new("../examples/basic_fibonacci/app.bin"));
        let (_, text_section) =
            setups::read_and_pad_binary(&Path::new("../examples/basic_fibonacci/app.text"));

        let worker = prover::worker::Worker::new_with_num_threads(8);

        let cycles_bound = 1 << 24;
        let rom_bound = 1 << 32;
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![15, 1]);

        let proofs =
            prove_unrolled_for_machine_configuration::<IMStandardIsaConfigWithUnsignedMulDiv>(
                &binary_image,
                &text_section,
                cycles_bound,
                non_determinism_source,
                rom_bound,
                &worker,
            );

        println!("Proving completed, prepairing to verify");

        let is_valid = verify_unrolled_base_layer_for_machine_configuration::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(&binary_image, &text_section, proofs);

        assert!(is_valid);
    }

    #[test]
    fn test_prove_unrolled_hashed_fibonacci() {
        let (_, binary_image) =
            setups::read_and_pad_binary(&Path::new("../examples/hashed_fibonacci/app.bin"));
        let (_, text_section) =
            setups::read_and_pad_binary(&Path::new("../examples/hashed_fibonacci/app.text"));

        let worker = prover::worker::Worker::new_with_num_threads(8);

        let cycles_bound = 1 << 24;
        let rom_bound = 1 << 32;
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![15, 1]);

        let proofs = prove_unrolled_with_replayer_for_machine_configuration::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(
            &binary_image,
            &text_section,
            cycles_bound,
            non_determinism_source,
            rom_bound,
            &worker,
        );

        println!("Proving completed, prepairing to verify");

        let is_valid = verify_unrolled_base_layer_for_machine_configuration::<
            IMStandardIsaConfigWithUnsignedMulDiv,
        >(&binary_image, &text_section, proofs);

        assert!(is_valid);
    }

    pub fn prove_unrolled_for_machine_configuration<C: MachineConfig>(
        binary_image: &[u32],
        text_section: &[u32],
        cycles_bound: usize,
        non_determinism: impl NonDeterminismCSRSource<VectorMemoryImplWithRom>,
        ram_bound: usize,
        worker: &prover::worker::Worker,
    ) -> (
        BTreeMap<u8, Vec<UnrolledModeProof>>,
        Vec<UnrolledModeProof>,
        Vec<(u32, Vec<Proof>)>,
        [FinalRegisterValue; 32],
        (u32, TimestampScalar),
    ) {
        println!("Performing precomputations for circuit families");
        let families_precomps =
            setups::unrolled_circuits::get_unrolled_circuits_setups_for_machine_type::<
                C,
                Global,
                Global,
            >(binary_image, &text_section, &worker);

        println!("Performing precomputations for inits and teardowns");
        let inits_and_teardowns_precomps =
            setups::unrolled_circuits::inits_and_teardowns_circuit_setup(
                &binary_image,
                &text_section,
                worker,
            );

        println!("Performing precomputations for delegation circuits");
        let delegation_precomputations = setups::all_delegation_circuits_precomputations(worker);

        let (
            main_proofs,
            inits_and_teardowns_proofs,
            delegation_proofs,
            register_final_state,
            (final_pc, final_timestamp),
        ) = prover_examples::unrolled::prove_unrolled_execution::<_, C, Global, 5>(
            cycles_bound,
            &binary_image,
            &text_section,
            non_determinism,
            &families_precomps,
            &inits_and_teardowns_precomps,
            &delegation_precomputations,
            ram_bound,
            worker,
        );

        (
            main_proofs,
            inits_and_teardowns_proofs,
            delegation_proofs,
            register_final_state,
            (final_pc, final_timestamp),
        )
    }

    pub fn verify_unrolled_base_layer_for_machine_configuration<C: MachineConfig>(
        binary_image: &[u32],
        text_section: &[u32],
        proofs: (
            BTreeMap<u8, Vec<UnrolledModeProof>>,
            Vec<UnrolledModeProof>,
            Vec<(u32, Vec<Proof>)>,
            [FinalRegisterValue; 32],
            (u32, TimestampScalar),
        ),
    ) -> bool {
        let (
            main_proofs,
            inits_and_teardowns_proofs,
            delegation_proofs,
            register_final_state,
            (final_pc, final_timestamp),
        ) = proofs;
        let compiled_circuits_set =
            setups::unrolled_circuits::get_unrolled_circuits_artifacts_for_machine_type::<C>(
                &binary_image,
            );

        // flatten and set iterator

        let program_proofs = UnrolledProgramProof {
            final_pc,
            final_timestamp,
            circuit_families_proofs: main_proofs,
            inits_and_teardowns_proofs,
            delegation_proofs: BTreeMap::from_iter(delegation_proofs.into_iter()),
            register_final_values: register_final_state,
            recursion_chain_hash: None,
            recursion_chain_preimage: None,
        };

        for (k, v) in program_proofs.circuit_families_proofs.iter() {
            println!("{} proofs for family {}", v.len(), k);
        }

        let responses = program_proofs
            .flatten_into_responses(C::ALLOWED_DELEGATION_CSRS, &compiled_circuits_set);

        let families_setups = setups::compute_unrolled_circuits_params_for_machine_configuration::<C>(
            binary_image,
            text_section,
        );
        let inits_and_teardowns_setup =
            setups::compute_inits_and_teardowns_params(&binary_image, &text_section);

        let params = if setups::is_default_machine_configuration::<C>() {
            full_statement_verifier::unrolled_proof_statement::FULL_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS
        } else if setups::is_machine_without_signed_mul_div_configuration::<C>() {
            full_statement_verifier::unrolled_proof_statement::FULL_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS
        } else if setups::is_reduced_machine_configuration::<C>() {
            full_statement_verifier::unrolled_proof_statement::RECURSION_WORD_ONLY_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS
        } else {
            panic!("Unknown configuration {:?}", std::any::type_name::<C>());
        };

        println!("Running the verifier");

        let result = std::thread::Builder::new()
                .name("verifier thread".to_string())
                .stack_size(1 << 27)
                .spawn(move || {

            let families_setups: Vec<_> = families_setups.iter().map(|el| &el.setup_caps).collect();

            let it = responses.into_iter();
            prover::nd_source_std::set_iterator(it);

            #[allow(invalid_value)]
            let _ = unsafe {
                full_statement_verifier::unrolled_proof_statement::verify_full_statement_for_unrolled_circuits::<true, { setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS }>(
                    &families_setups,
                    params,
                    (&inits_and_teardowns_setup, full_statement_verifier::unrolled_proof_statement::INITS_AND_TEARDOWNS_VERIFIER_PTR),
                    full_statement_verifier::imports::BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS,
                )
            };
        })
        .expect("must spawn verifier thread").join();

        result.is_ok()
    }
}
