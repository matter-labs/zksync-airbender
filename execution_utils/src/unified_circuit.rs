use riscv_transpiler::common_constants;
use std::collections::BTreeMap;
use trace_and_split::prover;
use trace_and_split::setups;

use super::unrolled::{UnrolledProgramProof, UnrolledProgramSetup};
use super::*;
use prover::common_constants::TimestampScalar;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::prover_stages::Proof;
use setups::CompiledCircuitsSet;
use trace_and_split::FinalRegisterValue;

pub use setups::unrolled_circuits::get_unified_circuit_artifact_for_machine_type;

pub fn compute_unified_setup_for_machine_configuration<C: MachineConfig>(
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

    let families_setups = setups::compute_unified_circuit_params_for_machine_configuration::<C>(
        &binary_image_u32,
        &text_section_u32,
    );

    UnrolledProgramSetup::new_from_setups_and_binary(
        binary_image,
        &families_setups
            .into_iter()
            .map(|el| (el.family_idx as u8, el.setup_caps))
            .collect::<Vec<_>>(),
        &[MerkleTreeCap::dummy(); NUM_COSETS],
    )
}

pub fn flatten_proof_into_responses_for_unified_recursion(
    proof: &UnrolledProgramProof,
    setup: &UnrolledProgramSetup,
    compiled_layouts: &CompiledCircuitsSet,
    input_is_unrolled: bool,
) -> Vec<u32> {
    let mut responses = vec![];
    let op = if input_is_unrolled {
        assert!(setup.circuit_families_setups.len() > 1);

        full_statement_verifier::definitions::OP_VERIFY_UNROLLED_RECURSION_LAYER_IN_UNIFIED_CIRCUIT
    } else {
        use crate::unified_circuit::common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
        assert_eq!(setup.circuit_families_setups.len(), 1);
        assert!(setup
            .circuit_families_setups
            .contains_key(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX));

        assert_eq!(proof.circuit_families_proofs.len(), 1);
        assert!(proof.inits_and_teardowns_proofs.is_empty());
        assert!(proof.circuit_families_proofs[&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX].len() > 0);

        full_statement_verifier::definitions::OP_VERIFY_UNIFIED_RECURSION_LAYER_IN_UNIFIED_CIRCUIT
    };
    responses.push(op);
    if input_is_unrolled {
        responses.extend(setup.flatten_for_recursion());
    } else {
        responses.extend(setup.flatten_unified_for_recursion());
    }
    responses.extend(proof.flatten_into_responses(&[
        common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
    ], compiled_layouts));

    responses
}

pub fn verify_proof_in_unified_layer(
    proof: &UnrolledProgramProof,
    setup: &UnrolledProgramSetup,
    compiled_layouts: &CompiledCircuitsSet,
    input_is_unrolled: bool,
    security: verifier_common::SecurityModel,
) -> Result<[u32; 16], ()> {
    for (k, v) in proof.circuit_families_proofs.iter() {
        println!("{} proofs for family {}", v.len(), k);
    }

    let responses = flatten_proof_into_responses_for_unified_recursion(
        proof,
        setup,
        compiled_layouts,
        input_is_unrolled,
    );

    println!("Running the verifier");

    #[cfg(target_arch = "wasm32")]
    {
        let result = std::panic::catch_unwind(move || {
            let it = responses.into_iter();
            prover::nd_source_std::set_iterator(it);

            let regs = full_statement_verifier::unified_circuit_statement::verify_unrolled_or_unified_circuit_recursion_layer(security);

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

                let regs = full_statement_verifier::unified_circuit_statement::verify_unrolled_or_unified_circuit_recursion_layer(security);

                regs
            })
            .expect("must spawn verifier thread")
            .join();

        result.map_err(|_| ())
    }
}

/// A single input into the combined verification: a proof together with the
/// setup and compiled layouts of the program it proves, plus whether it is an
/// unrolled recursion layer proof (`true`) or a unified layer proof (`false`).
pub struct CombinedRecursionInput<'a> {
    pub proof: &'a UnrolledProgramProof,
    pub setup: &'a UnrolledProgramSetup,
    pub compiled_layouts: &'a CompiledCircuitsSet,
    pub input_is_unrolled: bool,
}

/// Create oracle data for combining multiple recursion layer proofs into one
/// statement (see `verify_combined_recursion_layers`). All proofs must belong
/// to the same recursion chain.
pub fn flatten_proofs_into_responses_for_combined_unified_recursion(
    inputs: &[CombinedRecursionInput],
) -> Vec<u32> {
    assert!(
        inputs.len() >= 2,
        "combining requires at least two proofs, got {}",
        inputs.len()
    );

    let mut responses = vec![
        full_statement_verifier::definitions::OP_VERIFY_COMBINED_RECURSION_LAYERS_IN_UNIFIED_CIRCUIT,
        inputs.len() as u32,
    ];
    for input in inputs {
        responses.extend(flatten_proof_into_responses_for_unified_recursion(
            input.proof,
            input.setup,
            input.compiled_layouts,
            input.input_is_unrolled,
        ));
    }

    responses
}

/// Host-side mirror of the guest's combined output computation: the keccak
/// rolling hash of the proofs' outputs in words 0..8, with the shared recursion
/// chain carried through in words 8..16.
pub fn compute_combined_recursion_layers_output(outputs: &[[u32; 16]]) -> [u32; 16] {
    assert!(outputs.len() >= 2);
    let chain = &outputs[0][8..16];
    for output in outputs.iter() {
        assert_eq!(&output[8..16], chain, "Proving chains must be equal");
    }

    let mut hasher = reduced_keccak::Keccak32::new();
    for output in outputs.iter() {
        hasher.update(&output[0..8]);
    }

    let mut result = [0u32; 16];
    result[0..8].copy_from_slice(&hasher.finalize());
    result[8..16].copy_from_slice(chain);
    result
}

/// Verify multiple recursion layer proofs from the same recursion chain as one
/// combined statement, natively on the host. Returns the combined output
/// (keccak rolling hash of the outputs || shared recursion chain).
pub fn verify_combined_proofs_in_unified_layer(
    inputs: &[CombinedRecursionInput],
    security: verifier_common::SecurityModel,
) -> Result<[u32; 16], ()> {
    let responses = flatten_proofs_into_responses_for_combined_unified_recursion(inputs);

    println!("Running the verifier for {} combined proofs", inputs.len());

    #[cfg(target_arch = "wasm32")]
    {
        let result = std::panic::catch_unwind(move || {
            let it = responses.into_iter();
            prover::nd_source_std::set_iterator(it);

            let regs = full_statement_verifier::unified_circuit_statement::verify_unrolled_or_unified_circuit_recursion_layer(security);

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

                let regs = full_statement_verifier::unified_circuit_statement::verify_unrolled_or_unified_circuit_recursion_layer(security);

                regs
            })
            .expect("must spawn verifier thread")
            .join();

        result.map_err(|_| ())
    }
}

use common_constants::rom::ROM_SECOND_WORD_BITS;

#[cfg(feature = "prover")]
pub fn prove_unified_for_machine_configuration_into_program_proof<C: MachineConfig>(
    binary_image: &[u32],
    text_section: &[u32],
    cycles_bound: usize,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &prover::worker::Worker,
    security: verifier_common::SecurityModel,
) -> UnrolledProgramProof {
    use riscv_transpiler::common_constants::ROM_WORD_SIZE;

    assert_eq!(binary_image.len(), ROM_WORD_SIZE);
    assert_eq!(text_section.len(), ROM_WORD_SIZE);

    let proofs = prove_unified_with_replayer_for_machine_configuration::<C>(
        &binary_image,
        &text_section,
        cycles_bound,
        non_determinism,
        ram_bound,
        &worker,
        security,
    );

    let (
        main_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
        pow_challenge,
    ) = proofs;

    let program_proofs = UnrolledProgramProof {
        final_pc,
        final_timestamp,
        circuit_families_proofs: main_proofs,
        inits_and_teardowns_proofs: Vec::new(),
        delegation_proofs: BTreeMap::from_iter(delegation_proofs.into_iter()),
        register_final_values: register_final_state,
        recursion_chain_hash: None,
        recursion_chain_preimage: None,
        pow_challenge,
    };

    program_proofs
}

#[cfg(feature = "prover")]
pub fn prove_unified_with_replayer_for_machine_configuration<C: MachineConfig>(
    binary_image: &[u32],
    text_section: &[u32],
    cycles_bound: usize,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &prover::worker::Worker,
    security: verifier_common::SecurityModel,
) -> (
    BTreeMap<u8, Vec<UnrolledModeProof>>,
    Vec<(u32, Vec<Proof>)>,
    [FinalRegisterValue; 32],
    (u32, TimestampScalar),
    u64,
) {
    use std::alloc::Global;
    println!("Performing precomputations for circuit families");
    let precomputation = setups::unrolled_circuits::get_unified_circuit_setup_for_machine_type::<
        C,
        Global,
        Global,
    >(binary_image, &text_section, &worker);

    println!("Performing precomputations for delegation circuits");
    let delegation_precomputations = setups::all_delegation_circuits_precomputations(worker);

    let (
        main_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
        pow_challenge,
    ) = match security {
        verifier_common::SecurityModel::Security80 => {
            prover_examples::unified::prove_unified_execution_with_replayer_80::<
                C,
                Global,
                ROM_SECOND_WORD_BITS,
            >(
                cycles_bound,
                &binary_image,
                &text_section,
                non_determinism,
                &precomputation,
                &delegation_precomputations,
                ram_bound,
                worker,
            )
        }
        verifier_common::SecurityModel::Security100 => {
            prover_examples::unified::prove_unified_execution_with_replayer_100::<
                C,
                Global,
                ROM_SECOND_WORD_BITS,
            >(
                cycles_bound,
                &binary_image,
                &text_section,
                non_determinism,
                &precomputation,
                &delegation_precomputations,
                ram_bound,
                worker,
            )
        }
    };

    (
        main_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
        pow_challenge,
    )
}

#[cfg(test)]
mod test {
    use crate::{recursion_artifact_path, RecursionArtifact, RecursionLayer};
    use test_utils::skip_if_ci;

    #[test]
    fn test_compute_combined_recursion_layers_output_matches_keccak256() {
        use sha3::Digest;

        // Two 16-word outputs from the same recursion chain (words 8..16 equal).
        let chain: [u32; 8] = [11, 22, 33, 44, 55, 66, 77, 88];
        let mut output_1 = [0u32; 16];
        let mut output_2 = [0u32; 16];
        output_1[..8].copy_from_slice(&[1, 2, 3, 4, 5, 6, 7, 0]);
        output_2[..8].copy_from_slice(&[9, 10, 11, 12, 13, 14, 15, 0]);
        output_1[8..].copy_from_slice(&chain);
        output_2[8..].copy_from_slice(&chain);

        let combined = super::compute_combined_recursion_layers_output(&[output_1, output_2]);

        // Reference: keccak256 over the little-endian byte serialization of
        // out[0..8] per proof (see `verify_combined_recursion_layers`).
        let mut reference_input = Vec::new();
        for output in [output_1, output_2] {
            for val in &output[0..8] {
                reference_input.extend_from_slice(&val.to_le_bytes());
            }
        }
        let reference_hash = sha3::Keccak256::digest(&reference_input);
        let reference_words: Vec<u32> = reference_hash
            .chunks_exact(4)
            .map(|chunk| u32::from_le_bytes(chunk.try_into().unwrap()))
            .collect();

        assert_eq!(&combined[0..8], reference_words.as_slice());
        assert_eq!(&combined[8..16], &chain);
    }

    #[test]
    #[should_panic(expected = "Proving chains must be equal")]
    fn test_compute_combined_recursion_layers_output_rejects_chain_mismatch() {
        let mut output_1 = [1u32; 16];
        let mut output_2 = [1u32; 16];
        output_1[8] = 42;
        output_2[8] = 43;

        super::compute_combined_recursion_layers_output(&[output_1, output_2]);
    }

    fn read_recursion_binary_u32(security: verifier_common::SecurityModel) -> Vec<u32> {
        let (_, binary_u32) = crate::setups::read_and_pad_binary(std::path::Path::new(
            recursion_artifact_path(security, RecursionLayer::Unified, RecursionArtifact::Bin),
        ));

        binary_u32
    }

    fn read_unified_recursion_program(
        security: verifier_common::SecurityModel,
    ) -> (Vec<u8>, Vec<u32>, Vec<u8>, Vec<u32>) {
        let (binary, binary_u32) = crate::setups::read_and_pad_binary(std::path::Path::new(
            recursion_artifact_path(security, RecursionLayer::Unified, RecursionArtifact::Bin),
        ));
        let (text, text_u32) = crate::setups::read_and_pad_binary(std::path::Path::new(
            recursion_artifact_path(security, RecursionLayer::Unified, RecursionArtifact::Txt),
        ));

        (binary, binary_u32, text, text_u32)
    }

    #[cfg(test)]
    #[ignore = "requires pre-generated recursion fixtures"]
    #[test]
    fn test_unified_over_unrolled_verifier() {
        skip_if_ci!();
        use riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation;
        use std::fs::File;
        let security = verifier_common::SecurityModel::Security80;
        let binary_u32 = read_recursion_binary_u32(security);

        let setup: crate::unrolled::UnrolledProgramSetup = serde_json::from_reader(
            &File::open("../gpu_prover_test/setup_recursion_over_base.json").unwrap(),
        )
        .unwrap();
        let proof: crate::unrolled::UnrolledProgramProof = serde_json::from_reader(
            &File::open("../gpu_prover_test/gpu_proof_recursion_over_base.json").unwrap(),
        )
        .unwrap();

        println!("Verifying...");
        let cicuit_set = crate::unrolled::get_unrolled_circuits_artifacts_for_machine_type::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(&binary_u32);
        // let cicuit_set = crate::unified_circuit::get_unified_circuit_artifact_for_machine_type::<IWithoutByteAccessIsaConfigWithDelegation>(&binary_u32);
        let result = crate::unified_circuit::verify_proof_in_unified_layer(
            &proof,
            &setup,
            &cicuit_set,
            true,
            security,
        )
        .expect("is valid proof");
        assert!(result.iter().all(|el| *el == 0) == false);
        dbg!(result);
    }

    #[cfg(test)]
    #[ignore = "requires pre-generated recursion fixtures"]
    #[test]
    fn test_unified_over_unified_verifier() {
        skip_if_ci!();
        use riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation;
        use std::fs::File;
        let security = verifier_common::SecurityModel::Security80;
        let binary_u32 = read_recursion_binary_u32(security);

        let setup: crate::unrolled::UnrolledProgramSetup = serde_json::from_reader(
            &File::open("../gpu_prover_test/setup_recursion_over_recursion.json").unwrap(),
        )
        .unwrap();
        let proof: crate::unrolled::UnrolledProgramProof = serde_json::from_reader(
            &File::open("../gpu_prover_test/gpu_proof_recursion_over_recursion.json").unwrap(),
        )
        .unwrap();

        println!("Verifying...");
        let cicuit_set = crate::unified_circuit::get_unified_circuit_artifact_for_machine_type::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(&binary_u32);
        let result = crate::unified_circuit::verify_proof_in_unified_layer(
            &proof,
            &setup,
            &cicuit_set,
            false,
            security,
        )
        .expect("is valid proof");
        assert!(result.iter().all(|el| *el == 0) == false);
        dbg!(result);
    }

    #[cfg(test)]
    #[ignore = "requires pre-generated recursion fixtures"]
    #[test]
    fn test_unified_x2_over_unified_verifier() {
        skip_if_ci!();
        use riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation;
        use std::fs::File;
        let security = verifier_common::SecurityModel::Security80;
        let binary_u32 = read_recursion_binary_u32(security);

        let setup: crate::unrolled::UnrolledProgramSetup = serde_json::from_reader(
            &File::open("../gpu_prover_test/setup_final_recursion.json").unwrap(),
        )
        .unwrap();
        let proof: crate::unrolled::UnrolledProgramProof = serde_json::from_reader(
            &File::open("../gpu_prover_test/gpu_proof_final_recursion.json").unwrap(),
        )
        .unwrap();

        println!("Verifying...");
        let cicuit_set = crate::unified_circuit::get_unified_circuit_artifact_for_machine_type::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(&binary_u32);
        let result = crate::unified_circuit::verify_proof_in_unified_layer(
            &proof,
            &setup,
            &cicuit_set,
            false,
            security,
        )
        .expect("is valid proof");
        assert!(result.iter().all(|el| *el == 0) == false);
        dbg!(result);
    }

    #[cfg(test)]
    #[ignore = "requires pre-generated recursion fixtures"]
    #[test]
    fn prove_unified_recursion() {
        skip_if_ci!();
        use crate::unified_circuit::flatten_proof_into_responses_for_unified_recursion;
        use crate::unrolled::*;
        use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
        use riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation;
        use std::fs::File;
        let security = verifier_common::SecurityModel::Security80;
        let (binary, binary_u32, text, text_u32) = read_unified_recursion_program(security);

        let input_setup: crate::unrolled::UnrolledProgramSetup = serde_json::from_reader(
            &File::open("../gpu_prover_test/setup_recursion_over_base.json").unwrap(),
        )
        .unwrap();
        let input_proof: crate::unrolled::UnrolledProgramProof = serde_json::from_reader(
            &File::open("../gpu_prover_test/gpu_proof_recursion_over_base.json").unwrap(),
        )
        .unwrap();
        let input_cicuit_set = crate::unrolled::get_unrolled_circuits_artifacts_for_machine_type::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(&binary_u32);

        let responses = flatten_proof_into_responses_for_unified_recursion(
            &input_proof,
            &input_setup,
            &input_cicuit_set,
            true,
        );

        let source = QuasiUARTSource::new_with_reads(responses);

        println!("Computing setup");
        let output_setup = crate::unified_circuit::compute_unified_setup_for_machine_configuration::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(&binary, &text);
        serde_json::to_writer_pretty(
            File::create("unified_setup_over_recursion.json").unwrap(),
            &output_setup,
        )
        .unwrap();
        let output_compiled_layouts = crate::setups::get_unified_circuit_artifact_for_machine_type::<
            IWithoutByteAccessIsaConfigWithDelegation,
        >(&binary_u32);
        serde_json::to_writer_pretty(
            File::create("unified_layout_over_recursion.json").unwrap(),
            &output_compiled_layouts,
        )
        .unwrap();
        let worker = setups::prover::worker::Worker::new_with_num_threads(8);
        println!("Computing proof");

        let mut output_proof =
            crate::unified_circuit::prove_unified_for_machine_configuration_into_program_proof::<
                IWithoutByteAccessIsaConfigWithDelegation,
            >(
                &binary_u32,
                &text_u32,
                1 << 31,
                source,
                1 << 30,
                &worker,
                security,
            );

        let existing_hash_chain = input_proof.recursion_chain_hash.unwrap();
        let existing_preimage = input_proof.recursion_chain_preimage.unwrap();
        // extend a hash chain
        let (hash_chain, preimage) = UnrolledProgramSetup::continue_recursion_chain(
            &input_setup.end_params,
            &existing_hash_chain,
            &existing_preimage,
        );
        output_proof.recursion_chain_hash = Some(hash_chain);
        output_proof.recursion_chain_preimage = Some(preimage);

        serde_json::to_writer_pretty(
            File::create("unified_proof_over_recursion.json").unwrap(),
            &output_proof,
        )
        .unwrap();

        // let result = crate::unified_circuit::verify_proof_in_unified_layer(&output_proof, &output_setup, &output_compiled_layouts, false).expect("is valid proof");
        // assert!(result.iter().all(|el| *el == 0) == false);
        // dbg!(result);
    }
}
