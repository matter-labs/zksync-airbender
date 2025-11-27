use riscv_transpiler::common_constants;
use sha3::Digest;
use std::collections::BTreeMap;
use trace_and_split::prover;
use trace_and_split::setups;

use super::unrolled::{UnrolledProgramProof, UnrolledProgramSetup};
use super::*;
use prover::common_constants::TimestampScalar;
use prover::cs::one_row_compiler::CompiledCircuitArtifact;
use prover::cs::utils::split_timestamp;
use prover::field::*;
use prover::prover_stages::unrolled_prover::UnrolledModeProof;
use prover::prover_stages::Proof;
use prover::risc_v_simulator;
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
        assert!(proof.inits_and_teardowns_proofs.is_empty() == false);

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

#[cfg(any(feature = "verifier_80", feature = "verifier_100"))]
pub fn verify_proof_in_unified_layer(
    proof: &UnrolledProgramProof,
    setup: &UnrolledProgramSetup,
    compiled_layouts: &CompiledCircuitsSet,
    input_is_unrolled: bool,
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

            let regs = full_statement_verifier::unified_circuit_statement::verify_unrolled_or_unified_circuit_recursion_layer();

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

                let regs = full_statement_verifier::unified_circuit_statement::verify_unrolled_or_unified_circuit_recursion_layer();

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
) -> UnrolledProgramProof {
    use riscv_transpiler::common_constants::{REDUCED_MACHINE_CIRCUIT_FAMILY_IDX, ROM_WORD_SIZE};

    assert_eq!(binary_image.len(), ROM_WORD_SIZE);
    assert_eq!(text_section.len(), ROM_WORD_SIZE);

    let proofs = prove_unified_with_replayer_for_machine_configuration::<C>(
        &binary_image,
        &text_section,
        cycles_bound,
        non_determinism,
        ram_bound,
        &worker,
    );

    let (main_proofs, delegation_proofs, register_final_state, (final_pc, final_timestamp)) =
        proofs;

    let program_proofs = UnrolledProgramProof {
        final_pc,
        final_timestamp,
        circuit_families_proofs: main_proofs,
        inits_and_teardowns_proofs: Vec::new(),
        delegation_proofs: BTreeMap::from_iter(delegation_proofs.into_iter()),
        register_final_values: register_final_state,
        recursion_chain_hash: None,
        recursion_chain_preimage: None,
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
) -> (
    BTreeMap<u8, Vec<UnrolledModeProof>>,
    Vec<(u32, Vec<Proof>)>,
    [FinalRegisterValue; 32],
    (u32, TimestampScalar),
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

    let (main_proofs, delegation_proofs, register_final_state, (final_pc, final_timestamp)) =
        prover_examples::unified::prove_unified_execution_with_replayer::<
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
        );

    (
        main_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
    )
}

#[cfg(test)]
mod test {
    #[test]
    #[cfg(any(feature = "verifier_80", feature = "verifier_100"))]
    fn test_unified_over_unrolled_verifier() {
        use crate::setups::read_and_pad_binary;
        use risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation;
        use std::fs::File;
        use std::path::Path;

        let (_, binary_u32) = read_and_pad_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.bin",
        ));

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
        )
        .expect("is valid proof");
        assert!(result.iter().all(|el| *el == 0) == false);
        dbg!(result);
    }

    #[test]
    #[cfg(any(feature = "verifier_80", feature = "verifier_100"))]
    fn test_unified_over_unified_verifier() {
        use crate::setups::read_and_pad_binary;
        use risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation;
        use std::fs::File;
        use std::path::Path;

        let (_, binary_u32) = read_and_pad_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.bin",
        ));

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
        )
        .expect("is valid proof");
        assert!(result.iter().all(|el| *el == 0) == false);
        dbg!(result);
    }

    #[test]
    #[cfg(any(feature = "verifier_80", feature = "verifier_100"))]
    fn test_unified_x2_over_unified_verifier() {
        use crate::setups::read_and_pad_binary;
        use risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation;
        use std::fs::File;
        use std::path::Path;

        let (_, binary_u32) = read_and_pad_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.bin",
        ));

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
        )
        .expect("is valid proof");
        assert!(result.iter().all(|el| *el == 0) == false);
        dbg!(result);
    }

    #[test]
    fn prove_unified_recursion() {
        use crate::setups::read_and_pad_binary;
        use crate::setups::CompiledCircuitsSet;
        use crate::unified_circuit::flatten_proof_into_responses_for_unified_recursion;
        use crate::unrolled::*;
        use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
        use risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation;
        use std::fs::File;
        use std::{io::Read, path::Path};

        let (binary, binary_u32) = read_and_pad_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.bin",
        ));
        let (text, text_u32) = read_and_pad_binary(Path::new(
            "../tools/verifier/recursion_in_unified_layer.text",
        ));

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
            >(&binary_u32, &text_u32, 1 << 31, source, 1 << 30, &worker);

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
