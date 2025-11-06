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
    responses.extend(setup.flatten_for_recursion());
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

    let mut responses = flatten_proof_into_responses_for_unified_recursion(
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
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource<
        riscv_transpiler::vm::RamWithRomRegion<ROM_SECOND_WORD_BITS>,
    >,
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
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource<
        riscv_transpiler::vm::RamWithRomRegion<ROM_SECOND_WORD_BITS>,
    >,
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
