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

// #[cfg(any(feature = "verifier_80", feature = "verifier_100"))]
// pub fn verify_unrolled_base_layer_for_machine_configuration<C: MachineConfig>(
//     proof: &UnrolledProgramProof,
//     setup: &UnrolledProgramSetup,
// ) -> Result<[u32; 16], ()> {
//     for (k, v) in proof.circuit_families_proofs.iter() {
//         println!("{} proofs for family {}", v.len(), k);
//     }

//     let responses = proof.flatten_into_responses(C::ALLOWED_DELEGATION_CSRS);

//     let params = if setups::is_default_machine_configuration::<C>() {
//         full_statement_verifier::unrolled_proof_statement::FULL_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS
//     } else if setups::is_machine_without_signed_mul_div_configuration::<C>() {
//         full_statement_verifier::unrolled_proof_statement::FULL_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS
//     } else if setups::is_reduced_machine_configuration::<C>() {
//         full_statement_verifier::unrolled_proof_statement::RECURSION_WORD_ONLY_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS
//     } else {
//         panic!("Unknown configuration {:?}", std::any::type_name::<C>());
//     };

//     println!("Running the verifier");

//     let families_setups: Vec<_> = setup
//         .circuit_families_setups
//         .iter()
//         .map(|el| *el.1)
//         .collect();
//     let inits_and_teardowns_setup = setup.inits_and_teardowns_setup;

//     let result = std::thread::Builder::new()
//             .name("verifier thread".to_string())
//             .stack_size(1 << 27)
//             .spawn(move || {

//         let families_setups_refs: Vec<_> = families_setups.iter().map(|el| el).collect();
//         let it = responses.into_iter();
//         prover::nd_source_std::set_iterator(it);

//         #[allow(invalid_value)]
//         let regs = unsafe {
//             full_statement_verifier::unrolled_proof_statement::verify_full_statement_for_unrolled_circuits::<true, { setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS }>(
//                 &families_setups_refs,
//                 params,
//                 (&inits_and_teardowns_setup, full_statement_verifier::unrolled_proof_statement::INITS_AND_TEARDOWNS_VERIFIER_PTR),
//                 full_statement_verifier::BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS,
//             )
//         };

//         regs
//     })
//     .expect("must spawn verifier thread").join();

//     result.map_err(|_| ())
// }

// #[cfg(any(feature = "verifier_80", feature = "verifier_100"))]
// pub fn verify_unrolled_base_layer_via_full_statement_verifier(
//     proof: &UnrolledProgramProof,
//     setup: &UnrolledProgramSetup,
// ) -> Result<[u32; 16], ()> {
//     for (k, v) in proof.circuit_families_proofs.iter() {
//         println!("{} proofs for family {}", v.len(), k);
//     }

//     let mut responses = setup.flatten_for_recursion();
//     responses.extend(proof.flatten_into_responses(&[
//         common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
//         common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
//         common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER,
//     ]));

//     println!("Running the verifier");

//     let result = std::thread::Builder::new()
//         .name("verifier thread".to_string())
//         .stack_size(1 << 27)
//         .spawn(move || {
//             let it = responses.into_iter();
//             prover::nd_source_std::set_iterator(it);

//             #[allow(invalid_value)]
//             let regs = unsafe {
//                 full_statement_verifier::unrolled_proof_statement::verify_unrolled_base_layer()
//             };

//             regs
//         })
//         .expect("must spawn verifier thread")
//         .join();

//     result.map_err(|_| ())
// }

#[cfg(any(feature = "verifier_80", feature = "verifier_100"))]
pub fn verify_unified_recursion_layer_for_machine_configuration<C: MachineConfig>(
    proof: &UnrolledProgramProof,
    setup: &UnrolledProgramSetup,
    compiled_layouts: &CompiledCircuitsSet,
) -> Result<[u32; 16], ()> {
    use crate::unified_circuit::common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
    assert_eq!(setup.circuit_families_setups.len(), 1);
    assert!(setup
        .circuit_families_setups
        .contains_key(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX));

    assert_eq!(proof.circuit_families_proofs.len(), 1);
    assert!(proof.inits_and_teardowns_proofs.is_empty());
    assert!(proof.circuit_families_proofs[&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX].len() > 0);

    for (k, v) in proof.circuit_families_proofs.iter() {
        println!("{} proofs for family {}", v.len(), k);
    }

    let responses = proof.flatten_into_responses(C::ALLOWED_DELEGATION_CSRS, compiled_layouts);

    let params = if setups::is_default_machine_configuration::<C>() {
        panic!(
            "Trying to use configuration {:?} at recursion layer",
            std::any::type_name::<C>()
        );
    } else if setups::is_machine_without_signed_mul_div_configuration::<C>() {
        panic!(
            "Trying to use configuration {:?} at recursion layer",
            std::any::type_name::<C>()
        );
    } else if setups::is_reduced_machine_configuration::<C>() {
        full_statement_verifier::unrolled_proof_statement::RECURSION_WORD_ONLY_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS
    } else {
        panic!("Unknown configuration {:?}", std::any::type_name::<C>());
    };

    println!("Running the verifier");

    let families_setups: Vec<_> = setup
        .circuit_families_setups
        .iter()
        .map(|el| *el.1)
        .collect();

    let result = std::thread::Builder::new()
            .name("verifier thread".to_string())
            .stack_size(1 << 27)
            .spawn(move || {

        let families_setups_refs: Vec<_> = families_setups.iter().map(|el| el).collect();
        let it = responses.into_iter();
        prover::nd_source_std::set_iterator(it);

        #[allow(invalid_value)]
        let regs = unsafe {
            full_statement_verifier::unified_circuit_statement::verify_unified_circuit_statement::<false>(
                &families_setups_refs[0],
                full_statement_verifier::unified_circuit_statement::REDUCED_UNIFIED_CIRCUIT_CAPACITY,
                full_statement_verifier::unified_circuit_statement::REDUCED_UNIFIED_CIRCUIT_VERIFIER_PTR,
                full_statement_verifier::BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS,
            )
        };

        regs
    })
    .expect("must spawn verifier thread").join();

    result.map_err(|_| ())
}

#[cfg(any(feature = "verifier_80", feature = "verifier_100"))]
pub fn verify_unrolled_recursion_layer_via_full_statement_verifier(
    proof: &UnrolledProgramProof,
    setup: &UnrolledProgramSetup,
    compiled_layouts: &CompiledCircuitsSet,
) -> Result<[u32; 16], ()> {
    use crate::unified_circuit::common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
    assert_eq!(setup.circuit_families_setups.len(), 1);
    assert!(setup
        .circuit_families_setups
        .contains_key(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX));

    assert_eq!(proof.circuit_families_proofs.len(), 1);
    assert!(proof.inits_and_teardowns_proofs.is_empty());
    assert!(proof.circuit_families_proofs[&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX].len() > 0);

    for (k, v) in proof.circuit_families_proofs.iter() {
        println!("{} proofs for family {}", v.len(), k);
    }

    let mut responses = setup.flatten_unified_for_recursion();
    responses.extend(proof.flatten_into_responses(&[
        common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER,
    ], compiled_layouts));

    println!("Running the verifier");

    #[cfg(target_arch = "wasm32")]
    {
        let result = std::panic::catch_unwind(move || {
            let it = responses.into_iter();
            prover::nd_source_std::set_iterator(it);

            #[allow(invalid_value)]
            let regs = unsafe {
                full_statement_verifier::unified_circuit_statement::verify_unified_circuit_recursion_layer()
            };

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

                #[allow(invalid_value)]
                let regs = unsafe {
                    full_statement_verifier::unified_circuit_statement::verify_unified_circuit_recursion_layer()
                };

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
