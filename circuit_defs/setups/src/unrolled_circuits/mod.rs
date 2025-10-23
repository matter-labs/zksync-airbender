use crate::cs::one_row_compiler::CompiledCircuitArtifact;
use std::collections::BTreeMap;

use super::*;

pub use ::add_sub_lui_auipc_mop;
pub use ::inits_and_teardowns;
pub use ::jump_branch_slt;
pub use ::load_store_subword_only;
pub use ::load_store_word_only;
pub use ::mul_div;
pub use ::mul_div_unsigned;
pub use ::shift_binary_csr;
pub use ::unified_reduced_machine;

mod add_sub_lui_auipc_mop_circuit;
mod inits_and_teardowns_circuit;
mod jump_branch_slt_circuit;
mod load_store_subword_only_circuit;
mod load_store_word_only_circuit;
mod mul_div_circuit;
mod mul_div_unsigned_circuit;
mod shift_binary_csr_circuit;
mod unifier_reduced_machine_circuit;

pub use add_sub_lui_auipc_mop_circuit::*;
pub use inits_and_teardowns_circuit::*;
pub use jump_branch_slt_circuit::*;
pub use load_store_subword_only_circuit::*;
pub use load_store_word_only_circuit::*;
pub use mul_div_circuit::*;
pub use mul_div_unsigned_circuit::*;
pub use shift_binary_csr_circuit::*;
pub use unifier_reduced_machine_circuit::*;

pub fn get_unrolled_circuits_artifacts_for_machine_type<C: MachineConfig>(
    binary_image: &[u32],
    // text_section: &[u32],
) -> (
    BTreeMap<u8, CompiledCircuitArtifact<Mersenne31Field>>,
    CompiledCircuitArtifact<Mersenne31Field>,
) {
    let t: Vec<(u8, fn(&[u32]) -> CompiledCircuitArtifact<Mersenne31Field>)> =
        if is_default_machine_configuration::<C>() {
            vec![
                (
                    ::add_sub_lui_auipc_mop::FAMILY_IDX,
                    ::add_sub_lui_auipc_mop::get_circuit,
                ),
                (
                    ::jump_branch_slt::FAMILY_IDX,
                    ::jump_branch_slt::get_circuit,
                ),
                (
                    ::shift_binary_csr::FAMILY_IDX,
                    ::shift_binary_csr::get_circuit,
                ),
                (::mul_div::FAMILY_IDX, ::mul_div::get_circuit),
                (
                    ::load_store_word_only::FAMILY_IDX,
                    ::load_store_word_only::get_circuit,
                ),
                (
                    ::load_store_subword_only::FAMILY_IDX,
                    ::load_store_subword_only::get_circuit,
                ),
            ]
        } else if is_machine_without_signed_mul_div_configuration::<C>() {
            vec![
                (
                    ::add_sub_lui_auipc_mop::FAMILY_IDX,
                    ::add_sub_lui_auipc_mop::get_circuit,
                ),
                (
                    ::jump_branch_slt::FAMILY_IDX,
                    ::jump_branch_slt::get_circuit,
                ),
                (
                    ::shift_binary_csr::FAMILY_IDX,
                    ::shift_binary_csr::get_circuit,
                ),
                (
                    ::mul_div_unsigned::FAMILY_IDX,
                    ::mul_div_unsigned::get_circuit,
                ),
                (
                    ::load_store_word_only::FAMILY_IDX,
                    ::load_store_word_only::get_circuit,
                ),
                (
                    ::load_store_subword_only::FAMILY_IDX,
                    ::load_store_subword_only::get_circuit,
                ),
            ]
        } else if is_reduced_machine_configuration::<C>() {
            vec![
                (
                    ::add_sub_lui_auipc_mop::FAMILY_IDX,
                    ::add_sub_lui_auipc_mop::get_circuit,
                ),
                (
                    ::jump_branch_slt::FAMILY_IDX,
                    ::jump_branch_slt::get_circuit,
                ),
                (
                    ::shift_binary_csr::FAMILY_IDX,
                    ::shift_binary_csr::get_circuit,
                ),
                (
                    ::load_store_word_only::FAMILY_IDX,
                    ::load_store_word_only::get_circuit,
                ),
            ]
        } else {
            panic!("Unknown configuration {:?}", std::any::type_name::<C>());
        };

    let families = artifacts_for_unrolled_circuits_params_impl(binary_image, &t);
    let inits_and_teardowns = ::inits_and_teardowns::get_circuit(binary_image);

    (families, inits_and_teardowns)
}

fn artifacts_for_unrolled_circuits_params_impl(
    binary_image: &[u32],
    // bytecode: &[u32],
    circuits: &[(u8, fn(&[u32]) -> CompiledCircuitArtifact<Mersenne31Field>)],
) -> BTreeMap<u8, CompiledCircuitArtifact<Mersenne31Field>> {
    let mut results = BTreeMap::new();
    for (family_idx, eval_fn) in circuits.iter() {
        let artifact = (eval_fn)(binary_image);

        results.insert(*family_idx, artifact);
    }

    results
}

pub fn get_unrolled_circuits_setups_for_machine_type<
    C: MachineConfig,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    binary_image: &[u32],
    text_section: &[u32],
    worker: &Worker,
) -> BTreeMap<u8, UnrolledCircuitPrecomputations<A, B>> {
    let t = if is_default_machine_configuration::<C>() {
        vec![
            add_sub_lui_auipc_mop_circuit_setup,
            jump_branch_slt_circuit_setup,
            shift_binary_csr_circuit_setup,
            mul_div_circuit_setup,
            load_store_word_only_circuit_setup,
            load_store_subword_only_circuit_setup,
        ]
    } else if is_machine_without_signed_mul_div_configuration::<C>() {
        vec![
            add_sub_lui_auipc_mop_circuit_setup,
            jump_branch_slt_circuit_setup,
            shift_binary_csr_circuit_setup,
            mul_div_unsigned_circuit_setup,
            load_store_word_only_circuit_setup,
            load_store_subword_only_circuit_setup,
        ]
    } else if is_reduced_machine_configuration::<C>() {
        vec![
            add_sub_lui_auipc_mop_circuit_setup,
            jump_branch_slt_circuit_setup,
            shift_binary_csr_circuit_setup,
            load_store_word_only_circuit_setup,
        ]
    } else {
        panic!("Unknown configuration {:?}", std::any::type_name::<C>());
    };

    precomputations_for_unrolled_circuits_params_impl::<A, B>(
        binary_image,
        text_section,
        &t,
        worker,
    )
}

fn precomputations_for_unrolled_circuits_params_impl<A: GoodAllocator, B: GoodAllocator>(
    binary_image: &[u32],
    bytecode: &[u32],
    circuits: &[fn(&[u32], &[u32], &Worker) -> UnrolledCircuitPrecomputations<A, B>],
    worker: &Worker,
) -> BTreeMap<u8, UnrolledCircuitPrecomputations<A, B>> {
    assert!(binary_image.len() >= bytecode.len());
    assert!(binary_image.starts_with(bytecode));

    let mut results = BTreeMap::new();
    for eval_fn in circuits.iter() {
        let precomp = (eval_fn)(binary_image, bytecode, &worker);

        results.insert(precomp.family_idx, precomp);
    }

    results
}
