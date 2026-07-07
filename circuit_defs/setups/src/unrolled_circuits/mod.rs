use std::collections::BTreeMap;

use super::*;

pub use ::add_sub_lui_auipc_mop;
pub use ::inits_and_teardowns;
pub use ::jump_branch_slt;
pub use ::load_store_subword_only;
pub use ::load_store_word_only;
use circuit_common::RiscVCycleCircuit;
// pub use ::mul_div;
pub use ::mul_div_unsigned;
pub use ::shift_binary;
pub use ::unified_reduced_machine;
use prover::common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;

mod add_sub_lui_auipc_mop_circuit;
mod inits_and_teardowns_circuit;
mod jump_branch_slt_circuit;
mod load_store_subword_only_circuit;
mod load_store_word_only_circuit;
// mod mul_div_circuit;
mod mul_div_unsigned_circuit;
mod shift_binary_circuit;
mod unifier_reduced_machine_circuit;

pub use add_sub_lui_auipc_mop_circuit::*;
pub use inits_and_teardowns_circuit::*;
pub use jump_branch_slt_circuit::*;
pub use load_store_subword_only_circuit::*;
pub use load_store_word_only_circuit::*;
// pub use mul_div_circuit::*;
pub use mul_div_unsigned_circuit::*;
pub use shift_binary_circuit::*;
pub use unifier_reduced_machine_circuit::*;
// pub use unifier_reduced_machine_circuit::*;

pub fn decoders_for_machine_type<C: MachineConfig>(
) -> Vec<Box<dyn crate::cs::gkr_circuits::OpcodeFamilyDecoder>> {
    use crate::cs::gkr_circuits::*;

    // opcodes_for_full_machine_with_mem_word_access_specialization

    if is_machine_without_signed_mul_div_configuration::<C>() {
        opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization()
    } else if is_reduced_machine_configuration::<C>() {
        opcodes_for_reduced_machine()
    } else {
        panic!("Unknown configuration {:?}", std::any::type_name::<C>());
    }
}

pub fn get_unrolled_circuits_setups_for_machine_type<
    C: MachineConfig,
    A: GoodAllocator + 'static,
>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    worker: &Worker,
) -> BTreeMap<u8, CircuitSetup<A>> {
    use crate::cs::gkr_circuits::process_binary_into_separate_tables_ext;

    let supported_csrs: Vec<_> = C::ALLOWED_DELEGATION_CSRS
        .iter()
        .map(|el| *el as u16)
        .collect();

    // first we preprocess the bytecode
    let preprocessing_data =
        process_binary_into_separate_tables_ext::<BabyBearField, C::DecodingOptions, true, Global>(
            &text_section,
            &decoders_for_machine_type::<C>(),
            common_constants::ROM_WORD_SIZE,
            &supported_csrs,
        );

    let mut setups = BTreeMap::new();
    // default set
    {
        let t = <::add_sub_lui_auipc_mop::AddSubLuiAuipcMopCircuit as RiscVCycleCircuit<
            BabyBearField,
            false,
        >>::CIRCUIT_FAMILY;
        let tt = &preprocessing_data[&t];
        setups.insert(
            t,
            add_sub_lui_auipc_mop_circuit_setup(tt, use_caches, worker),
        );
    }
    {
        let t = <::jump_branch_slt::JumpBranchSltCircuit as RiscVCycleCircuit<
            BabyBearField,
            false,
        >>::CIRCUIT_FAMILY;
        let tt = &preprocessing_data[&t];
        setups.insert(t, jump_branch_slt_circuit_setup(tt, use_caches, worker));
    }
    {
        let t = <::shift_binary::ShiftBinaryCircuit as RiscVCycleCircuit<BabyBearField, false>>::CIRCUIT_FAMILY;
        let tt = &preprocessing_data[&t];
        setups.insert(t, shift_binary_circuit_setup(tt, use_caches, worker));
    }
    {
        let t = <::load_store_word_only::LoadStoreWordOnlyCircuit as RiscVCycleCircuit<
            BabyBearField,
            true,
        >>::CIRCUIT_FAMILY;
        let tt = &preprocessing_data[&t];
        setups.insert(
            t,
            load_store_word_only_circuit_setup(tt, binary_image, use_caches, worker),
        );
    }

    if is_machine_without_signed_mul_div_configuration::<C>() {
        {
            let t = <::mul_div_unsigned::UnsignedMulDivCircuit as RiscVCycleCircuit<
                BabyBearField,
                false,
            >>::CIRCUIT_FAMILY;
            let tt = &preprocessing_data[&t];
            setups.insert(t, mul_div_unsigned_circuit_setup(tt, use_caches, worker));
        }
        {
            let t = <::load_store_subword_only::LoadStoreSubwordOnlyCircuit as RiscVCycleCircuit<
                BabyBearField,
                true,
            >>::CIRCUIT_FAMILY;
            let tt = &preprocessing_data[&t];
            setups.insert(
                t,
                load_store_subword_only_circuit_setup(tt, binary_image, use_caches, worker),
            );
        }
    } else if is_reduced_machine_configuration::<C>() {
        // nothing
    } else {
        panic!("Unknown configuration {:?}", std::any::type_name::<C>());
    }

    setups
}

// pub fn get_unified_circuit_setup_for_machine_type<
//     C: MachineConfig,
//     A: GoodAllocator + 'static,
//     B: GoodAllocator,
// >(
//     binary_image: &[u32],
//     text_section: &[u32],
//     worker: &Worker,
// ) -> UnrolledCircuitPrecomputations<A, B> {
//     let t: Vec<fn(&[u32], &[u32], &Worker) -> UnrolledCircuitPrecomputations<A, B>> =
//         if is_default_machine_configuration::<C>() {
//             panic!(
//                 "Unsupported machine configuration {}",
//                 std::any::type_name::<C>()
//             );
//         } else if is_machine_without_signed_mul_div_configuration::<C>() {
//             panic!(
//                 "Unsupported machine configuration {}",
//                 std::any::type_name::<C>()
//             );
//         } else if is_reduced_machine_configuration::<C>() {
//             vec![unified_reduced_machine_circuit_setup::<A, B>]
//         } else {
//             panic!("Unknown configuration {:?}", std::any::type_name::<C>());
//         };

//     let mut t = precomputations_for_unrolled_circuits_params_impl::<A, B>(
//         binary_image,
//         text_section,
//         &t[..],
//         worker,
//     );

//     t.remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
//         .expect("must compute setup for unified circuit")
// }

// fn precomputations_for_unrolled_circuits_params_impl<A: GoodAllocator, B: GoodAllocator>(
//     binary_image: &[u32],
//     bytecode: &[u32],
//     circuits: &[fn(&[u32], &[u32], &Worker) -> UnrolledCircuitPrecomputations<A, B>],
//     worker: &Worker,
// ) -> BTreeMap<u8, UnrolledCircuitPrecomputations<A, B>> {
//     assert!(binary_image.len() >= bytecode.len());

//     let mut results = BTreeMap::new();
//     for eval_fn in circuits.iter() {
//         let precomp = (eval_fn)(binary_image, bytecode, &worker);

//         results.insert(precomp.family_idx, precomp);
//     }

//     results
// }
