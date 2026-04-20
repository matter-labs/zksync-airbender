#![feature(allocator_api)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use crate::cs::gkr_circuits::ExecutorFamilyDecoderData;
use cs::tables::TableDriver;
use definitions::MerkleTreeCap;
use merkle_trees::DefaultTreeConstructor;
use prover::cs::gkr_compiler::GKRCircuitArtifact;
use prover::fft::*;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::*;
use prover::gkr::prover::setup::GKRSetup;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::gkr::witness_gen::oracles::*;
use prover::merkle_trees::MerkleTreeCapVarLength;
use prover::tracers::*;
use prover::*;
use riscv_transpiler::cycle::*;
use std::alloc::Global;
use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;
use worker::Worker;

pub use ::add_sub_lui_auipc_mop::AddSubLuiAuipcMopCircuit;
pub use ::jump_branch_slt::JumpBranchSltCircuit;
pub use ::load_store_subword_only::LoadStoreSubwordOnlyCircuit;
pub use ::load_store_word_only::LoadStoreWordOnlyCircuit;
pub use ::mul_div_unsigned::UnsignedMulDivCircuit;
pub use ::shift_binary::ShiftBinaryCircuit;

pub use ::bigint_with_control::BigIntDelegationCircuit;
pub use ::blake2_with_compression::Blake2sWithCompressionDelegationCircuit;
pub use ::keccak_special5::KeccakSpecial5DelegationCircuit;

pub use ::inits_and_teardowns;

pub use bigint_with_control;
pub use blake2_with_compression;
pub use keccak_special5;
pub use prover;

pub mod circuits;
pub mod unrolled_circuits;
pub use self::circuits::*;
pub use self::unrolled_circuits::*;

pub fn is_default_machine_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>() == std::any::TypeId::of::<IMStandardIsaConfig>()
}

pub fn is_reduced_machine_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>() == std::any::TypeId::of::<ReducedMachineWithDelegation>()
}

pub fn is_machine_without_signed_mul_div_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>() == std::any::TypeId::of::<IMStandardIsaConfigUnsignedMulDivOnly>()
}

pub fn is_final_reduced_machine_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>() == std::any::TypeId::of::<ReducedMachineWithoutDelegation>()
}

pub enum UnrolledCircuitWitnessEvalFn<A: GoodAllocator> {
    NonMemory {
        witness_fn:
            fn(&'_ mut ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BabyBearField>),
        decoder_table: Vec<ExecutorFamilyDecoderData, A>,
        default_pc_value_in_padding: u32,
    },
    Memory {
        witness_fn: fn(&'_ mut ColumnMajorWitnessProxy<'_, MemoryCircuitOracle<'_>, BabyBearField>),
        decoder_table: Vec<ExecutorFamilyDecoderData, A>,
    },
    // Unified {
    //     witness_fn: fn(&'_ mut ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>>),
    //     decoder_table: Vec<ExecutorFamilyDecoderData, A>,
    // },
}

pub struct CircuitSetup<A: GoodAllocator = Global> {
    pub family_idx: u8,
    pub trace_len: usize,
    pub compiled_circuit: GKRCircuitArtifact<BabyBearField>,
    pub table_driver: TableDriver<BabyBearField>,
    pub setup: GKRSetup<BabyBearField>,
    pub witness_eval_fn: Option<UnrolledCircuitWitnessEvalFn<A>>,
}

pub fn make_setup_for_non_mem_circuit<
    C: circuit_common::RiscVCycleCircuit<BabyBearField, false>,
    A: GoodAllocator,
>(
    witness_eval_fn: Option<
        fn(&'_ mut ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BabyBearField>),
    >,
    default_pc_value_in_padding: u32,
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    use_caches: bool,
) -> CircuitSetup<A> {
    let circuit = circuit_common::risc_v_non_mem_get_circuit::<BabyBearField, C>(use_caches);
    let table_driver = circuit_common::risc_v_non_mem_get_table_driver::<BabyBearField, C>();
    let setup = GKRSetup::construct(
        &table_driver,
        &decoder_table_data,
        1 << C::DOMAIN_SIZE_LOG2,
        &circuit,
    );

    let mut witness_gen_data = Vec::new_in(A::default());
    for el in decoder_table_data.iter() {
        let t = el.as_ref().copied().unwrap_or(Default::default());
        witness_gen_data.push(t);
    }

    let witness_eval_fn = witness_eval_fn.map(|el| UnrolledCircuitWitnessEvalFn::NonMemory {
        witness_fn: el,
        decoder_table: witness_gen_data,
        default_pc_value_in_padding,
    });

    CircuitSetup {
        family_idx: C::CIRCUIT_FAMILY,
        trace_len: 1 << C::DOMAIN_SIZE_LOG2,
        compiled_circuit: circuit,
        table_driver,
        setup,
        witness_eval_fn,
    }
}

pub fn make_setup_for_with_mem_circuit<
    C: circuit_common::RiscVCycleCircuit<BabyBearField, true>,
    A: GoodAllocator,
>(
    witness_eval_fn: Option<
        fn(&'_ mut ColumnMajorWitnessProxy<'_, MemoryCircuitOracle<'_>, BabyBearField>),
    >,
    bytecode: &[u32],
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    use_caches: bool,
) -> CircuitSetup<A> {
    let circuit =
        circuit_common::risc_v_with_mem_get_circuit::<BabyBearField, C>(use_caches, bytecode);
    let table_driver =
        circuit_common::risc_v_with_mem_get_table_driver::<BabyBearField, C>(bytecode);
    let setup = GKRSetup::construct(
        &table_driver,
        &decoder_table_data,
        1 << C::DOMAIN_SIZE_LOG2,
        &circuit,
    );

    let mut witness_gen_data = Vec::new_in(A::default());
    for el in decoder_table_data.iter() {
        let t = el.as_ref().copied().unwrap_or(Default::default());
        witness_gen_data.push(t);
    }

    let witness_eval_fn = witness_eval_fn.map(|el| UnrolledCircuitWitnessEvalFn::Memory {
        witness_fn: el,
        decoder_table: witness_gen_data,
    });

    CircuitSetup {
        family_idx: C::CIRCUIT_FAMILY,
        trace_len: 1 << C::DOMAIN_SIZE_LOG2,
        compiled_circuit: circuit,
        table_driver,
        setup,
        witness_eval_fn,
    }
}

// pub mod all_parameters {
//     use super::*;
//     include!("../generated/all_delegation_circuits_params.rs");
// }

use prover::definitions::{DEFAULT_CAP_SIZE, DEFAULT_LDE_FACTOR};

#[derive(serde::Serialize, serde::Deserialize)]
pub struct UnrolledCircuitSetupParams {
    pub family_idx: u32,
    pub capacity: u32,
    // #[serde(with = "serde_big_array::BigArray")]
    // #[serde(bound(deserialize = "MerkleTreeCap<DEFAULT_CAP_SIZE>: serde::Deserialize<'de>"))]
    // #[serde(bound(serialize = "MerkleTreeCap<DEFAULT_CAP_SIZE>: serde::Serialize"))]
    pub setup_caps: MerkleTreeCap<DEFAULT_CAP_SIZE>,
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct DelegationCircuitSetupParams {
    pub delegation_type: u32,
    pub capacity: u32,
    // #[serde(with = "serde_big_array::BigArray")]
    // #[serde(bound(deserialize = "MerkleTreeCap<DEFAULT_CAP_SIZE>: serde::Deserialize<'de>"))]
    // #[serde(bound(serialize = "MerkleTreeCap<DEFAULT_CAP_SIZE>: serde::Serialize"))]
    pub setup_caps: MerkleTreeCap<DEFAULT_CAP_SIZE>,
}

// pub fn compute_unrolled_circuits_params_for_machine_configuration<C: MachineConfig>(
//     binary_image: &[u32],
//     bytecode: &[u32],
// ) -> Vec<UnrolledCircuitSetupParams> {
//     if is_default_machine_configuration::<C>() {
//         compute_unrolled_circuits_params_base_layer(binary_image, bytecode)
//     } else if is_machine_without_signed_mul_div_configuration::<C>() {
//         compute_unrolled_circuits_params_base_layer_unsigned_only(binary_image, bytecode)
//     } else if is_reduced_machine_configuration::<C>() {
//         compute_unrolled_circuits_params_recursion_layer(binary_image, bytecode)
//     } else {
//         panic!("Unknown configuration {:?}", std::any::type_name::<C>());
//     }
// }

// pub fn compute_unified_circuit_params_for_machine_configuration<C: MachineConfig>(
//     binary_image: &[u32],
//     bytecode: &[u32],
// ) -> Vec<UnrolledCircuitSetupParams> {
//     if is_default_machine_configuration::<C>() {
//         panic!(
//             "Configuration {:?} is not supported",
//             std::any::type_name::<C>()
//         );
//     } else if is_machine_without_signed_mul_div_configuration::<C>() {
//         panic!(
//             "Configuration {:?} is not supported",
//             std::any::type_name::<C>()
//         );
//     } else if is_reduced_machine_configuration::<C>() {
//         compute_unified_circuit_params_recursion_layer(binary_image, bytecode)
//     } else {
//         panic!("Unknown configuration {:?}", std::any::type_name::<C>());
//     }
// }

// pub fn compute_unrolled_circuits_params_base_layer(
//     binary_image: &[u32],
//     bytecode: &[u32],
// ) -> Vec<UnrolledCircuitSetupParams> {
//     let eval_fns = vec![
//         add_sub_lui_auipc_mop_circuit_setup,
//         jump_branch_slt_circuit_setup,
//         shift_binary_csr_circuit_setup,
//         // mul_div_circuit_setup,
//         load_store_word_only_circuit_setup,
//         load_store_subword_only_circuit_setup,
//     ];
//     compute_unrolled_circuits_params_impl(binary_image, bytecode, &eval_fns)
// }

// pub fn compute_unrolled_circuits_params_base_layer_unsigned_only(
//     binary_image: &[u32],
//     bytecode: &[u32],
// ) -> Vec<UnrolledCircuitSetupParams> {
//     let eval_fns = vec![
//         add_sub_lui_auipc_mop_circuit_setup,
//         jump_branch_slt_circuit_setup,
//         shift_binary_csr_circuit_setup,
//         mul_div_unsigned_circuit_setup,
//         load_store_word_only_circuit_setup,
//         load_store_subword_only_circuit_setup,
//     ];
//     compute_unrolled_circuits_params_impl(binary_image, bytecode, &eval_fns)
// }

// pub fn compute_unrolled_circuits_params_recursion_layer(
//     binary_image: &[u32],
//     bytecode: &[u32],
// ) -> Vec<UnrolledCircuitSetupParams> {
//     let eval_fns = vec![
//         add_sub_lui_auipc_mop_circuit_setup,
//         jump_branch_slt_circuit_setup,
//         shift_binary_csr_circuit_setup,
//         load_store_word_only_circuit_setup,
//     ];
//     compute_unrolled_circuits_params_impl(binary_image, bytecode, &eval_fns)
// }

// pub fn compute_unified_circuit_params_recursion_layer(
//     binary_image: &[u32],
//     bytecode: &[u32],
// ) -> Vec<UnrolledCircuitSetupParams> {
//     let eval_fns: Vec<fn(&[u32], &[u32], &Worker) -> UnrolledCircuitPrecomputations<Global>> =
//         vec![unified_reduced_machine_circuit_setup::<Global, Global>];
//     compute_unrolled_circuits_params_impl(binary_image, bytecode, &eval_fns)
// }

pub fn compute_setup_commitment(
    setup: GKRSetup<BabyBearField>,
    cap_size: usize,
    lde_factor: usize,
    worker: &Worker,
) -> MerkleTreeCapVarLength {
    assert!(lde_factor.is_power_of_two());

    todo!();
}

// fn compute_unrolled_circuits_params_impl(
//     binary_image: &[u32],
//     bytecode: &[u32],
//     circuits: &[fn(&[u32], &[u32], &Worker) -> UnrolledCircuitPrecomputations<Global, Global>],
// ) -> Vec<UnrolledCircuitSetupParams> {
//     assert!(binary_image.len() >= bytecode.len());
//     let worker = prover::worker::Worker::new();
//     use prover::merkle_trees::MerkleTreeConstructor;

//     let mut results = Vec::with_capacity(circuits.len());
//     for eval_fn in circuits.iter() {
//         let precomp = (eval_fn)(binary_image, bytecode, &worker);
//         let num_cycles = (precomp.trace_len - 1) as u32;
//         let setup = DefaultTreeConstructor::dump_caps(&precomp.setup.trees);
//         let setup: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS] = setup
//             .into_iter()
//             .map(|el| MerkleTreeCap {
//                 cap: el.cap.try_into().unwrap(),
//             })
//             .collect::<Vec<_>>()
//             .try_into()
//             .unwrap();

//         results.push(UnrolledCircuitSetupParams {
//             family_idx: precomp.family_idx as u32,
//             capacity: num_cycles,
//             setup_caps: setup,
//         });
//     }
//     // sort by family index
//     results.sort_by(|a, b| a.family_idx.cmp(&b.family_idx));

//     results
// }

// pub fn compute_delegation_circuits_params() -> Vec<DelegationCircuitSetupParams> {
//     let worker = prover::worker::Worker::new();
//     use prover::merkle_trees::MerkleTreeConstructor;
//     let all_circuits = all_delegation_circuits_precomputations::<Global, Global>(&worker);
//     let mut results = Vec::with_capacity(all_circuits.len());
//     for (delegation_type, prec) in all_circuits.into_iter() {
//         let delegation_type = delegation_type as u32;
//         let num_delegation_requests = (prec.trace_len - 1) as u32;
//         let setup = DefaultTreeConstructor::dump_caps(&prec.setup.trees);
//         let setup: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS] = setup
//             .into_iter()
//             .map(|el| MerkleTreeCap {
//                 cap: el.cap.try_into().unwrap(),
//             })
//             .collect::<Vec<_>>()
//             .try_into()
//             .unwrap();
//         results.push((delegation_type, num_delegation_requests, setup));
//     }

//     results
// }

// pub fn generate_delegation_circuits_artifacts() -> String {
//     use prover::cap_holder::array_to_tokens;
//     use quote::quote;

//     let all_params = compute_delegation_circuits_params();

//     let mut streams = Vec::with_capacity(all_params.len());

//     for (delegation_type, num_delegation_requests, setup) in all_params.into_iter() {
//         let caps_stream = array_to_tokens(&setup);
//         let t = quote! {
//             (
//                 #delegation_type,
//                 #num_delegation_requests,
//                 #caps_stream
//             )
//         };
//         streams.push(t);
//     }

//     use quote::TokenStreamExt;

//     let mut full_stream = proc_macro2::TokenStream::new();
//     full_stream.append_separated(
//         streams.into_iter().map(|el| {
//             quote! { #el }
//         }),
//         quote! {,},
//     );

//     let cap_size = CAP_SIZE;
//     let num_cosets = NUM_COSETS;

//     let description = quote! {
//         pub const ALL_DELEGATION_CIRCUITS_PARAMS: &[(u32, u32, [MerkleTreeCap<#cap_size>; #num_cosets])] = & [#full_stream];
//     }.to_string();

//     description
// }

// pub fn binary_u8_to_u32(binary_u8: &[u8]) -> Vec<u32> {
//     assert_eq!(binary_u8.len() % core::mem::size_of::<u32>(), 0);
//     let mut binary = Vec::with_capacity(binary_u8.len() / core::mem::size_of::<u32>());
//     for el in binary_u8.as_chunks::<4>().0 {
//         binary.push(u32::from_le_bytes(*el));
//     }
//     binary
// }

// pub fn read_binary(path: &Path) -> (Vec<u8>, Vec<u32>) {
//     use std::io::Read;
//     let mut file = std::fs::File::open(path).expect("must open provided file");
//     let mut buffer = vec![];
//     file.read_to_end(&mut buffer).expect("must read the file");
//     let binary = binary_u8_to_u32(&buffer);
//     (buffer, binary)
// }

// pub fn read_and_pad_binary(path: &Path) -> (Vec<u8>, Vec<u32>) {
//     let (mut buffer, mut binary) = read_binary(path);
//     pad_bytecode_bytes_for_proving(&mut buffer);
//     pad_bytecode_for_proving(&mut binary);
//     (buffer, binary)
// }

// pub fn pad_binary(mut buffer: Vec<u8>) -> (Vec<u8>, Vec<u32>) {
//     let mut binary = binary_u8_to_u32(&buffer);
//     pad_bytecode_bytes_for_proving(&mut buffer);
//     pad_bytecode_for_proving(&mut binary);
//     (buffer, binary)
// }

// pub fn compute_and_save_params(
//     binary_image_path: &Path,
//     bytecode_path: &Path,
//     destination: &Path,
//     gen_fn: fn(&[u32], &[u32]) -> Vec<UnrolledCircuitSetupParams>,
// ) {
//     use sha3::Digest;
//     let (raw_binary_image, binary_image) = read_and_pad_binary(binary_image_path);
//     let (raw_bytecode, bytecode) = read_and_pad_binary(bytecode_path);
//     let setups = (gen_fn)(&binary_image, &bytecode);
//     let binary_image_hash = sha3::Keccak256::digest(&raw_binary_image);
//     let bytecode_hash = sha3::Keccak256::digest(&raw_bytecode);
//     let path = destination.join(format!(
//         "{}_{}.json",
//         hex::encode(binary_image_hash),
//         hex::encode(bytecode_hash)
//     ));
//     let file = std::fs::File::create(path).expect("create result file");
//     serde_json::to_writer(file, &(setups, inits_setup)).expect("must serialize");
// }

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;

    // #[cfg(test)]
    // #[test]
    // fn generate_all() {
    //     skip_if_ci!();
    //     let description = generate_delegation_circuits_artifacts();

    //     let mut dst = std::fs::File::create("generated/all_delegation_circuits_params.rs").unwrap();
    //     use std::io::Write;
    //     dst.write_all(&description.as_bytes()).unwrap();
    // }

    // #[cfg(test)]
    // #[test]
    // fn test_generate_unrolled_base() {
    //     skip_if_ci!();
    //     compute_and_save_params(
    //         Path::new("../../examples/basic_fibonacci/app.bin"),
    //         Path::new("../../examples/basic_fibonacci/app.text"),
    //         Path::new("./"),
    //         compute_unrolled_circuits_params_base_layer_unsigned_only,
    //     );
    // }
}
