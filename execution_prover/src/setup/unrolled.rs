use super::CanonicalCircuitSetup;
use crate::upstream::{
    add_sub_lui_auipc_mop_circuit_setup, jump_branch_slt_circuit_setup,
    load_store_subword_only_circuit_setup, load_store_word_only_circuit_setup,
    mul_div_unsigned_circuit_setup,
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    opcodes_for_reduced_machine, process_binary_into_separate_tables_ext,
    shift_binary_circuit_setup, unified_reduced_machine_circuit_setup, BF, ROM_WORD_SIZE,
};
use execution_prover_model::circuit_type::{
    DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use execution_prover_model::MachineType;
use riscv_transpiler::ir::{FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig};
use std::alloc::Global;
use worker::Worker;

pub fn build_unrolled_setup(
    machine_type: MachineType,
    circuit_type: UnrolledCircuitType,
    binary_image: &[u32],
    text_section: &[u32],
    worker: &Worker,
) -> CanonicalCircuitSetup {
    let family_idx = match circuit_type {
        UnrolledCircuitType::Memory(c) => c.get_family_idx(),
        UnrolledCircuitType::NonMemory(c) => c.get_family_idx(),
        UnrolledCircuitType::Unified => {
            return CanonicalCircuitSetup::Riscv(unified_reduced_machine_circuit_setup::<Global>(
                binary_image,
                text_section,
                true,
                worker,
            ))
        }
        UnrolledCircuitType::InitsAndTeardowns => {
            panic!("inits-and-teardowns is binary-independent and is set up as a common circuit")
        }
    };
    let supported_csrs: Vec<u16> =
        DelegationCircuitType::get_delegation_types_for_machine_type(machine_type)
            .iter()
            .map(DelegationCircuitType::get_delegation_type_id)
            .collect();
    let preprocessing = match machine_type {
        MachineType::Full | MachineType::FullUnsigned => {
            process_binary_into_separate_tables_ext::<BF, FullUnsignedMachineDecoderConfig, true, Global>(
                text_section,
                &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
                ROM_WORD_SIZE,
                &supported_csrs,
            )
        }
        MachineType::Reduced => {
            process_binary_into_separate_tables_ext::<BF, ReducedMachineDecoderConfig, true, Global>(
                text_section,
                &opcodes_for_reduced_machine(),
                ROM_WORD_SIZE,
                &supported_csrs,
            )
        }
    };
    let table_data = preprocessing
        .get(&family_idx)
        .expect("missing decoder data for circuit family")
        .clone();

    let setup = match circuit_type {
        UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreWordOnly) => {
            load_store_word_only_circuit_setup::<Global>(&table_data, binary_image, true, worker)
        }
        UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreSubwordOnly) => {
            load_store_subword_only_circuit_setup::<Global>(&table_data, binary_image, true, worker)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop) => {
            add_sub_lui_auipc_mop_circuit_setup::<Global>(&table_data, true, worker)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::JumpBranchSlt) => {
            jump_branch_slt_circuit_setup::<Global>(&table_data, true, worker)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::ShiftBinary) => {
            shift_binary_circuit_setup::<Global>(&table_data, true, worker)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::MulDivUnsigned) => {
            mul_div_unsigned_circuit_setup::<Global>(&table_data, true, worker)
        }
        UnrolledCircuitType::InitsAndTeardowns | UnrolledCircuitType::Unified => unreachable!(),
    };
    CanonicalCircuitSetup::Riscv(setup)
}
