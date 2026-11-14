use super::CanonicalCircuitSetup;
use crate::upstream::{
    add_sub_lui_auipc_mop_circuit_setup, jump_branch_slt_circuit_setup,
    load_store_subword_only_circuit_setup, load_store_word_only_circuit_setup,
    mul_div_unsigned_circuit_setup,
    opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization,
    opcodes_for_reduced_machine, process_predecoded_into_separate_tables,
    shift_binary_circuit_setup, unified_reduced_machine_2_22_circuit_setup_from_decoder,
    unified_reduced_machine_circuit_setup_from_decoder, ExecutorFamilyDecoderData,
    OpcodeFamilyDecoder, UnifiedReducedMachineDecoder, ROM_WORD_SIZE,
};
use crate::ExecutionKind;
use execution_prover_model::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};
use execution_prover_model::MachineType;
use riscv_transpiler::ir::simple_instruction_set::{
    preprocess_bytecode, preprocess_bytecode_for_setup_and_execution, Instruction,
};
use riscv_transpiler::ir::{
    FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig,
};
use std::alloc::Global;
use std::collections::HashMap;
use worker::Worker;

pub struct BinaryPreprocessing {
    pub execution_instructions: Vec<Instruction>,
    decoder_tables: HashMap<u8, Vec<Option<ExecutorFamilyDecoderData>>>,
}

/// Share instruction decoding when setup and execution use the same decoder.
pub fn preprocess_binary(
    machine: MachineType,
    kinds: &[ExecutionKind],
    text: &[u32],
) -> BinaryPreprocessing {
    let (setup_instructions, execution_instructions) = match machine {
        // Full setup has always used the unsigned decoder, even though its
        // execution tape enables signed operations. Keep those streams distinct.
        MachineType::Full => (
            preprocess_bytecode::<FullUnsignedMachineDecoderConfig, false>(text),
            preprocess_bytecode::<FullMachineDecoderConfig, true>(text),
        ),
        MachineType::FullUnsigned => {
            preprocess_bytecode_for_setup_and_execution::<FullUnsignedMachineDecoderConfig>(text)
        }
        MachineType::Reduced => {
            preprocess_bytecode_for_setup_and_execution::<ReducedMachineDecoderConfig>(text)
        }
    };
    let mut decoder_tables = HashMap::new();
    if kinds.contains(&ExecutionKind::Unrolled) {
        let supported_csrs: Vec<u16> =
            DelegationCircuitType::get_delegation_types_for_machine_type(machine)
                .iter()
                .map(DelegationCircuitType::get_delegation_type_id)
                .collect();
        let decoders = match machine {
            MachineType::Full | MachineType::FullUnsigned => opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
            MachineType::Reduced => opcodes_for_reduced_machine(),
        };
        decoder_tables.extend(process_predecoded_into_separate_tables::<true, Global>(
            &setup_instructions,
            &decoders,
            ROM_WORD_SIZE,
            &supported_csrs,
        ));
    }
    if kinds.iter().any(|kind| kind.is_unified()) {
        assert_eq!(
            machine,
            MachineType::Reduced,
            "Unified execution requires the Reduced machine"
        );
        let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> =
            vec![Box::new(UnifiedReducedMachineDecoder)];
        let supported_csrs = [
            common_constants::NON_DETERMINISM_CSR as u16,
            common_constants::BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            common_constants::KECCAK_SPECIAL5_CSR_REGISTER as u16,
            common_constants::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ];
        decoder_tables.extend(process_predecoded_into_separate_tables::<true, Global>(
            &setup_instructions,
            &decoders,
            ROM_WORD_SIZE,
            &supported_csrs,
        ));
    }
    BinaryPreprocessing {
        execution_instructions,
        decoder_tables,
    }
}

pub fn circuit_types_for_variant(
    kind: ExecutionKind,
    machine: MachineType,
) -> Vec<UnrolledCircuitType> {
    match kind {
        ExecutionKind::Unrolled => {
            let memory = UnrolledMemoryCircuitType::get_circuit_types_for_machine_type(machine)
                .iter()
                .copied()
                .map(UnrolledCircuitType::Memory);
            let non_memory =
                UnrolledNonMemoryCircuitType::get_circuit_types_for_machine_type(machine)
                    .iter()
                    .copied()
                    .map(UnrolledCircuitType::NonMemory);
            memory.chain(non_memory).collect()
        }
        ExecutionKind::Unified | ExecutionKind::Unified22 => {
            assert_eq!(
                machine,
                MachineType::Reduced,
                "Unified execution requires the Reduced machine"
            );
            let CircuitType::Unrolled(circuit) = kind.unified_circuit().unwrap() else {
                unreachable!()
            };
            vec![circuit]
        }
        ExecutionKind::L1Wrap => vec![],
    }
}

/// Standalone circuit construction for callers that need only one circuit.
pub fn build_unrolled_setup(
    machine_type: MachineType,
    circuit_type: UnrolledCircuitType,
    binary_image: &[u32],
    text_section: &[u32],
    worker: &Worker,
) -> CanonicalCircuitSetup {
    let kind = match circuit_type {
        UnrolledCircuitType::Unified => ExecutionKind::Unified,
        UnrolledCircuitType::Unified22 => ExecutionKind::Unified22,
        _ => ExecutionKind::Unrolled,
    };
    let preprocessing = preprocess_binary(machine_type, &[kind], text_section);
    build_unrolled_setup_with_preprocessing(circuit_type, binary_image, &preprocessing, worker)
}

pub fn build_unrolled_setup_with_preprocessing(
    circuit_type: UnrolledCircuitType,
    binary_image: &[u32],
    preprocessing: &BinaryPreprocessing,
    worker: &Worker,
) -> CanonicalCircuitSetup {
    let family_idx = match circuit_type {
        UnrolledCircuitType::Memory(c) => c.get_family_idx(),
        UnrolledCircuitType::NonMemory(c) => c.get_family_idx(),
        UnrolledCircuitType::Unified => {
            let decoder = preprocessing.decoder_tables
                [&common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX]
                .clone();
            return CanonicalCircuitSetup::Riscv(
                unified_reduced_machine_circuit_setup_from_decoder::<Global>(
                    binary_image,
                    decoder,
                    true,
                    worker,
                ),
            );
        }
        UnrolledCircuitType::Unified22 => {
            let decoder = preprocessing.decoder_tables
                [&common_constants::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX]
                .clone();
            return CanonicalCircuitSetup::Riscv(
                unified_reduced_machine_2_22_circuit_setup_from_decoder::<Global>(
                    binary_image,
                    decoder,
                    true,
                    worker,
                ),
            );
        }
        UnrolledCircuitType::InitsAndTeardowns => panic!("inits-and-teardowns is a common circuit"),
    };
    let table_data = preprocessing
        .decoder_tables
        .get(&family_idx)
        .expect("missing decoder data for circuit family");
    let setup = match circuit_type {
        UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreWordOnly) => {
            load_store_word_only_circuit_setup::<Global>(table_data, binary_image, true, worker)
        }
        UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreSubwordOnly) => {
            load_store_subword_only_circuit_setup::<Global>(table_data, binary_image, true, worker)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop) => {
            add_sub_lui_auipc_mop_circuit_setup::<Global>(table_data, true, worker)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::JumpBranchSlt) => {
            jump_branch_slt_circuit_setup::<Global>(table_data, true, worker)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::ShiftBinary) => {
            shift_binary_circuit_setup::<Global>(table_data, true, worker)
        }
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::MulDivUnsigned) => {
            mul_div_unsigned_circuit_setup::<Global>(table_data, true, worker)
        }
        UnrolledCircuitType::InitsAndTeardowns
        | UnrolledCircuitType::Unified
        | UnrolledCircuitType::Unified22 => unreachable!(),
    };
    CanonicalCircuitSetup::Riscv(setup)
}
