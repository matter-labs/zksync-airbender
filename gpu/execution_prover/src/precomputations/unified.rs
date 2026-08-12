use super::UnrolledUnifiedSetup;
use gpu_core::primitives::field::BF;
use gpu_trace::witness::circuit_type::{CircuitType, UnrolledCircuitType};

use crate::upstream::{CSExecutorFamilyDecoderData, CpuGKRSetup};
use worker::Worker;

/// Build the unified-circuit setup from the canonical unified artifact. Unlike
/// the per-family path in `build_unrolled_setup`, this uses the unified 5-CSR
/// `UnifiedReducedMachineDecoder` over `ReducedMachineDecoderConfig` (family
/// 128), NOT the per-family decoder set.
pub(crate) fn build_unified_setup_direct(
    binary_image: &[u32],
    text_section: &[u32],
    _worker: &Worker,
) -> UnrolledUnifiedSetup {
    use crate::upstream::{
        build_unified_table_driver, get_unified_reduced_machine_circuit, OpcodeFamilyDecoder,
        UnifiedReducedMachineDecoder, ROM_WORD_SIZE,
    };

    let compiled_circuit = get_unified_reduced_machine_circuit(true);

    // Decoder table for the five supported reduced-machine CSRs.
    let decoder_table = {
        use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX;
        use common_constants::{
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER, BLAKE2S_DELEGATION_CSR_REGISTER,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER, KECCAK_SPECIAL5_CSR_REGISTER,
            NON_DETERMINISM_CSR,
        };
        use riscv_transpiler::ir::ReducedMachineDecoderConfig;
        use std::alloc::Global;
        let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> =
            vec![Box::new(UnifiedReducedMachineDecoder)];
        const SUPPORTED_CSRS: &[u16] = &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ];
        let mut preprocessing_data =
            crate::upstream::process_binary_into_separate_tables_ext::<
                BF,
                ReducedMachineDecoderConfig,
                true,
                Global,
            >(text_section, &decoders, ROM_WORD_SIZE, SUPPORTED_CSRS);
        preprocessing_data
            .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
            .expect("UnifiedReducedMachineDecoder must produce a family-128 entry")
    };

    // Real binary-derived table content lives in the prove-time table driver.
    let table_driver = build_unified_table_driver::<BF>(binary_image);

    let trace_len = CircuitType::Unrolled(UnrolledCircuitType::Unified).get_domain_size();
    let setup = CpuGKRSetup::construct(&table_driver, &decoder_table, trace_len, &compiled_circuit);

    let decoder_data: Vec<CSExecutorFamilyDecoderData> = decoder_table
        .iter()
        .map(|el| el.as_ref().copied().unwrap_or_default())
        .collect();

    UnrolledUnifiedSetup {
        compiled_circuit,
        setup,
        decoder_data,
    }
}

#[cfg(test)]
mod unified_setup_tests {
    use super::*;
    use crate::upstream::OutputType;

    #[test]
    fn cpu_unified_setup_constructs_expected_setup() {
        let worker = Worker::new();
        // A full padded ROM image is required for unified decoder preprocessing.
        let n = (1usize << (16 + common_constants::ROM_SECOND_WORD_BITS)) / 4;
        let binary = vec![0u32; n];
        let s = build_unified_setup_direct(&binary, &binary, &worker);
        assert!(s
            .compiled_circuit
            .global_output_map
            .contains_key(&OutputType::PermutationProduct));
        assert!(s
            .compiled_circuit
            .global_output_map
            .contains_key(&OutputType::InitsAndTeardownsProduct));
        assert!(!s.compiled_circuit.memory_layout.teardown_sets.is_empty());
    }
}
