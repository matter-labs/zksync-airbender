use super::UnrolledUnifiedSetup;
use gpu_core::primitives::field::BF;
use gpu_trace::witness::circuit_type::{CircuitType, UnrolledCircuitType};

use crate::upstream::{CSExecutorFamilyDecoderData, CpuGKRSetup};
use worker::Worker;

/// Build the unified-circuit setup directly from the unified cs/prover sources,
/// bit-for-bit mirroring the CPU unified decoder-preprocessing path
/// and `cs::gkr_circuits::unified_reduced_machine::circuit::build_unified_artifact`
/// compile path (the source of truth that produced
/// `unified_reduced_machine_layout_gkr.json`). Unlike the per-family path in
/// `build_unrolled_setup`, this uses the unified 5-CSR
/// `UnifiedReducedMachineDecoder` over `ReducedMachineDecoderConfig`
/// (family 128), NOT the per-family decoder set.
pub(crate) fn build_unified_setup_direct(
    binary_image: &[u32],
    text_section: &[u32],
    _worker: &Worker,
) -> UnrolledUnifiedSetup {
    use crate::upstream::{
        build_unified_table_driver, create_mem_word_only_special_tables,
        unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr,
        unified_reduced_machine_table_addition_fn, BasicAssembly, Circuit, GKRCompiler,
        OpcodeFamilyDecoder, UnifiedReducedMachineDecoder, ROM_SECOND_WORD_BITS, ROM_WORD_SIZE,
    };

    // Compile the unified artifact identically to
    // `build_unified_artifact::<BF>(use_caches = true)`
    // (cs::gkr_circuits::unified_reduced_machine::circuit): register the unified
    // tables + the mem_word_only AlignedRomRead table (sized with empty bytecode
    // so `offset_for_decoder_table` accounts for it), build the circuit body, then
    // compile with inline inits/teardowns at trace_len_log2 = 24.
    let mut cs = BasicAssembly::<BF>::new();
    unified_reduced_machine_table_addition_fn(&mut cs);
    for (table_type, table) in create_mem_word_only_special_tables::<BF, ROM_SECOND_WORD_BITS>(&[])
    {
        cs.add_table_with_content(table_type, table);
    }
    unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr(&mut cs);
    let (cs_output, _) = cs.finalize();
    let compiler = GKRCompiler::<BF>::default();
    let compiled_circuit = compiler.compile_family_circuit_with_inline_inits_and_teardowns(
        cs_output,
        ROM_WORD_SIZE,
        /* num_inits_and_teardowns */ 1,
        /* trace_len_log2 */ 24,
        /* caching_is_allowed */ true,
    );

    // Decoder table via the unified reduced-machine preprocessing (mirrors
    // setups::unrolled_circuits::unifier_reduced_machine_circuit's
    // `unified_reduced_machine_circuit_setup`: `UnifiedReducedMachineDecoder`
    // over `ReducedMachineDecoderConfig` with the 5 supported CSRs). pr-332
    // removed the `UnifiedRiscvCircuitOracle::new` derivation this used to
    // mirror; the oracle is now a plain borrow of an externally built table.
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

    // Real binary-derived AlignedRomRead content lives in the prove-time table
    // driver (matches the second `create_mem_word_only_special_tables` call inside
    // `build_unified_table_driver`).
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

    /// CPU-free geometry oracle: the unified artifact the GPU build-direct path
    /// compiles must match the shape the cs-side test asserts
    /// (`compile_unified_reduced_machine_with_inline_inits_and_teardowns` in
    /// `cs::gkr_circuits::unified_reduced_machine::circuit`).
    #[test]
    fn cpu_unified_setup_direct_matches_cpu_geometry() {
        let worker = Worker::new();
        // 2^(16+ROM_SECOND_WORD_BITS) bytes of zero bytecode for compile-shape parity.
        let n = (1usize << (16 + crate::upstream::ROM_SECOND_WORD_BITS)) / 4;
        let binary = vec![0u32; n];
        let s = build_unified_setup_direct(&binary, &binary, &worker);
        assert_eq!(
            s.compiled_circuit.trace_len,
            CircuitType::Unrolled(UnrolledCircuitType::Unified).get_domain_size()
        );
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
