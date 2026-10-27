use super::*;

use prover::gkr::prover::setup::GKRSetup;

/// Build the GKR [`CircuitSetup`] for the unified extended-machine circuit (the reduced
/// machine plus unsigned MUL/MULHU and ROM-free sub-word memory). Mirrors
/// [`unified_reduced_machine_circuit_setup`]; the circuit has no bytecode-dependent tables,
/// so only the decoder table depends on the program (`text_section`).
pub fn unified_extended_machine_circuit_setup<A: GoodAllocator + 'static>(
    text_section: &[u32],
    use_caches: bool,
    _worker: &Worker,
) -> CircuitSetup<A> {
    let compiled_circuit = ::unified_extended_machine::get_circuit(use_caches);
    let table_driver = ::unified_extended_machine::get_table_driver();

    use common_constants::*;
    use cs::gkr_circuits::*;
    use riscv_transpiler::ir::ExtendedMachineDecoderConfig;

    let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> = vec![Box::new(UnifiedExtendedMachineDecoder)];
    const SUPPORTED_CSRS: &[u16] = &[
        NON_DETERMINISM_CSR as u16,
        BLAKE2S_DELEGATION_CSR_REGISTER as u16,
        BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
        KECCAK_SPECIAL5_CSR_REGISTER as u16,
        BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
    ];
    let mut preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        ExtendedMachineDecoderConfig,
        true,
        A,
    >(
        text_section,
        &decoders,
        common_constants::ROM_WORD_SIZE,
        SUPPORTED_CSRS,
    );
    let decoder_table = preprocessing_data
        .remove(&EXTENDED_MACHINE_CIRCUIT_FAMILY_IDX)
        .expect("UnifiedExtendedMachineDecoder must produce a family-129 entry");

    let trace_len = 1
        << <::unified_extended_machine::UnifiedExtendedMachineCircuit as RiscVCycleCircuit<
            BabyBearField,
            true,
        >>::trace_len_log2();
    let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &compiled_circuit);

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn = Some(UnrolledCircuitWitnessEvalFn::Unified {
        witness_fn: ::unified_extended_machine::witness_eval_fn,
        decoder_table,
    });

    CircuitSetup {
        family_idx: ::unified_extended_machine::FAMILY_IDX,
        trace_len,
        compiled_circuit,
        table_driver,
        setup,
        witness_eval_fn,
        prover_configs: circuit_common::prover_configs_for_all_levels(
            <::unified_extended_machine::UnifiedExtendedMachineCircuit as RiscVCycleCircuit<
                BabyBearField,
                true,
            >>::prover_config,
        ),
    }
}
