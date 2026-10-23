use super::*;

use prover::gkr::prover::setup::GKRSetup;

/// Build the GKR [`CircuitSetup`] for the unified reduced-machine circuit.
///
/// The unified circuit folds every executor family plus its inline
/// inits-and-teardowns into a single GKR circuit, so unlike the per-family
/// path there is exactly one setup. Mirrors [`make_setup_for_non_mem_circuit`]:
/// the compiled artifact is bytecode-independent, the table driver carries the
/// bytecode-dependent special-table content (from `binary_image`), and the
/// decoder table is derived from `text_section`.
pub fn unified_reduced_machine_circuit_setup<A: GoodAllocator + 'static>(
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    worker: &Worker,
) -> CircuitSetup<A> {
    let compiled_circuit = ::unified_reduced_machine::get_circuit(use_caches);
    let table_driver = ::unified_reduced_machine::get_table_driver(binary_image);
    let trace_len = 1
        << <::unified_reduced_machine::UnifiedReducedMachineCircuit as RiscVCycleCircuit<
            BabyBearField,
            true,
        >>::trace_len_log2();
    unified_circuit_setup_from_parts::<A>(
        compiled_circuit,
        table_driver,
        trace_len,
        text_section,
        ::unified_reduced_machine::witness_eval_fn,
        <::unified_reduced_machine::UnifiedReducedMachineCircuit as RiscVCycleCircuit<
            BabyBearField,
            true,
        >>::prover_config,
        worker,
    )
}

/// Shared body of the unified setups: the decoder table is derived from
/// `text_section`, the setup from the compiled artifact of the selected trace
/// length.
pub(super) fn unified_circuit_setup_from_parts<A: GoodAllocator + 'static>(
    compiled_circuit: GKRCircuitArtifact<BabyBearField>,
    table_driver: TableDriver<BabyBearField>,
    trace_len: usize,
    text_section: &[u32],
    witness_fn: fn(
        &'_ mut ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, BabyBearField>,
    ),
    prover_config: fn(SecurityLevel) -> ProverConfig,
    _worker: &Worker,
) -> CircuitSetup<A> {
    use common_constants::*;
    use cs::gkr_circuits::*;
    use riscv_transpiler::ir::ReducedMachineDecoderConfig;

    let decoders: Vec<Box<dyn OpcodeFamilyDecoder>> = vec![Box::new(UnifiedReducedMachineDecoder)];
    const SUPPORTED_CSRS: &[u16] = &[
        NON_DETERMINISM_CSR as u16,
        BLAKE2S_DELEGATION_CSR_REGISTER as u16,
        BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
        KECCAK_SPECIAL5_CSR_REGISTER as u16,
        BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
    ];
    let mut preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        ReducedMachineDecoderConfig,
        true,
        A,
    >(
        text_section,
        &decoders,
        common_constants::ROM_WORD_SIZE,
        SUPPORTED_CSRS,
    );
    let decoder_table = preprocessing_data
        .remove(&REDUCED_MACHINE_CIRCUIT_FAMILY_IDX)
        .expect("UnifiedReducedMachineDecoder must produce a family-128 entry");

    assert_eq!(compiled_circuit.trace_len, trace_len);
    let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &compiled_circuit);

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = {
        let _ = (witness_fn, decoder_table);
        None
    };

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn = Some(UnrolledCircuitWitnessEvalFn::Unified {
        witness_fn,
        decoder_table,
    });

    CircuitSetup {
        family_idx: ::unified_reduced_machine::FAMILY_IDX,
        trace_len,
        compiled_circuit,
        table_driver,
        setup,
        witness_eval_fn,
        prover_configs: circuit_common::prover_configs_for_all_levels(prover_config),
    }
}
