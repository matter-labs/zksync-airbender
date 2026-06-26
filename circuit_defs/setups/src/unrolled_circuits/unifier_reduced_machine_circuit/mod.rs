use super::*;

use prover::gkr::prover::setup::GKRSetup;
use prover::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;

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
    _worker: &Worker,
) -> CircuitSetup<A> {
    let compiled_circuit = ::unified_reduced_machine::get_circuit(use_caches);
    let table_driver = ::unified_reduced_machine::get_table_driver(binary_image);

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

    let trace_len = ::unified_reduced_machine::DOMAIN_SIZE;
    let setup = GKRSetup::construct(&table_driver, &decoder_table, trace_len, &compiled_circuit);

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn = Some(UnrolledCircuitWitnessEvalFn::Unified {
        witness_fn: ::unified_reduced_machine::witness_eval_fn,
        decoder_table,
    });

    CircuitSetup {
        family_idx: ::unified_reduced_machine::FAMILY_IDX,
        trace_len,
        compiled_circuit,
        table_driver,
        setup,
        witness_eval_fn,
    }
}
