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

    // The decoder table for the unified family (family 128) is produced by the
    // same preprocessing the witness-gen oracle uses, so build a throwaway
    // oracle over an empty trace just to read it out.
    let oracle = UnifiedRiscvCircuitOracle::new::<BabyBearField>(
        &[],
        text_section,
        common_constants::ROM_WORD_SIZE,
    );
    let decoder_table_data: Vec<Option<ExecutorFamilyDecoderData>> =
        oracle.decoder_table_with_options().to_vec();

    let trace_len = ::unified_reduced_machine::DOMAIN_SIZE;
    let setup = GKRSetup::construct(
        &table_driver,
        &decoder_table_data,
        trace_len,
        &compiled_circuit,
    );

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn = Some(UnrolledCircuitWitnessEvalFn::Unified {
        witness_fn: ::unified_reduced_machine::witness_eval_fn,
        decoder_table: decoder_table_data.to_vec_in(A::default()),
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
