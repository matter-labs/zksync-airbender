use prover::cs::gkr_circuits::ExecutorFamilyDecoderData;

use super::*;

pub fn add_sub_lui_auipc_mop_circuit_setup<A: GoodAllocator>(
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    use_caches: bool,
    worker: &Worker,
) -> CircuitSetup<A> {
    type C = ::add_sub_lui_auipc_mop::AddSubLuiAuipcMopCircuit;

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn: Option<
        fn(&mut ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BabyBearField>),
    > = Some(::add_sub_lui_auipc_mop::witness_eval_fn);

    make_setup_for_non_mem_circuit::<C, A>(witness_eval_fn, 4, decoder_table_data, use_caches)
}
