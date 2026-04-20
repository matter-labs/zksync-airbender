use super::*;

pub fn shift_binary_circuit_setup<A: GoodAllocator>(
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    use_caches: bool,
    worker: &Worker,
) -> CircuitSetup<A> {
    type C = ::shift_binary::ShiftBinaryCircuit;

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn: Option<
        fn(&mut ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BabyBearField>),
    > = Some(::shift_binary::witness_eval_fn);

    make_setup_for_non_mem_circuit::<C, A>(witness_eval_fn, 4, decoder_table_data, use_caches)
}
