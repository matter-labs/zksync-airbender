use super::*;

pub fn load_store_word_only_circuit_setup<A: GoodAllocator>(
    decoder_table_data: &[Option<ExecutorFamilyDecoderData>],
    bytecode: &[u32],
    use_caches: bool,
    worker: &Worker,
) -> CircuitSetup<A> {
    type C = ::load_store_word_only::LoadStoreWordOnlyCircuit;

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn: Option<
        fn(&mut ColumnMajorWitnessProxy<'_, MemoryCircuitOracle<'_>, BabyBearField>),
    > = Some(::load_store_word_only::witness_eval_fn);

    make_setup_for_with_mem_circuit::<C, A>(
        witness_eval_fn,
        bytecode,
        decoder_table_data,
        use_caches,
    )
}
