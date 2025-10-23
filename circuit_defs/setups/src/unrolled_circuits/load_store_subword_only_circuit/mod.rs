use super::*;

pub fn load_store_subword_only_circuit_setup<A: GoodAllocator + 'static, B: GoodAllocator>(
    binary_image: &[u32],
    bytecode: &[u32],
    worker: &Worker,
) -> UnrolledCircuitPrecomputations<A, B> {
    let circuit = ::load_store_subword_only::get_circuit_for_rom_bound::<
        { ::load_store_subword_only::ROM_ADDRESS_SPACE_SECOND_WORD_BITS },
    >(binary_image);
    let table_driver = ::load_store_subword_only::get_table_driver(binary_image);
    let (decoder_table_data, witness_gen_data) =
        ::load_store_subword_only::get_decoder_table::<B>(bytecode);
    use prover::cs::machine::ops::unrolled::materialize_flattened_decoder_table;
    let decoder_table = materialize_flattened_decoder_table::<Mersenne31Field>(&decoder_table_data);

    let twiddles = Twiddles::get(::load_store_subword_only::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        ::load_store_subword_only::DOMAIN_SIZE,
        ::load_store_subword_only::LDE_FACTOR,
        ::load_store_subword_only::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table,
            ::load_store_subword_only::DOMAIN_SIZE,
            &circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            ::load_store_subword_only::LDE_FACTOR,
            ::load_store_subword_only::TREE_CAP_SIZE,
            &worker,
        );

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn = Some(UnrolledCircuitWitnessEvalFn::Memory {
        witness_fn: ::load_store_subword_only::witness_eval_fn_for_gpu_tracer,
        decoder_table: witness_gen_data,
    });

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    UnrolledCircuitPrecomputations {
        family_idx: ::load_store_subword_only::FAMILY_IDX,
        trace_len: ::load_store_subword_only::DOMAIN_SIZE,
        lde_factor: ::load_store_subword_only::LDE_FACTOR,
        tree_cap_size: ::load_store_subword_only::TREE_CAP_SIZE,
        compiled_circuit: circuit,
        table_driver,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer: witness_eval_fn,
    }
}
