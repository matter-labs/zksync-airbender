use super::*;

pub fn mul_div_unsigned_circuit_setup<A: GoodAllocator + 'static, B: GoodAllocator>(
    binary_image: &[u32],
    bytecode: &[u32],
    worker: &Worker,
) -> UnrolledCircuitPrecomputations<A, B> {
    let circuit = ::mul_div_unsigned::get_circuit_for_rom_bound::<
        { ::mul_div_unsigned::ROM_ADDRESS_SPACE_SECOND_WORD_BITS },
    >(binary_image);
    let table_driver = ::mul_div_unsigned::get_table_driver(binary_image);
    let (decoder_table_data, witness_gen_data) =
        ::mul_div_unsigned::get_decoder_table::<B>(bytecode);
    use prover::cs::machine::ops::unrolled::materialize_flattened_decoder_table;
    let decoder_table = materialize_flattened_decoder_table::<Mersenne31Field>(&decoder_table_data);

    let twiddles = Twiddles::get(::mul_div_unsigned::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        ::mul_div_unsigned::DOMAIN_SIZE,
        ::mul_div_unsigned::LDE_FACTOR,
        ::mul_div_unsigned::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table,
            ::mul_div_unsigned::DOMAIN_SIZE,
            &circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            ::mul_div_unsigned::LDE_FACTOR,
            ::mul_div_unsigned::TREE_CAP_SIZE,
            &worker,
        );

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn = Some(UnrolledCircuitWitnessEvalFn::NonMemory {
        witness_fn: ::mul_div_unsigned::witness_eval_fn_for_gpu_tracer,
        decoder_table: witness_gen_data,
        default_pc_value_in_padding: 4,
    });

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    UnrolledCircuitPrecomputations {
        family_idx: ::mul_div_unsigned::FAMILY_IDX,
        trace_len: ::mul_div_unsigned::DOMAIN_SIZE,
        lde_factor: ::mul_div_unsigned::LDE_FACTOR,
        tree_cap_size: ::mul_div_unsigned::TREE_CAP_SIZE,
        compiled_circuit: circuit,
        table_driver,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer: witness_eval_fn,
    }
}
