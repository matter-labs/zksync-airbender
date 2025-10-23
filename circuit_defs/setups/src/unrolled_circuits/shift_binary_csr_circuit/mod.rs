use super::*;

pub fn shift_binary_csr_circuit_setup<A: GoodAllocator, B: GoodAllocator>(
    binary_image: &[u32],
    bytecode: &[u32],
    worker: &Worker,
) -> UnrolledCircuitPrecomputations<A, B> {
    let circuit = ::shift_binary_csr::get_circuit_for_rom_bound::<
        { ::shift_binary_csr::ROM_ADDRESS_SPACE_SECOND_WORD_BITS },
    >(binary_image);
    let table_driver = ::shift_binary_csr::get_table_driver(binary_image);
    let (decoder_table_data, witness_gen_data) =
        ::shift_binary_csr::get_decoder_table::<B>(bytecode);
    use prover::cs::machine::ops::unrolled::materialize_flattened_decoder_table;
    let decoder_table = materialize_flattened_decoder_table::<Mersenne31Field>(&decoder_table_data);

    let twiddles: Twiddles<_, A> = Twiddles::new(::shift_binary_csr::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        ::shift_binary_csr::DOMAIN_SIZE,
        ::shift_binary_csr::LDE_FACTOR,
        ::shift_binary_csr::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table,
            ::shift_binary_csr::DOMAIN_SIZE,
            &circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            ::shift_binary_csr::LDE_FACTOR,
            ::shift_binary_csr::TREE_CAP_SIZE,
            &worker,
        );

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn = Some(UnrolledCircuitWitnessEvalFn::NonMemory {
        witness_fn: ::shift_binary_csr::witness_eval_fn_for_gpu_tracer,
        decoder_table: witness_gen_data,
        default_pc_value_in_padding: 4,
    });

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    UnrolledCircuitPrecomputations {
        family_idx: ::shift_binary_csr::FAMILY_IDX,
        trace_len: ::shift_binary_csr::DOMAIN_SIZE,
        lde_factor: ::shift_binary_csr::LDE_FACTOR,
        tree_cap_size: ::shift_binary_csr::TREE_CAP_SIZE,
        compiled_circuit: circuit,
        table_driver,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer: witness_eval_fn,
    }
}
