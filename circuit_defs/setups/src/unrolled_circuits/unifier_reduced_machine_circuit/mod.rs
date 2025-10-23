use super::*;

pub fn unified_reduced_machine_circuit_setup<A: GoodAllocator, B: GoodAllocator>(
    binary_image: &[u32],
    bytecode: &[u32],
    worker: &Worker,
) -> UnrolledCircuitPrecomputations<A, B> {
    let circuit = ::unified_reduced_machine::get_circuit_for_rom_bound::<
        { ::unified_reduced_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS },
    >(binary_image);
    let table_driver = ::unified_reduced_machine::get_table_driver(binary_image);
    let (decoder_table_data, witness_gen_data) =
        ::unified_reduced_machine::get_decoder_table::<B>(bytecode);
    use prover::cs::machine::ops::unrolled::materialize_flattened_decoder_table;
    let decoder_table = materialize_flattened_decoder_table::<Mersenne31Field>(&decoder_table_data);

    let twiddles: Twiddles<_, A> = Twiddles::new(::unified_reduced_machine::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        ::unified_reduced_machine::DOMAIN_SIZE,
        ::unified_reduced_machine::LDE_FACTOR,
        ::unified_reduced_machine::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table,
            ::unified_reduced_machine::DOMAIN_SIZE,
            &circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            ::unified_reduced_machine::LDE_FACTOR,
            ::unified_reduced_machine::TREE_CAP_SIZE,
            &worker,
        );

    #[cfg(feature = "witness_eval_fn")]
    let witness_eval_fn = Some(UnrolledCircuitWitnessEvalFn::Unified {});

    #[cfg(not(feature = "witness_eval_fn"))]
    let witness_eval_fn = None;

    UnrolledCircuitPrecomputations {
        family_idx: ::unified_reduced_machine::FAMILY_IDX,
        trace_len: ::unified_reduced_machine::DOMAIN_SIZE,
        lde_factor: ::unified_reduced_machine::LDE_FACTOR,
        tree_cap_size: ::unified_reduced_machine::TREE_CAP_SIZE,
        compiled_circuit: circuit,
        table_driver,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer: witness_eval_fn,
    }
}
