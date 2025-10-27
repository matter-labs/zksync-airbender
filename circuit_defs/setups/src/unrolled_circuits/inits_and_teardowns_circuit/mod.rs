use super::*;

pub fn inits_and_teardowns_circuit_setup<A: GoodAllocator + 'static, B: GoodAllocator>(
    binary_image: &[u32],
    _bytecode: &[u32],
    worker: &Worker,
) -> UnrolledCircuitPrecomputations<A, B> {
    let circuit = ::inits_and_teardowns::get_circuit_for_rom_bound::<
        { ::inits_and_teardowns::ROM_ADDRESS_SPACE_SECOND_WORD_BITS },
    >(binary_image);
    let table_driver = ::inits_and_teardowns::get_table_driver(binary_image);

    let twiddles = Twiddles::get(::inits_and_teardowns::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        ::inits_and_teardowns::DOMAIN_SIZE,
        ::inits_and_teardowns::LDE_FACTOR,
        ::inits_and_teardowns::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &[],
            ::inits_and_teardowns::DOMAIN_SIZE,
            &circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            ::inits_and_teardowns::LDE_FACTOR,
            ::inits_and_teardowns::TREE_CAP_SIZE,
            &worker,
        );

    UnrolledCircuitPrecomputations {
        family_idx: ::inits_and_teardowns::FAMILY_IDX,
        trace_len: ::inits_and_teardowns::DOMAIN_SIZE,
        lde_factor: ::inits_and_teardowns::LDE_FACTOR,
        tree_cap_size: ::inits_and_teardowns::TREE_CAP_SIZE,
        compiled_circuit: circuit,
        table_driver,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer: None,
    }
}
