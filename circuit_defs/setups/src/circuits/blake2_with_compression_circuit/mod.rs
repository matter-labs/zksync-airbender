use super::*;

pub fn get_blake2_with_compression_circuit_setup<A: GoodAllocator + 'static, B: GoodAllocator>(
    worker: &Worker,
) -> DelegationCircuitPrecomputations<A, B> {
    let machine: DelegationProcessorDescription = blake2_with_compression::get_delegation_circuit();
    let table_driver = blake2_with_compression::get_table_driver();

    let twiddles = Twiddles::get(blake2_with_compression::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        blake2_with_compression::DOMAIN_SIZE,
        blake2_with_compression::LDE_FACTOR,
        blake2_with_compression::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len(
            &table_driver,
            blake2_with_compression::DOMAIN_SIZE,
            &machine.compiled_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            blake2_with_compression::LDE_FACTOR,
            blake2_with_compression::TREE_CAP_SIZE,
            &worker,
        );

    DelegationCircuitPrecomputations {
        trace_len: blake2_with_compression::DOMAIN_SIZE,
        lde_factor: blake2_with_compression::LDE_FACTOR,
        tree_cap_size: blake2_with_compression::TREE_CAP_SIZE,
        compiled_circuit: machine,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer: blake2_with_compression::witness_eval_fn_for_gpu_tracer,
    }
}
