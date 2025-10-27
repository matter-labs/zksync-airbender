use super::*;

pub fn get_bigint_with_control_circuit_setup<A: GoodAllocator + 'static, B: GoodAllocator>(
    worker: &Worker,
) -> DelegationCircuitPrecomputations<A, B> {
    let machine: DelegationProcessorDescription = bigint_with_control::get_delegation_circuit();
    let table_driver = bigint_with_control::get_table_driver();

    let twiddles = Twiddles::get(bigint_with_control::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        bigint_with_control::DOMAIN_SIZE,
        bigint_with_control::LDE_FACTOR,
        bigint_with_control::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len(
            &table_driver,
            bigint_with_control::DOMAIN_SIZE,
            &machine.compiled_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            bigint_with_control::LDE_FACTOR,
            bigint_with_control::TREE_CAP_SIZE,
            &worker,
        );

    DelegationCircuitPrecomputations {
        trace_len: bigint_with_control::DOMAIN_SIZE,
        lde_factor: bigint_with_control::LDE_FACTOR,
        tree_cap_size: bigint_with_control::TREE_CAP_SIZE,
        compiled_circuit: machine,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer: bigint_with_control::witness_eval_fn_for_gpu_tracer,
    }
}
