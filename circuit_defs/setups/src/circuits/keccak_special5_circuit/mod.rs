use super::*;

pub fn get_keccak_special5_circuit_setup<A: GoodAllocator, B: GoodAllocator>(
    worker: &Worker,
) -> DelegationCircuitPrecomputations<A, B> {
    let machine: DelegationProcessorDescription = keccak_special5::get_delegation_circuit();
    let table_driver = keccak_special5::get_table_driver();

    let twiddles: Twiddles<_, A> = Twiddles::new(keccak_special5::DOMAIN_SIZE, &worker);
    let lde_precomputations = LdePrecomputations::new(
        keccak_special5::DOMAIN_SIZE,
        keccak_special5::LDE_FACTOR,
        keccak_special5::LDE_SOURCE_COSETS,
        &worker,
    );
    let setup =
        SetupPrecomputations::<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>::from_tables_and_trace_len(
            &table_driver,
            keccak_special5::DOMAIN_SIZE,
            &machine.compiled_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            keccak_special5::LDE_FACTOR,
            keccak_special5::TREE_CAP_SIZE,
            &worker,
        );

    DelegationCircuitPrecomputations {
        trace_len: keccak_special5::DOMAIN_SIZE,
        lde_factor: keccak_special5::LDE_FACTOR,
        tree_cap_size: keccak_special5::TREE_CAP_SIZE,
        compiled_circuit: machine,
        twiddles,
        lde_precomputations,
        setup,
        witness_eval_fn_for_gpu_tracer: keccak_special5::witness_eval_fn_for_gpu_tracer,
    }
}
