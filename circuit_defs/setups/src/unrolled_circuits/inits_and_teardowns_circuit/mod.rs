use super::*;

pub fn inits_and_teardowns_circuit_setup<A: GoodAllocator>(
    use_caches: bool,
    _worker: &Worker,
) -> CircuitSetup<A> {
    let circuit = ::inits_and_teardowns::get_inits_and_teardowns_circuit(use_caches);
    let table_driver = ::inits_and_teardowns::get_table_driver();
    let setup = GKRSetup::construct(
        &table_driver,
        &[],
        1 << ::inits_and_teardowns::TRACE_LEN_LOG2,
        &circuit,
    );

    CircuitSetup {
        family_idx: u8::MAX,
        geometry: ::inits_and_teardowns::geometry(),
        trace_len: 1 << ::inits_and_teardowns::TRACE_LEN_LOG2,
        compiled_circuit: circuit,
        table_driver,
        setup,
        witness_eval_fn: None,
        prover_configs: circuit_common::prover_configs_for_all_levels(
            ::inits_and_teardowns::prover_config,
        ),
    }
}
