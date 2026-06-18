use super::*;

pub fn get_bigint_with_control_circuit_setup(
    use_caches: bool,
    worker: &Worker,
) -> DelegationCircuitSetup {
    type C = ::bigint_with_control::BigIntDelegationCircuit;

    make_setup_for_delegation_circuit::<C>(use_caches)
}
