use super::*;

pub fn get_blake2_g_function_circuit_setup(
    use_caches: bool,
    worker: &Worker,
) -> DelegationCircuitSetup {
    type C = ::blake2_g_function::Blake2sGFunctionDelegationCircuit;

    make_setup_for_delegation_circuit::<C>(use_caches)
}
