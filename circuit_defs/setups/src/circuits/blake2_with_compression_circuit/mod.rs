use super::*;

pub fn get_blake2_with_compression_circuit_setup(
    use_caches: bool,
    worker: &Worker,
) -> DelegationCircuitSetup {
    type C = ::blake2_with_compression::Blake2sWithCompressionDelegationCircuit;

    make_setup_for_delegation_circuit::<C>(use_caches)
}
