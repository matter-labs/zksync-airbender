use super::*;

pub fn get_keccak_special5_circuit_setup(
    use_caches: bool,
    worker: &Worker,
) -> DelegationCircuitSetup {
    type C = ::keccak_special5::KeccakSpecial5DelegationCircuit;

    make_setup_for_delegation_circuit::<C>(use_caches)
}
