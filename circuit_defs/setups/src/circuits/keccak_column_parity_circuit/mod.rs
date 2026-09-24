use super::*;

pub fn get_keccak_column_parity_circuit_setup(
    use_caches: bool,
    _worker: &Worker,
) -> DelegationCircuitSetup {
    make_setup_for_delegation_circuit::<::keccak_column_parity::KeccakColumnParityDelegationCircuit>(
        use_caches,
    )
}
