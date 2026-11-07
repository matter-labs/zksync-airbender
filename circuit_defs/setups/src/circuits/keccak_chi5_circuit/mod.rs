use super::*;

pub fn get_keccak_chi5_circuit_setup(use_caches: bool, worker: &Worker) -> DelegationCircuitSetup {
    make_setup_for_delegation_circuit::<::keccak_chi5::KeccakChi5DelegationCircuit>(
        use_caches, worker,
    )
}
