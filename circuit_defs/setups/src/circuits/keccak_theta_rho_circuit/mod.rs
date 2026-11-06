use super::*;

pub fn get_keccak_theta_rho_circuit_setup(
    use_caches: bool,
    _worker: &Worker,
) -> DelegationCircuitSetup {
    make_setup_for_delegation_circuit::<::keccak_theta_rho::KeccakThetaRhoDelegationCircuit>(
        use_caches,
    )
}
