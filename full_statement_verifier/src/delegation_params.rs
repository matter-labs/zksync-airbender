use crate::prover::definitions::GKRExternalChallenges;
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::non_determinism_source::NonDeterminismSource;

pub const NUM_DELEGATION_CIRCUIT_TYPES: usize =
    crate::constants::DELEGATION_CIRCUITS_SETUP_PARAMS.len();

pub fn all_delegation_circuit_verifiers_sec_100<
    I: NonDeterminismSource<BabyBearField>,
    E: ErrorCreator,
>() -> [fn(
    &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    &mut I,
) -> Result<crate::imports::DelegationCircuitOutput, E::Error>; NUM_DELEGATION_CIRCUIT_TYPES] {
    crate::definitions::DELEGATION_TYPES.map(|csr| match csr {
        common_constants::BLAKE2S_DELEGATION_CSR_REGISTER => {
            crate::imports::blake2_with_extended_control_sec_100::verify::<I, E> as _
        }
        common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER => {
            crate::imports::bigint_with_extended_control_sec_100::verify::<I, E> as _
        }
        common_constants::KECCAK_SPECIAL5_CSR_REGISTER => {
            crate::imports::keccak_special5_sec_100::verify::<I, E> as _
        }
        common_constants::KECCAK_THETA_RHO_CSR_REGISTER => {
            crate::imports::keccak_theta_rho_sec_100::verify::<I, E> as _
        }
        common_constants::KECCAK_COLUMN_PARITY_CSR_REGISTER => {
            crate::imports::keccak_column_parity_sec_100::verify::<I, E> as _
        }
        common_constants::KECCAK_CHI5_CSR_REGISTER => {
            crate::imports::keccak_chi5_sec_100::verify::<I, E> as _
        }
        _ => unreachable!("unsupported delegation CSR {csr}"),
    })
}
