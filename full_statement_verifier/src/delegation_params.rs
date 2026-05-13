use crate::prover::gkr::prover::GKRExternalChallenges;
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::non_determinism_source::NonDeterminismSource;

use crate::constants::*;
use crate::MerkleTreeCap;

pub const NUM_DELEGATION_CIRCUIT_TYPES: usize =
    crate::constants::DELEGATION_CIRCUITS_SETUP_PARAMS.len();

// NOTE: order here must match the setups
pub fn all_delegation_circuit_verifiers<I: NonDeterminismSource, E: ErrorCreator>() -> [
    fn(&GKRExternalChallenges<BabyBearField, BabyBearExt4>) -> Result<crate::imports::DelegationCircuitOutput, E::Error>;
    NUM_DELEGATION_CIRCUIT_TYPES
]{
    [
        crate::imports::blake2_with_extended_control_sec_80::verify::<I, E>,
        crate::imports::bigint_with_extended_control_sec_80::verify::<I, E>,
        crate::imports::keccak_special5_sec_80::verify::<I, E>,
        crate::imports::blake2_g_function_sec_80::verify::<I, E>,
    ]
}
