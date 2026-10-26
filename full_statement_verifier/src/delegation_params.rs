//! The delegation-circuit verifier tables, one module per soundness mode:
//! the FULL table (every delegation a user program can call) and the REDUCED
//! table for the recursion layers, whose programs (the verifier guests) only
//! ever call the blake2s delegation — the other entries are a stub, so that
//! LTO drops the unused delegation verifiers from the recursion guests.

use crate::prover::definitions::GKRExternalChallenges;
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::non_determinism_source::NonDeterminismSource;

pub use crate::delegation_circuits_setups::NUM_DELEGATION_CIRCUIT_TYPES;

pub type DelegationVerifierFn<I, E> = fn(
    &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    &mut I,
) -> Result<crate::imports::DelegationCircuitOutput, <E as ErrorCreator>::Error>;

/// The entry of the recursion-layer table for a delegation the recursion
/// guests never call: a proof claiming such a delegation is rejected.
fn unsupported_in_recursion_layers<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
    _external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    _nd_source: &mut I,
) -> Result<crate::imports::DelegationCircuitOutput, E::Error> {
    panic!("delegation circuit is not part of the recursion layers")
}

macro_rules! delegation_verifier_tables {
    ($mode:ident) => {
        pub mod $mode {
            use super::*;

            /// Every delegation circuit's verifier, indexed like
            /// [`crate::definitions::DELEGATION_TYPES`].
            pub fn all_delegation_circuit_verifiers<
                I: NonDeterminismSource<BabyBearField>,
                E: ErrorCreator,
            >() -> [DelegationVerifierFn<I, E>; NUM_DELEGATION_CIRCUIT_TYPES] {
                crate::definitions::DELEGATION_TYPES.map(|csr| match csr {
                    common_constants::BLAKE2S_DELEGATION_CSR_REGISTER => {
                        crate::imports::$mode::blake2_with_extended_control::verify::<I, E> as _
                    }
                    common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER => {
                        crate::imports::$mode::bigint_with_extended_control::verify::<I, E> as _
                    }
                    common_constants::KECCAK_SPECIAL5_CSR_REGISTER => {
                        crate::imports::$mode::keccak_special5::verify::<I, E> as _
                    }
                    common_constants::KECCAK_THETA_RHO_CSR_REGISTER => {
                        crate::imports::$mode::keccak_theta_rho::verify::<I, E> as _
                    }
                    common_constants::KECCAK_COLUMN_PARITY_CSR_REGISTER => {
                        crate::imports::$mode::keccak_column_parity::verify::<I, E> as _
                    }
                    common_constants::KECCAK_CHI5_CSR_REGISTER => {
                        crate::imports::$mode::keccak_chi5::verify::<I, E> as _
                    }
                    _ => unreachable!("unsupported delegation CSR {csr}"),
                })
            }

            /// The recursion-layer table: only the blake2s delegation (the one
            /// the verifier guests call) is verifiable, every other entry
            /// rejects — used by the recursion-layer statements only, so the
            /// recursion guests do not link the other delegation verifiers.
            pub fn reduced_machine_delegation_circuit_verifiers<
                I: NonDeterminismSource<BabyBearField>,
                E: ErrorCreator,
            >() -> [DelegationVerifierFn<I, E>; NUM_DELEGATION_CIRCUIT_TYPES] {
                crate::definitions::DELEGATION_TYPES.map(|csr| match csr {
                    common_constants::BLAKE2S_DELEGATION_CSR_REGISTER => {
                        crate::imports::$mode::blake2_with_extended_control::verify::<I, E> as _
                    }
                    common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER
                    | common_constants::KECCAK_SPECIAL5_CSR_REGISTER
                    | common_constants::KECCAK_THETA_RHO_CSR_REGISTER
                    | common_constants::KECCAK_COLUMN_PARITY_CSR_REGISTER
                    | common_constants::KECCAK_CHI5_CSR_REGISTER => {
                        unsupported_in_recursion_layers::<I, E> as _
                    }
                    _ => unreachable!("unsupported delegation CSR {csr}"),
                })
            }
        }
    };
}

delegation_verifier_tables!(pessimistic_conjecture);
delegation_verifier_tables!(ethproofs_soundcalc);
