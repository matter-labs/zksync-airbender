//! The full-statement verifier entry points, one module per soundness mode
//! (`pessimistic_conjecture`, `ethproofs_soundcalc`): each wires the mode's
//! generated circuit verifiers (`crate::imports::<mode>`), delegation setup
//! parameters (`crate::delegation_circuits_setups::<mode>`) and verifier
//! tables into the generic statements of `unrolled_proof_statement` /
//! `unified_circuit_statement`.
//!
//! Base layers verify user programs and link the FULL delegation table; the
//! recursion layers verify verifier guests, which only call the blake2s
//! delegation, and link the REDUCED table
//! (`delegation_params::<mode>::reduced_machine_delegation_circuit_verifiers`)
//! so that the other delegation verifiers are dead code for LTO in the
//! recursion guests.

use crate::statement_common::read_setup_cap;
use crate::verifier_imports::*;
use verifier_common::prover::definitions::DEFAULT_CAP_SIZE;

macro_rules! soundness_mode_statements {
    ($mode:ident) => {
        #[cfg(feature = "verifiers")]
        pub fn verify_unrolled_base_layer<
            I: NonDeterminismSource<BabyBearField>,
            E: ErrorCreator,
            const REDUCED_ROUNDS: bool,
        >(
            nd_source: &mut I,
        ) -> Result<[u32; 16], E::Error> {
            use crate::unrolled_circuit_params::NUM_BASE_LAYER_CIRCUITS;
            unsafe {
                let circuits_setups: [MerkleTreeCap<DEFAULT_CAP_SIZE>; NUM_BASE_LAYER_CIRCUITS] =
                    core::array::from_fn(|_| read_setup_cap::<I, DEFAULT_CAP_SIZE>(nd_source));
                let circuits_setups_refs = circuits_setups.each_ref();
                crate::unrolled_proof_statement::verify_full_statement_for_unrolled_circuits::<
                    I,
                    E,
                    true,
                    REDUCED_ROUNDS,
                >(
                    &circuits_setups_refs,
                    &crate::unrolled_circuit_params::$mode::unrolled_circuit_verifiers_for_base_layer::<I, E>(),
                    crate::unrolled_circuit_params::$mode::inits_and_teardowns_verifier::<I, E>(),
                    &crate::delegation_circuits_setups::$mode::DELEGATION_CIRCUITS_SETUP_PARAMS,
                    &crate::delegation_params::$mode::all_delegation_circuit_verifiers::<I, E>(),
                    nd_source,
                )
            }
        }

        #[cfg(feature = "verifiers")]
        pub fn verify_unrolled_recursion_layer<
            I: NonDeterminismSource<BabyBearField>,
            E: ErrorCreator,
            const REDUCED_ROUNDS: bool,
        >(
            nd_source: &mut I,
        ) -> Result<[u32; 16], E::Error> {
            use crate::unrolled_circuit_params::NUM_RECURSION_LAYER_CIRCUITS;
            unsafe {
                let circuits_setups: [MerkleTreeCap<DEFAULT_CAP_SIZE>; NUM_RECURSION_LAYER_CIRCUITS] =
                    core::array::from_fn(|_| read_setup_cap::<I, DEFAULT_CAP_SIZE>(nd_source));
                let circuits_setups_refs = circuits_setups.each_ref();
                crate::unrolled_proof_statement::verify_full_statement_for_unrolled_circuits::<
                    I,
                    E,
                    false,
                    REDUCED_ROUNDS,
                >(
                    &circuits_setups_refs,
                    &crate::unrolled_circuit_params::$mode::unrolled_circuit_verifiers_for_recursion_layer::<I, E>(),
                    crate::unrolled_circuit_params::$mode::inits_and_teardowns_verifier::<I, E>(),
                    &crate::delegation_circuits_setups::$mode::DELEGATION_CIRCUITS_SETUP_PARAMS,
                    &crate::delegation_params::$mode::reduced_machine_delegation_circuit_verifiers::<I, E>(),
                    nd_source,
                )
            }
        }

        #[cfg(feature = "verifiers")]
        pub fn verify_base_or_recursion_unrolled_circuits<
            I: NonDeterminismSource<BabyBearField>,
            E: ErrorCreator,
            const REDUCED_ROUNDS: bool,
        >(
            nd_source: &mut I,
        ) -> Result<[u32; 16], E::Error> {
            use crate::definitions::*;
            // we just branch
            let op_type = nd_source.read_word();
            match op_type {
                OP_VERIFY_BASE_LAYER_IN_UNROLLED_CIRCUITS => {
                    verify_unrolled_base_layer::<I, E, REDUCED_ROUNDS>(nd_source)
                }
                OP_VERIFY_RECURSIVE_LAYER_IN_UNROLLED_CIRCUITS => {
                    verify_unrolled_recursion_layer::<I, E, REDUCED_ROUNDS>(nd_source)
                }
                _ => {
                    panic!("Unknown op");
                }
            }
        }

        pub fn verify_unified_circuit_base_layer<
            I: NonDeterminismSource<BabyBearField>,
            E: ErrorCreator,
            const REDUCED_ROUNDS: bool,
        >(
            nd_source: &mut I,
        ) -> Result<[u32; 16], E::Error> {
            unsafe {
                let unified_setup = read_setup_cap::<I, DEFAULT_CAP_SIZE>(nd_source);
                crate::unified_circuit_statement::verify_full_statement_for_unified_circuit::<
                    I,
                    E,
                    true,
                    REDUCED_ROUNDS,
                    _,
                    _,
                >(
                    &unified_setup,
                    crate::imports::$mode::unified_reduced_machine::verify::<I, E>,
                    &crate::delegation_circuits_setups::$mode::DELEGATION_CIRCUITS_SETUP_PARAMS,
                    &crate::delegation_params::$mode::all_delegation_circuit_verifiers::<I, E>(),
                    nd_source,
                )
            }
        }

        pub fn verify_unified_circuit_recursion_layer<
            I: NonDeterminismSource<BabyBearField>,
            E: ErrorCreator,
            const REDUCED_ROUNDS: bool,
        >(
            nd_source: &mut I,
        ) -> Result<[u32; 16], E::Error> {
            unsafe {
                let unified_setup = read_setup_cap::<I, DEFAULT_CAP_SIZE>(nd_source);
                crate::unified_circuit_statement::verify_full_statement_for_unified_circuit::<
                    I,
                    E,
                    false,
                    REDUCED_ROUNDS,
                    _,
                    _,
                >(
                    &unified_setup,
                    crate::imports::$mode::unified_reduced_machine::verify::<I, E>,
                    &crate::delegation_circuits_setups::$mode::DELEGATION_CIRCUITS_SETUP_PARAMS,
                    &crate::delegation_params::$mode::reduced_machine_delegation_circuit_verifiers::<I, E>(),
                    nd_source,
                )
            }
        }

        pub fn verify_unrolled_or_unified_circuit_recursion_layer<
            I: NonDeterminismSource<BabyBearField>,
            E: ErrorCreator,
            const REDUCED_ROUNDS: bool,
        >(
            nd_source: &mut I,
        ) -> Result<[u32; 16], E::Error> {
            use crate::definitions::*;
            // we just branch
            let op_type = nd_source.read_word();
            match op_type {
                OP_VERIFY_UNROLLED_RECURSION_LAYER_IN_UNIFIED_CIRCUIT => {
                    #[cfg(feature = "verifiers")]
                    {
                        verify_unrolled_recursion_layer::<I, E, REDUCED_ROUNDS>(nd_source)
                    }
                    #[cfg(not(feature = "verifiers"))]
                    {
                        let _ = nd_source;
                        panic!("Unrolled recursion layer verification is not available. Enable `verifiers` feature.");
                    }
                }
                OP_VERIFY_UNIFIED_RECURSION_LAYER_IN_UNIFIED_CIRCUIT => {
                    verify_unified_circuit_recursion_layer::<I, E, REDUCED_ROUNDS>(nd_source)
                }
                _ => {
                    panic!("Unknown op");
                }
            }
        }
    };
}

/// The in-house capacity-conjecture accounting: the production verifiers.
pub mod pessimistic_conjecture {
    use super::*;

    soundness_mode_statements!(pessimistic_conjecture);

    /// [`verify_unified_circuit_recursion_layer`] against the high-LDE
    /// "L1 feeder" unified verifier (base LDE 16, round-0 queries 22 — see
    /// `prover::gkr::prover_config::example_configs::l1_feeder_config_for_2_23`).
    /// Verifies proofs of the FINAL BabyBear recursion layer(s), whose cheap
    /// verification is what the L1 (Proth120) 2^22 wrapper circuit executes.
    /// Same circuit, same delegation table, same 100-bit target — only the
    /// commitment parameters embedded in the generated verify function differ.
    /// A pessimistic-conjecture variant: no soundcalc twin has been designed.
    pub fn verify_unified_circuit_recursion_layer_l1_feeder<
        I: NonDeterminismSource<BabyBearField>,
        E: ErrorCreator,
        const REDUCED_ROUNDS: bool,
    >(
        nd_source: &mut I,
    ) -> Result<[u32; 16], E::Error> {
        unsafe {
            let unified_setup = read_setup_cap::<I, DEFAULT_CAP_SIZE>(nd_source);
            crate::unified_circuit_statement::verify_full_statement_for_unified_circuit::<
                I,
                E,
                false,
                REDUCED_ROUNDS,
                _,
                _,
            >(
                &unified_setup,
                crate::imports::pessimistic_conjecture::unified_reduced_machine_l1_feeder::verify::<I, E>,
                &crate::delegation_circuits_setups::pessimistic_conjecture::DELEGATION_CIRCUITS_SETUP_PARAMS,
                &crate::delegation_params::pessimistic_conjecture::reduced_machine_delegation_circuit_verifiers::<I, E>(),
                nd_source,
            )
        }
    }
}

/// The `ethereum/soundcalc`-certified accounting (see
/// `prover::gkr::prover_config::example_configs::ethproofs_soundcalc`).
pub mod ethproofs_soundcalc {
    use super::*;

    soundness_mode_statements!(ethproofs_soundcalc);
}
