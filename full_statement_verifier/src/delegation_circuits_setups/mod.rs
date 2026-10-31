//! The delegation circuits' setup parameters (delegation type, permutation
//! terms, setup cap), one set per soundness mode: the caps are committed with
//! the config of the mode (`circuit_defs/setups` generates them with
//! `dump_delegation_setups_for_verifier`).

pub mod ethproofs_soundcalc;
pub mod pessimistic_conjecture;

pub const NUM_DELEGATION_CIRCUIT_TYPES: usize =
    pessimistic_conjecture::DELEGATION_CIRCUITS_SETUP_PARAMS.len();

const _: () = assert!(
    ethproofs_soundcalc::DELEGATION_CIRCUITS_SETUP_PARAMS.len() == NUM_DELEGATION_CIRCUIT_TYPES,
    "every soundness mode covers the same delegation circuits"
);
