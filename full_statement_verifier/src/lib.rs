#![allow(warnings)]
#![cfg_attr(not(any(test, feature = "replace_csr")), no_std)]

pub use verifier_common;

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
mod constants;
pub mod definitions;

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
pub mod delegation_params;
#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
pub mod imports;
// #[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
// pub mod unified_circuit_statement;
#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
pub mod unrolled_circuit_params;
#[cfg(feature = "verifiers")]
pub mod unrolled_proof_statement;

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
pub mod statement_common;

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
mod verifier_imports {
    pub(super) use super::constants::*;
    pub(super) use core::mem::MaybeUninit;
    pub(super) use verifier_common::blake2s_u32::{
        BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS,
    };
    pub(super) use verifier_common::field::{
        Field, Mersenne31Field, Mersenne31Quartic, PrimeField,
    };
    pub(super) use verifier_common::non_determinism_source::NonDeterminismSource;
    pub(super) use verifier_common::prover::definitions::{GKRExternalChallenges, MerkleTreeCap};
    pub(super) use verifier_common::transcript::Blake2sBufferingTranscript;
}

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
use self::verifier_imports::*;

use verifier_common::cs::definitions::{
    NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP, NUM_TIMESTAMP_COLUMNS_FOR_RAM, TIMESTAMP_COLUMNS_NUM_BITS,
};
use verifier_common::parse_field_els_as_u32_from_u16_limbs_checked;
use verifier_common::prover;

pub const MAX_CYCLES: u64 = const {
    let max_unique_timestamps =
        1u64 << (TIMESTAMP_COLUMNS_NUM_BITS as usize * NUM_TIMESTAMP_COLUMNS_FOR_RAM);
    let max_cycles = max_unique_timestamps >> NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP;

    max_cycles
};

pub const MEMORY_DELEGATION_POW_BITS: usize = 0; // TODO
