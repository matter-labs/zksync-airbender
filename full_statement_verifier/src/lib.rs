#![cfg_attr(not(any(test, any(feature = "replace_csr", feature = "proof_utils"))), no_std)]
#![cfg_attr(any(test, any(feature = "replace_csr", feature = "proof_utils")), allow(incomplete_features))]
#![cfg_attr(any(test, any(feature = "replace_csr", feature = "proof_utils")), feature(generic_const_exprs))]

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

#[cfg(feature = "proof_utils")]
pub mod program_proof;

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
mod verifier_imports {
    pub(super) use core::mem::MaybeUninit;
    pub(super) use verifier_common::blake2s_u32::{
        BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS,
    };
    pub(super) use verifier_common::errors::ErrorCreator;
    pub(super) use verifier_common::field::baby_bear::base::BabyBearField;
    pub(super) use verifier_common::field::baby_bear::ext4::BabyBearExt4;
    pub(super) use verifier_common::field::Field;
    pub(super) use verifier_common::non_determinism_source::NonDeterminismSource;
    pub(super) use verifier_common::prover::definitions::{GKRExternalChallenges, MerkleTreeCap};
    pub(super) use verifier_common::transcript::Blake2sBufferingTranscript;
    pub(super) use verifier_common::DelegationCircuitSetupData;
}

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
use self::verifier_imports::*;

use verifier_common::cs::definitions::{
    NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP, NUM_TIMESTAMP_COLUMNS_FOR_RAM, TIMESTAMP_COLUMNS_NUM_BITS,
};
use verifier_common::prover;

pub const MAX_CYCLES: u64 = const {
    let max_unique_timestamps =
        1u64 << (TIMESTAMP_COLUMNS_NUM_BITS as usize * NUM_TIMESTAMP_COLUMNS_FOR_RAM);
    let max_cycles = max_unique_timestamps >> NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP;

    max_cycles
};

pub const MEMORY_DELEGATION_POW_BITS: usize = 0; // TODO
