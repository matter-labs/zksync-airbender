#![cfg_attr(not(any(test, feature = "replace_csr")), no_std)]
#![feature(slice_from_ptr_range)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use core::mem::MaybeUninit;

pub use verifier_common;

mod constants;
pub mod definitions;

#[cfg(feature = "verifiers")]
pub mod imports;
#[cfg(feature = "verifiers")]
pub mod legacy_circuits;
#[cfg(feature = "verifiers")]
pub mod unified_circuit_statement;
#[cfg(feature = "verifiers")]
pub mod unrolled_proof_statement;

use self::constants::*;

use verifier_common::blake2s_u32::{BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use verifier_common::cs::definitions::{
    NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP, NUM_TIMESTAMP_COLUMNS_FOR_RAM, TIMESTAMP_COLUMNS_NUM_BITS,
};
use verifier_common::field::{Field, Mersenne31Field, Mersenne31Quartic, PrimeField};
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::prover::definitions::ExternalChallenges;
use verifier_common::prover::definitions::MerkleTreeCap;
use verifier_common::transcript::Blake2sBufferingTranscript;
use verifier_common::VerifierFunctionPointer;
use verifier_common::{parse_field_els_as_u32_from_u16_limbs_checked, ProofPublicInputs};
use verifier_common::{prover, ProofOutput};

pub const MAX_CYCLES: u64 = const {
    let max_unique_timestamps =
        1u64 << (TIMESTAMP_COLUMNS_NUM_BITS as usize * NUM_TIMESTAMP_COLUMNS_FOR_RAM);
    let max_cycles = max_unique_timestamps >> NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP;

    max_cycles
};

pub const MAX_BASE_LAYER_CIRCUITS: usize = const {
    let max_circuits =
        MAX_CYCLES / ((risc_v_cycles_verifier::concrete::size_constants::TRACE_LEN as u64) - 1);

    max_circuits as usize
};

pub const MAX_RECURSION_LAYER_CIRCUITS: usize = MAX_BASE_LAYER_CIRCUITS;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InitAndTeardownTuple {
    pub address: u32,
    pub teardown_value: u32,
    pub teardown_ts_pair: (u32, u32),
}

impl InitAndTeardownTuple {
    #[inline(always)]
    pub fn from_aux_values_first_row(
        value: &prover::definitions::AuxArgumentsBoundaryValues,
    ) -> Self {
        Self {
            address: parse_field_els_as_u32_from_u16_limbs_checked(value.lazy_init_first_row),
            teardown_value: parse_field_els_as_u32_from_u16_limbs_checked(
                value.teardown_value_first_row,
            ),
            teardown_ts_pair: (
                value.teardown_timestamp_first_row[0].to_reduced_u32(),
                value.teardown_timestamp_first_row[1].to_reduced_u32(),
            ),
        }
    }

    #[inline(always)]
    pub fn from_aux_values_one_before_last_row(
        value: &prover::definitions::AuxArgumentsBoundaryValues,
    ) -> Self {
        Self {
            address: parse_field_els_as_u32_from_u16_limbs_checked(
                value.lazy_init_one_before_last_row,
            ),
            teardown_value: parse_field_els_as_u32_from_u16_limbs_checked(
                value.teardown_value_one_before_last_row,
            ),
            teardown_ts_pair: (
                value.teardown_timestamp_one_before_last_row[0].to_reduced_u32(),
                value.teardown_timestamp_one_before_last_row[1].to_reduced_u32(),
            ),
        }
    }
}
