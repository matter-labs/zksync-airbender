#![cfg_attr(not(any(test, feature = "replace_csr")), no_std)]
#![cfg_attr(any(test, feature = "proof_utils"), feature(allocator_api))]
#![feature(ptr_as_ref_unchecked)]
#![feature(slice_from_ptr_range)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

#[cfg(any(all(feature = "security_80", feature = "security_100"),))]
compile_error!("multiple security levels selected same time");

pub const MERSENNE31QUARTIC_SIZE_LOG2: usize = 124;
pub const POW_BITS_FOR_80_SECURITY_BITS: usize = 28;
pub const POW_BITS_FOR_100_SECURITY_BITS: usize = 28;

#[cfg(feature = "security_80")]
pub const SECURITY_BITS: usize = 80;
#[cfg(all(feature = "security_80", not(feature = "worst_case_config_generation")))]
pub const MEMORY_DELEGATION_POW_BITS: usize =
    POW_BITS_FOR_MEMORY_AND_DELEGATION_FOR_80_SECURITY_BITS;

#[cfg(feature = "security_100")]
pub const SECURITY_BITS: usize = 100;
#[cfg(all(
    feature = "security_100",
    not(feature = "worst_case_config_generation")
))]
pub const MEMORY_DELEGATION_POW_BITS: usize =
    POW_BITS_FOR_MEMORY_AND_DELEGATION_FOR_100_SECURITY_BITS;

#[cfg(feature = "worst_case_config_generation")]
pub const MEMORY_DELEGATION_POW_BITS: usize = 0;

#[derive(Clone, Copy, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct SizedProofSecurityConfig<const NUM_FOLDINGS: usize> {
    pub lookup_pow_bits: u32,
    pub quotient_alpha_pow_bits: u32,
    pub quotient_z_pow_bits: u32,
    pub deep_poly_alpha_pow_bits: u32,
    #[serde(bound(deserialize = "[u32; NUM_FOLDINGS]: serde::Deserialize<'de>"))]
    #[serde(bound(serialize = "[u32; NUM_FOLDINGS]: serde::Serialize"))]
    pub foldings_pow_bits: [u32; NUM_FOLDINGS],
    pub fri_queries_pow_bits: u32,
    pub num_queries: usize,
}

#[cfg(any(test, feature = "proof_utils"))]
impl<const NUM_FOLDINGS: usize> SizedProofSecurityConfig<NUM_FOLDINGS> {
    pub fn for_prover(&self) -> prover::prover_stages::ProofSecurityConfig {
        prover::prover_stages::ProofSecurityConfig {
            lookup_pow_bits: self.lookup_pow_bits,
            quotient_alpha_pow_bits: self.quotient_alpha_pow_bits,
            quotient_z_pow_bits: self.quotient_z_pow_bits,
            deep_poly_alpha_pow_bits: self.deep_poly_alpha_pow_bits,
            foldings_pow_bits: self.foldings_pow_bits.to_vec(),
            fri_queries_pow_bits: self.fri_queries_pow_bits,
            num_queries: self.num_queries,
        }
    }
}

// The file should be generated with tools/pow_config_generator
#[cfg(not(feature = "worst_case_config_generation"))]
include!("pow_config_worst_constants.rs");

#[cfg(feature = "worst_case_config_generation")]
impl<const NUM_FOLDINGS: usize> SizedProofSecurityConfig<NUM_FOLDINGS> {
    pub const fn worst_case_config() -> Self {
        SizedProofSecurityConfig {
            lookup_pow_bits: 0,
            quotient_alpha_pow_bits: 0,
            quotient_z_pow_bits: 0,
            deep_poly_alpha_pow_bits: 0,
            foldings_pow_bits: [0; NUM_FOLDINGS],
            fri_queries_pow_bits: 0,
            num_queries: 50,
        }
    }
}

pub const fn transcript_challenge_array_size(num_elements: usize, pow_bits: usize) -> usize {
    if pow_bits > 0 {
        (num_elements + 1).next_multiple_of(blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS)
    } else {
        num_elements.next_multiple_of(blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS)
    }
}

#[derive(Clone, Copy, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct SizedProofPowChallenges<const NUM_FOLDINGS: usize> {
    pub lookup_pow_challenge: u64,
    pub quotient_alpha_pow_challenge: u64,
    pub quotient_z_pow_challenge: u64,
    pub deep_poly_alpha_pow_challenge: u64,
    #[serde(bound(deserialize = "[u64; NUM_FOLDINGS]: serde::Deserialize<'de>"))]
    #[serde(bound(serialize = "[u64; NUM_FOLDINGS]: serde::Serialize"))]
    pub foldings_pow_challenges: [u64; NUM_FOLDINGS],
    pub fri_queries_pow_challenge: u64,
}

use core::mem::MaybeUninit;

extern crate alloc;

use field::{Mersenne31Field, Mersenne31Quartic};
use prover::definitions::*;

pub use blake2s_u32;
pub use cs;
pub use field;
pub use non_determinism_source;
pub use prover;
pub use transcript;
pub mod fri_folding;
#[cfg(any(test, feature = "proof_utils"))]
pub mod proof_flattener;

pub mod structs;

#[cfg(not(target_arch = "riscv32"))]
pub type DefaultNonDeterminismSource = prover::nd_source_std::ThreadLocalBasedSource;

#[cfg(target_arch = "riscv32")]
pub type DefaultNonDeterminismSource = non_determinism_source::CSRBasedSource;

#[cfg(not(all(target_arch = "riscv32", feature = "blake2_with_compression")))]
pub type DefaultLeafInclusionVerifier = prover::definitions::Blake2sForEverythingVerifier;

// pub type DefaultLeafInclusionVerifier =
//     prover::definitions::Blake2sForLeafsPoseidon2ForNodesVerifier;

#[cfg(all(target_arch = "riscv32", feature = "blake2_with_compression"))]
pub type DefaultLeafInclusionVerifier =
    prover::definitions::Blake2sForEverythingVerifierWithAlternativeCompression;

pub type VerifierFunctionPointer<
    const CAP_SIZE: usize,
    const NUM_COSETS: usize,
    const NUM_DELEGATION_CHALLENGES: usize,
    const NUM_AUX_BOUNDARY_VALUES: usize,
    const NUM_STATE_ELEMENTS: usize,
    const NUM_MACHINE_STATE_CHALLENGES: usize = 0,
> = unsafe fn(
    &mut ProofOutput<
        CAP_SIZE,
        NUM_COSETS,
        NUM_DELEGATION_CHALLENGES,
        NUM_AUX_BOUNDARY_VALUES,
        NUM_MACHINE_STATE_CHALLENGES,
    >,
    &mut ProofPublicInputs<NUM_STATE_ELEMENTS>,
);

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize, Hash)]
pub struct ProofOutput<
    const CAP_SIZE: usize,
    const NUM_COSETS: usize,
    const NUM_DELEGATION_CHALLENGES: usize,
    const NUM_AUX_BOUNDARY_VALUES: usize,
    const NUM_MACHINE_STATE_CHALLENGES: usize = 0,
> {
    #[serde(bound(
        deserialize = "MerkleTreeCap<CAP_SIZE>: serde::Deserialize<'de>, [MerkleTreeCap<CAP_SIZE>; NUM_COSETS]: serde::Deserialize<'de>"
    ))]
    #[serde(bound(
        serialize = "MerkleTreeCap<CAP_SIZE>: serde::Serialize, [MerkleTreeCap<CAP_SIZE>; NUM_COSETS]: serde::Serialize"
    ))]
    pub setup_caps: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    pub memory_caps: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    pub memory_challenges: ExternalMemoryArgumentChallenges,
    #[serde(bound(
        deserialize = "[ExternalDelegationArgumentChallenges; NUM_DELEGATION_CHALLENGES]: serde::Deserialize<'de>"
    ))]
    #[serde(bound(
        serialize = "[ExternalDelegationArgumentChallenges; NUM_DELEGATION_CHALLENGES]: serde::Serialize"
    ))]
    pub delegation_challenges: [ExternalDelegationArgumentChallenges; NUM_DELEGATION_CHALLENGES],
    #[serde(bound(
        deserialize = "[ExternalMachineStateArgumentChallenges; NUM_MACHINE_STATE_CHALLENGES]: serde::Deserialize<'de>"
    ))]
    #[serde(bound(
        serialize = "[ExternalMachineStateArgumentChallenges; NUM_MACHINE_STATE_CHALLENGES]: serde::Serialize"
    ))]
    pub machine_state_permutation_challenges:
        [ExternalMachineStateArgumentChallenges; NUM_MACHINE_STATE_CHALLENGES],
    #[serde(bound(
        deserialize = "[AuxArgumentsBoundaryValues; NUM_AUX_BOUNDARY_VALUES]: serde::Deserialize<'de>"
    ))]
    #[serde(bound(
        serialize = "[AuxArgumentsBoundaryValues; NUM_AUX_BOUNDARY_VALUES]: serde::Serialize"
    ))]
    pub lazy_init_boundary_values: [AuxArgumentsBoundaryValues; NUM_AUX_BOUNDARY_VALUES],
    pub grand_product_accumulator: Mersenne31Quartic,
    #[serde(bound(
        deserialize = "[Mersenne31Quartic; NUM_DELEGATION_CHALLENGES]: serde::Deserialize<'de>"
    ))]
    #[serde(bound(
        serialize = "[Mersenne31Quartic; NUM_DELEGATION_CHALLENGES]: serde::Serialize"
    ))]
    pub delegation_argument_accumulator: [Mersenne31Quartic; NUM_DELEGATION_CHALLENGES],
    pub circuit_sequence: u32,
    pub delegation_type: u32,
}

impl<
        const CAP_SIZE: usize,
        const NUM_COSETS: usize,
        const NUM_DELEGATION_CHALLENGES: usize,
        const NUM_AUX_BOUNDARY_VALUES: usize,
        const NUM_MACHINE_STATE_CHALLENGES: usize,
    >
    ProofOutput<
        CAP_SIZE,
        NUM_COSETS,
        NUM_DELEGATION_CHALLENGES,
        NUM_AUX_BOUNDARY_VALUES,
        NUM_MACHINE_STATE_CHALLENGES,
    >
{
    pub fn setup_caps_flattened(&'_ self) -> &'_ [u32] {
        unsafe {
            core::slice::from_ptr_range(
                self.setup_caps.as_ptr_range().start.cast::<u32>()
                    ..self.setup_caps.as_ptr_range().end.cast::<u32>(),
            )
        }
    }

    pub fn memory_caps_flattened(&'_ self) -> &'_ [u32] {
        unsafe {
            core::slice::from_ptr_range(
                self.memory_caps.as_ptr_range().start.cast::<u32>()
                    ..self.memory_caps.as_ptr_range().end.cast::<u32>(),
            )
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize, Hash)]
pub struct ProofPublicInputs<const NUM_STATE_ELEMENTS: usize> {
    #[serde(bound(
        deserialize = "[Mersenne31Field; NUM_STATE_ELEMENTS]: serde::Deserialize<'de>"
    ))]
    #[serde(bound(serialize = "[Mersenne31Field; NUM_STATE_ELEMENTS]: serde::Serialize"))]
    pub input_state_variables: [Mersenne31Field; NUM_STATE_ELEMENTS],
    #[serde(bound(
        deserialize = "[Mersenne31Field; NUM_STATE_ELEMENTS]: serde::Deserialize<'de>"
    ))]
    #[serde(bound(serialize = "[Mersenne31Field; NUM_STATE_ELEMENTS]: serde::Serialize"))]
    pub output_state_variables: [Mersenne31Field; NUM_STATE_ELEMENTS],
}

impl<const NUM_STATE_ELEMENTS: usize> ProofPublicInputs<NUM_STATE_ELEMENTS> {
    pub fn uninit() -> Self {
        unsafe {
            Self {
                input_state_variables: MaybeUninit::uninit().assume_init(),
                output_state_variables: MaybeUninit::uninit().assume_init(),
            }
        }
    }
}

pub fn parse_field_els_as_u32_from_u16_limbs_checked(input: [Mersenne31Field; 2]) -> u32 {
    let [low, high] = input;
    let low = low.to_reduced_u32();
    let high = high.to_reduced_u32();
    assert!(low & core::hint::black_box(0xffff0000u32) == 0);
    assert!(high & core::hint::black_box(0xffff0000u32) == 0);

    low | (high << 16)
}
