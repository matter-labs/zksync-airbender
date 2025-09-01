#![cfg_attr(not(any(test, feature = "replace_csr")), no_std)]
#![cfg_attr(any(test, feature = "proof_utils"), feature(allocator_api))]
#![feature(ptr_as_ref_unchecked)]
#![feature(slice_from_ptr_range)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

#[cfg(any(
    all(feature = "security_80", feature = "security_100"),
    all(feature = "security_80", feature = "security_128"),
    all(feature = "security_100", feature = "security_128")
))]
compiler_error!("multiple security levels selected same time");

#[cfg(feature = "security_80")]
pub const SECURITY_BITS: usize = 80;

#[cfg(feature = "security_100")]
pub const SECURITY_BITS: usize = 100;

#[cfg(feature = "security_128")]
pub const SECURITY_BITS: usize = 128;

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
> = unsafe fn(
    &mut ProofOutput<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, NUM_AUX_BOUNDARY_VALUES>,
    &mut ProofPublicInputs<NUM_STATE_ELEMENTS>,
);

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize, Hash)]
pub struct ProofOutput<
    const CAP_SIZE: usize,
    const NUM_COSETS: usize,
    const NUM_DELEGATION_CHALLENGES: usize,
    const NUM_AUX_BOUNDARY_VALUES: usize,
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
    > ProofOutput<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, NUM_AUX_BOUNDARY_VALUES>
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

pub fn parse_field_els_as_u32_checked(input: [Mersenne31Field; 2]) -> u32 {
    let [low, high] = input;
    let low = low.to_reduced_u32();
    let high = high.to_reduced_u32();
    assert!(low & core::hint::black_box(0xffff0000u32) == 0);
    assert!(high & core::hint::black_box(0xffff0000u32) == 0);

    low | (high << 16)
}
