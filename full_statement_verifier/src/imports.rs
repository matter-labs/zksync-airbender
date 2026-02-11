use crate::constants::*;
use crate::MerkleTreeCap;
use crate::VerifierFunctionPointer;

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
pub const BLAKE_WITH_COMPRESSION_VERIFIER_PTR: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    0,
    0,
> = blake2_with_compression_verifier::verify;

#[cfg(feature = "verifiers")]
pub const BIGINT_WITH_CONTROL_VERIFIER_PTR: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    0,
    0,
> = bigint_with_control_verifier::verify;

#[cfg(feature = "verifiers")]
pub const KECCAK_SPECIAL5_CONTROL_VERIFIER_PTR: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    0,
    0,
> = keccak_special5_verifier::verify;

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
use crate::constants::ALL_DELEGATION_CIRCUITS_PARAMS;

#[cfg(feature = "verifiers")]
pub const BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS: &[(
    u32, // delegation type
    u32, // delegation capacity
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] = &[
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[0].0,
        ALL_DELEGATION_CIRCUITS_PARAMS[0].1,
        &ALL_DELEGATION_CIRCUITS_PARAMS[0].2,
        BLAKE_WITH_COMPRESSION_VERIFIER_PTR,
    ),
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[1].0,
        ALL_DELEGATION_CIRCUITS_PARAMS[1].1,
        &ALL_DELEGATION_CIRCUITS_PARAMS[1].2,
        BIGINT_WITH_CONTROL_VERIFIER_PTR,
    ),
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[2].0,
        ALL_DELEGATION_CIRCUITS_PARAMS[2].1,
        &ALL_DELEGATION_CIRCUITS_PARAMS[2].2,
        KECCAK_SPECIAL5_CONTROL_VERIFIER_PTR,
    ),
];

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
pub const RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS: &[(
    u32,
    u32,
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] = &[(
    ALL_DELEGATION_CIRCUITS_PARAMS[0].0,
    ALL_DELEGATION_CIRCUITS_PARAMS[0].1,
    &ALL_DELEGATION_CIRCUITS_PARAMS[0].2,
    BLAKE_WITH_COMPRESSION_VERIFIER_PTR,
)];

#[cfg(feature = "verifiers")]
pub const FINAL_RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS: &[(
    u32,
    u32,
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] = &[];

#[cfg(feature = "verifiers")]
const _: () = {
    let mut t = BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS[0].0;
    let mut i = 1;
    while i < BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS.len() {
        assert!(t < BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS[i].0);
        t = BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS[i].0;
        i += 1
    }

    let mut t = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS[0].0;
    let mut i = 1;
    while i < RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS.len() {
        assert!(t < RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS[i].0);
        t = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS[i].0;
        i += 1
    }

    ()
};
