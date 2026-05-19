use crate::constants::*;
use crate::MerkleTreeCap;
use crate::VerifierFunctionPointer;

// ==============================================================================
// Security-Aware Delegation Verifier Dispatch
// ==============================================================================
//
// `full_statement_verifier` sits above the migrated verifier crates, so the
// integration-layer migration happens by selecting the child crate's monomorphic
// `verify_80` / `verify_100` wrapper at runtime instead of introducing another
// `Geometry<S>` layer here.

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
pub const BLAKE_WITH_COMPRESSION_VERIFIER_PTR_80: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    0,
    0,
> = blake2_with_compression_verifier::verify_80;

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
pub const BLAKE_WITH_COMPRESSION_VERIFIER_PTR_100: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    0,
    0,
> = blake2_with_compression_verifier::verify_100;

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
#[inline(always)]
pub const fn blake_with_compression_verifier_ptr(
    security: verifier_common::SecurityModel,
) -> VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0> {
    match security {
        verifier_common::SecurityModel::Security80 => BLAKE_WITH_COMPRESSION_VERIFIER_PTR_80,
        verifier_common::SecurityModel::Security100 => BLAKE_WITH_COMPRESSION_VERIFIER_PTR_100,
    }
}

#[cfg(feature = "verifiers")]
pub const BIGINT_WITH_CONTROL_VERIFIER_PTR_80: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    0,
    0,
> = bigint_with_control_verifier::verify_80;

#[cfg(feature = "verifiers")]
pub const BIGINT_WITH_CONTROL_VERIFIER_PTR_100: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    0,
    0,
> = bigint_with_control_verifier::verify_100;

#[cfg(feature = "verifiers")]
#[inline(always)]
pub const fn bigint_with_control_verifier_ptr(
    security: verifier_common::SecurityModel,
) -> VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0> {
    match security {
        verifier_common::SecurityModel::Security80 => BIGINT_WITH_CONTROL_VERIFIER_PTR_80,
        verifier_common::SecurityModel::Security100 => BIGINT_WITH_CONTROL_VERIFIER_PTR_100,
    }
}

#[cfg(feature = "verifiers")]
pub const KECCAK_SPECIAL5_CONTROL_VERIFIER_PTR_80: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    0,
    0,
> = keccak_special5_verifier::verify_80;

#[cfg(feature = "verifiers")]
pub const KECCAK_SPECIAL5_CONTROL_VERIFIER_PTR_100: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    NUM_DELEGATION_CHALLENGES,
    0,
    0,
> = keccak_special5_verifier::verify_100;

#[cfg(feature = "verifiers")]
#[inline(always)]
pub const fn keccak_special5_control_verifier_ptr(
    security: verifier_common::SecurityModel,
) -> VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0> {
    match security {
        verifier_common::SecurityModel::Security80 => KECCAK_SPECIAL5_CONTROL_VERIFIER_PTR_80,
        verifier_common::SecurityModel::Security100 => KECCAK_SPECIAL5_CONTROL_VERIFIER_PTR_100,
    }
}

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
use crate::constants::ALL_DELEGATION_CIRCUITS_PARAMS;

#[cfg(feature = "verifiers")]
pub const BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_80: &[(
    u32, // delegation type
    u32, // delegation capacity
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] = &[
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[0].0,
        ALL_DELEGATION_CIRCUITS_PARAMS[0].1,
        &ALL_DELEGATION_CIRCUITS_PARAMS[0].2,
        BLAKE_WITH_COMPRESSION_VERIFIER_PTR_80,
    ),
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[1].0,
        ALL_DELEGATION_CIRCUITS_PARAMS[1].1,
        &ALL_DELEGATION_CIRCUITS_PARAMS[1].2,
        BIGINT_WITH_CONTROL_VERIFIER_PTR_80,
    ),
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[2].0,
        ALL_DELEGATION_CIRCUITS_PARAMS[2].1,
        &ALL_DELEGATION_CIRCUITS_PARAMS[2].2,
        KECCAK_SPECIAL5_CONTROL_VERIFIER_PTR_80,
    ),
];

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
pub const RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_80: &[(
    u32,
    u32,
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] = &[(
    ALL_DELEGATION_CIRCUITS_PARAMS[0].0,
    ALL_DELEGATION_CIRCUITS_PARAMS[0].1,
    &ALL_DELEGATION_CIRCUITS_PARAMS[0].2,
    BLAKE_WITH_COMPRESSION_VERIFIER_PTR_80,
)];

#[cfg(feature = "verifiers")]
pub const FINAL_RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS: &[(
    u32,
    u32,
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] = &[];

#[cfg(feature = "verifiers")]
pub const BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_100: &[(
    u32, // delegation type
    u32, // delegation capacity
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] = &[
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[0].0,
        ALL_DELEGATION_CIRCUITS_PARAMS[0].1,
        &ALL_DELEGATION_CIRCUITS_PARAMS[0].2,
        BLAKE_WITH_COMPRESSION_VERIFIER_PTR_100,
    ),
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[1].0,
        ALL_DELEGATION_CIRCUITS_PARAMS[1].1,
        &ALL_DELEGATION_CIRCUITS_PARAMS[1].2,
        BIGINT_WITH_CONTROL_VERIFIER_PTR_100,
    ),
    (
        ALL_DELEGATION_CIRCUITS_PARAMS[2].0,
        ALL_DELEGATION_CIRCUITS_PARAMS[2].1,
        &ALL_DELEGATION_CIRCUITS_PARAMS[2].2,
        KECCAK_SPECIAL5_CONTROL_VERIFIER_PTR_100,
    ),
];

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
pub const RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_100: &[(
    u32,
    u32,
    &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] = &[(
    ALL_DELEGATION_CIRCUITS_PARAMS[0].0,
    ALL_DELEGATION_CIRCUITS_PARAMS[0].1,
    &ALL_DELEGATION_CIRCUITS_PARAMS[0].2,
    BLAKE_WITH_COMPRESSION_VERIFIER_PTR_100,
)];

#[cfg(feature = "verifiers")]
#[inline(always)]
pub fn base_layer_delegation_circuits_verification_parameters(
    security: verifier_common::SecurityModel,
) -> &'static [(
    u32,
    u32,
    &'static [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] {
    match security {
        verifier_common::SecurityModel::Security80 => {
            BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_80
        }
        verifier_common::SecurityModel::Security100 => {
            BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_100
        }
    }
}

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
#[inline(always)]
pub fn recursion_layer_circuits_verification_parameters(
    security: verifier_common::SecurityModel,
) -> &'static [(
    u32,
    u32,
    &'static [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
    VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0>,
)] {
    match security {
        verifier_common::SecurityModel::Security80 => {
            RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_80
        }
        verifier_common::SecurityModel::Security100 => {
            RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_100
        }
    }
}

#[cfg(feature = "verifiers")]
const _: () = {
    let mut t = BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_80[0].0;
    let mut i = 1;
    while i < BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_80.len() {
        assert!(t < BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_80[i].0);
        t = BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_80[i].0;
        i += 1
    }

    let mut t = BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_100[0].0;
    let mut i = 1;
    while i < BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_100.len() {
        assert!(t < BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_100[i].0);
        t = BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS_100[i].0;
        i += 1
    }

    let mut t = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_80[0].0;
    let mut i = 1;
    while i < RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_80.len() {
        assert!(t < RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_80[i].0);
        t = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_80[i].0;
        i += 1
    }

    let mut t = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_100[0].0;
    let mut i = 1;
    while i < RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_100.len() {
        assert!(t < RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_100[i].0);
        t = RECURSION_LAYER_CIRCUITS_VERIFICATION_PARAMETERS_100[i].0;
        i += 1
    }

    ()
};
