use verifier_common::SecurityModel;

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
use crate::constants::{CAP_SIZE, NUM_COSETS};

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
fn assert_verifier_dispatch<
    const NUM_DELEGATION_CHALLENGES: usize,
    const NUM_AUX_BOUNDARY_VALUES: usize,
    const NUM_STATE_ELEMENTS: usize,
    const NUM_MACHINE_STATE_CHALLENGES: usize,
>(
    actual: verifier_common::VerifierFunctionPointer<
        CAP_SIZE,
        NUM_COSETS,
        NUM_DELEGATION_CHALLENGES,
        NUM_AUX_BOUNDARY_VALUES,
        NUM_STATE_ELEMENTS,
        NUM_MACHINE_STATE_CHALLENGES,
    >,
    expected: verifier_common::VerifierFunctionPointer<
        CAP_SIZE,
        NUM_COSETS,
        NUM_DELEGATION_CHALLENGES,
        NUM_AUX_BOUNDARY_VALUES,
        NUM_STATE_ELEMENTS,
        NUM_MACHINE_STATE_CHALLENGES,
    >,
    message: &str,
) {
    assert!(
        core::ptr::eq(actual as *const (), expected as *const ()),
        "{message}"
    );
}

#[cfg(feature = "verifiers")]
fn assert_unrolled_no_delegation_dispatch(
    actual: crate::unrolled_proof_statement::VerificationFunctionPointer,
    expected: verifier_common::VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, 0, 0, 0, 1>,
    message: &str,
) {
    match actual {
        crate::unrolled_proof_statement::VerificationFunctionPointer::UnrolledNoDelegation(
            actual,
        ) => {
            assert_verifier_dispatch(actual, expected, message);
        }
        crate::unrolled_proof_statement::VerificationFunctionPointer::UnrolledWithDelegation(_) => {
            panic!("{message}: expected verifier without delegation")
        }
    }
}

#[cfg(feature = "verifiers")]
fn assert_unrolled_with_delegation_dispatch(
    actual: crate::unrolled_proof_statement::VerificationFunctionPointer,
    expected: verifier_common::VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, 1, 0, 0, 1>,
    message: &str,
) {
    match actual {
        crate::unrolled_proof_statement::VerificationFunctionPointer::UnrolledNoDelegation(_) => {
            panic!("{message}: expected verifier with delegation")
        }
        crate::unrolled_proof_statement::VerificationFunctionPointer::UnrolledWithDelegation(
            actual,
        ) => {
            assert_verifier_dispatch(actual, expected, message);
        }
    }
}

#[cfg(any(feature = "verifiers", feature = "unified_verifier_only"))]
#[test]
fn unified_dispatch_uses_matching_security_wrappers() {
    let verifier_80 = crate::unified_circuit_statement::reduced_unified_circuit_verifier_ptr(
        SecurityModel::Security80,
    );
    let verifier_100 = crate::unified_circuit_statement::reduced_unified_circuit_verifier_ptr(
        SecurityModel::Security100,
    );

    assert_verifier_dispatch(
        verifier_80,
        unified_reduced_machine_verifier::verify_80,
        "80-bit unified recursion must use verify_80",
    );
    assert_verifier_dispatch(
        verifier_100,
        unified_reduced_machine_verifier::verify_100,
        "100-bit unified recursion must use verify_100",
    );

    let recursion_80 =
        crate::imports::recursion_layer_circuits_verification_parameters(SecurityModel::Security80);
    let recursion_100 = crate::imports::recursion_layer_circuits_verification_parameters(
        SecurityModel::Security100,
    );

    assert_eq!(recursion_80.len(), 1);
    assert_eq!(recursion_100.len(), 1);
    assert_verifier_dispatch(
        recursion_80[0].3,
        blake2_with_compression_verifier::verify_80,
        "80-bit recursion delegation must use verify_80",
    );
    assert_verifier_dispatch(
        recursion_100[0].3,
        blake2_with_compression_verifier::verify_100,
        "100-bit recursion delegation must use verify_100",
    );
}

#[cfg(feature = "verifiers")]
#[test]
fn unrolled_dispatch_uses_matching_security_wrappers() {
    let base_delegation_80 = crate::imports::base_layer_delegation_circuits_verification_parameters(
        SecurityModel::Security80,
    );
    let base_delegation_100 =
        crate::imports::base_layer_delegation_circuits_verification_parameters(
            SecurityModel::Security100,
        );

    assert_eq!(base_delegation_80.len(), 3);
    assert_eq!(base_delegation_100.len(), 3);
    assert_verifier_dispatch(
        base_delegation_80[0].3,
        blake2_with_compression_verifier::verify_80,
        "80-bit Blake delegation must use verify_80",
    );
    assert_verifier_dispatch(
        base_delegation_100[0].3,
        blake2_with_compression_verifier::verify_100,
        "100-bit Blake delegation must use verify_100",
    );
    assert_verifier_dispatch(
        base_delegation_80[1].3,
        bigint_with_control_verifier::verify_80,
        "80-bit bigint delegation must use verify_80",
    );
    assert_verifier_dispatch(
        base_delegation_100[1].3,
        bigint_with_control_verifier::verify_100,
        "100-bit bigint delegation must use verify_100",
    );
    assert_verifier_dispatch(
        base_delegation_80[2].3,
        keccak_special5_verifier::verify_80,
        "80-bit keccak delegation must use verify_80",
    );
    assert_verifier_dispatch(
        base_delegation_100[2].3,
        keccak_special5_verifier::verify_100,
        "100-bit keccak delegation must use verify_100",
    );

    let circuits_80 =
        crate::unrolled_proof_statement::full_unsigned_machine_unrolled_circuits_verification_parameters(
            SecurityModel::Security80,
        );
    let circuits_100 =
        crate::unrolled_proof_statement::full_unsigned_machine_unrolled_circuits_verification_parameters(
            SecurityModel::Security100,
        );

    assert_eq!(
        circuits_80.len(),
        crate::unrolled_proof_statement::FULL_UNSIGNED_MACHINE_NUM_UNROLLED_CIRCUITS
    );
    assert_eq!(
        circuits_100.len(),
        crate::unrolled_proof_statement::FULL_UNSIGNED_MACHINE_NUM_UNROLLED_CIRCUITS
    );

    assert_unrolled_no_delegation_dispatch(
        circuits_80[0].2,
        add_sub_lui_auipc_mop_verifier::verify_80,
        "80-bit add/sub verifier must use verify_80",
    );
    assert_unrolled_no_delegation_dispatch(
        circuits_100[0].2,
        add_sub_lui_auipc_mop_verifier::verify_100,
        "100-bit add/sub verifier must use verify_100",
    );
    assert_unrolled_with_delegation_dispatch(
        circuits_80[2].2,
        shift_binary_csr_verifier::verify_80,
        "80-bit shift verifier must use verify_80",
    );
    assert_unrolled_with_delegation_dispatch(
        circuits_100[2].2,
        shift_binary_csr_verifier::verify_100,
        "100-bit shift verifier must use verify_100",
    );

    let inits_and_teardowns_80 = crate::unrolled_proof_statement::inits_and_teardowns_verifier_ptr(
        SecurityModel::Security80,
    );
    let inits_and_teardowns_100 = crate::unrolled_proof_statement::inits_and_teardowns_verifier_ptr(
        SecurityModel::Security100,
    );

    assert_verifier_dispatch(
        inits_and_teardowns_80,
        inits_and_teardowns_verifier::verify_80,
        "80-bit inits/teardowns must use verify_80",
    );
    assert_verifier_dispatch(
        inits_and_teardowns_100,
        inits_and_teardowns_verifier::verify_100,
        "100-bit inits/teardowns must use verify_100",
    );
}
