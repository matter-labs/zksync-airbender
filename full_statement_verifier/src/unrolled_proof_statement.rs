use crate::statement_common::{
    read_setups, FINAL_PC_BUFFER_PC_IDX, FINAL_PC_BUFFER_TS_HIGH_IDX, FINAL_PC_BUFFER_TS_LOW_IDX,
};
use common_constants::{INITIAL_PC, INITIAL_TIMESTAMP};
use verifier_common::{cs::definitions::split_timestamp, DefaultNonDeterminismSource};

use super::*;
use crate::imports::*;

pub fn caps_flattened(caps: &'_ [MerkleTreeCap<CAP_SIZE>; NUM_COSETS]) -> &'_ [u32] {
    unsafe {
        core::slice::from_ptr_range(
            caps.as_ptr_range().start.cast::<u32>()..caps.as_ptr_range().end.cast::<u32>(),
        )
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(usize)]
pub enum VerificationFunctionPointer {
    UnrolledNoDelegation(VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, 0, 0, 0, 1>),
    UnrolledWithDelegation(VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, 1, 0, 0, 1>),
}

pub const INITS_AND_TEARDOWNS_CAPACITY_PER_SET: u32 =
    (inits_and_teardowns_verifier::concrete::size_constants::TRACE_LEN - 1) as u32;
pub const MAX_MEMORY_CELLS_TO_INIT: u32 = const {
    let mut max_cells = 1u32 << 30;
    max_cells -= common_constants::rom::ROM_WORD_SIZE as u32;

    max_cells
};

// ==============================================================================
// Security-Aware Unrolled Verifier Dispatch
// ==============================================================================
//
// This crate stitches together proofs produced by many verifier crates. The
// integration-layer migration therefore keeps the stitching logic intact and
// swaps the child verifier function pointers to the matching `verify_80` or
// `verify_100` entrypoint before verification starts.

pub const ADD_SUB_LUI_AUIPC_MOP_VERIFIER_PTR_80: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(add_sub_lui_auipc_mop_verifier::verify_80);
pub const ADD_SUB_LUI_AUIPC_MOP_VERIFIER_PTR_100: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(add_sub_lui_auipc_mop_verifier::verify_100);
pub const JUMP_BRANCH_SLT_VERIFIER_PTR_80: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(jump_branch_slt_verifier::verify_80);
pub const JUMP_BRANCH_SLT_VERIFIER_PTR_100: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(jump_branch_slt_verifier::verify_100);
pub const LOAD_STORE_SUBWORD_ONLY_VERIFIER_PTR_80: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(load_store_subword_only_verifier::verify_80);
pub const LOAD_STORE_SUBWORD_ONLY_VERIFIER_PTR_100: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(load_store_subword_only_verifier::verify_100);
pub const LOAD_STORE_WORD_ONLY_VERIFIER_PTR_80: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(load_store_word_only_verifier::verify_80);
pub const LOAD_STORE_WORD_ONLY_VERIFIER_PTR_100: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(load_store_word_only_verifier::verify_100);
pub const MUL_DIV_VERIFIER_PTR_80: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(mul_div_verifier::verify_80);
pub const MUL_DIV_VERIFIER_PTR_100: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(mul_div_verifier::verify_100);
pub const MUL_DIV_UNSIGNED_VERIFIER_PTR_80: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(mul_div_unsigned_verifier::verify_80);
pub const MUL_DIV_UNSIGNED_VERIFIER_PTR_100: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledNoDelegation(mul_div_unsigned_verifier::verify_100);
pub const SHIFT_BINARY_CSR_VERIFIER_PTR_80: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledWithDelegation(shift_binary_csr_verifier::verify_80);
pub const SHIFT_BINARY_CSR_VERIFIER_PTR_100: VerificationFunctionPointer =
    VerificationFunctionPointer::UnrolledWithDelegation(shift_binary_csr_verifier::verify_100);

pub const FULL_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_80: &[(
    u32, // family
    u32, // capacity
    VerificationFunctionPointer,
)] = &[
    (
        common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
        (add_sub_lui_auipc_mop_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        ADD_SUB_LUI_AUIPC_MOP_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
        (jump_branch_slt_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        JUMP_BRANCH_SLT_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX as u32,
        (shift_binary_csr_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        SHIFT_BINARY_CSR_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::MUL_DIV_CIRCUIT_FAMILY_IDX as u32,
        (mul_div_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        MUL_DIV_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        (load_store_word_only_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        LOAD_STORE_WORD_ONLY_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        (load_store_subword_only_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        LOAD_STORE_SUBWORD_ONLY_VERIFIER_PTR_80,
    ),
];

pub const FULL_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_100: &[(
    u32, // family
    u32, // capacity
    VerificationFunctionPointer,
)] = &[
    (
        common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
        (add_sub_lui_auipc_mop_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        ADD_SUB_LUI_AUIPC_MOP_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
        (jump_branch_slt_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        JUMP_BRANCH_SLT_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX as u32,
        (shift_binary_csr_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        SHIFT_BINARY_CSR_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::MUL_DIV_CIRCUIT_FAMILY_IDX as u32,
        (mul_div_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        MUL_DIV_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        (load_store_word_only_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        LOAD_STORE_WORD_ONLY_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        (load_store_subword_only_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        LOAD_STORE_SUBWORD_ONLY_VERIFIER_PTR_100,
    ),
];

pub const FULL_MACHINE_NUM_UNROLLED_CIRCUITS: usize =
    const { FULL_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_80.len() };

pub const FULL_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_80: &[(
    u32, // family
    u32, // capacity
    VerificationFunctionPointer,
)] = &[
    (
        common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
        (add_sub_lui_auipc_mop_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        ADD_SUB_LUI_AUIPC_MOP_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
        (jump_branch_slt_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        JUMP_BRANCH_SLT_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX as u32,
        (shift_binary_csr_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        SHIFT_BINARY_CSR_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::MUL_DIV_CIRCUIT_FAMILY_IDX as u32,
        (mul_div_unsigned_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        MUL_DIV_UNSIGNED_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        (load_store_word_only_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        LOAD_STORE_WORD_ONLY_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        (load_store_subword_only_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        LOAD_STORE_SUBWORD_ONLY_VERIFIER_PTR_80,
    ),
];

pub const FULL_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_100: &[(
    u32, // family
    u32, // capacity
    VerificationFunctionPointer,
)] = &[
    (
        common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
        (add_sub_lui_auipc_mop_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        ADD_SUB_LUI_AUIPC_MOP_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
        (jump_branch_slt_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        JUMP_BRANCH_SLT_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX as u32,
        (shift_binary_csr_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        SHIFT_BINARY_CSR_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::MUL_DIV_CIRCUIT_FAMILY_IDX as u32,
        (mul_div_unsigned_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        MUL_DIV_UNSIGNED_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        (load_store_word_only_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        LOAD_STORE_WORD_ONLY_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        (load_store_subword_only_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        LOAD_STORE_SUBWORD_ONLY_VERIFIER_PTR_100,
    ),
];

pub const FULL_UNSIGNED_MACHINE_NUM_UNROLLED_CIRCUITS: usize =
    const { FULL_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_80.len() };

pub const RECURSION_WORD_ONLY_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_80: &[(
    u32, // family
    u32, // capacity
    VerificationFunctionPointer,
)] = &[
    (
        common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
        (add_sub_lui_auipc_mop_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        ADD_SUB_LUI_AUIPC_MOP_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
        (jump_branch_slt_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        JUMP_BRANCH_SLT_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX as u32,
        (shift_binary_csr_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        SHIFT_BINARY_CSR_VERIFIER_PTR_80,
    ),
    (
        common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        (load_store_word_only_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        LOAD_STORE_WORD_ONLY_VERIFIER_PTR_80,
    ),
];

pub const RECURSION_WORD_ONLY_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_100:
    &[(
        u32, // family
        u32, // capacity
        VerificationFunctionPointer,
    )] = &[
    (
        common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
        (add_sub_lui_auipc_mop_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        ADD_SUB_LUI_AUIPC_MOP_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
        (jump_branch_slt_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        JUMP_BRANCH_SLT_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX as u32,
        (shift_binary_csr_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        SHIFT_BINARY_CSR_VERIFIER_PTR_100,
    ),
    (
        common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        (load_store_word_only_verifier::concrete::size_constants::TRACE_LEN - 1) as u32,
        LOAD_STORE_WORD_ONLY_VERIFIER_PTR_100,
    ),
];

pub const RECURSION_WORD_ONLY_UNSIGNED_MACHINE_NUM_UNROLLED_CIRCUITS: usize = const {
    RECURSION_WORD_ONLY_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_80.len()
};

pub const INITS_AND_TEARDOWNS_VERIFIER_PTR_80: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    0,
    { inits_and_teardowns_verifier::concrete::size_constants::NUM_AUX_BOUNDARY_VALUES },
    0,
> = inits_and_teardowns_verifier::verify_80;

pub const INITS_AND_TEARDOWNS_VERIFIER_PTR_100: VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    0,
    { inits_and_teardowns_verifier::concrete::size_constants::NUM_AUX_BOUNDARY_VALUES },
    0,
> = inits_and_teardowns_verifier::verify_100;

#[inline(always)]
pub const fn full_machine_unrolled_circuits_verification_parameters(
    security: verifier_common::SecurityModel,
) -> &'static [(u32, u32, VerificationFunctionPointer)] {
    match security {
        verifier_common::SecurityModel::Security80 => {
            FULL_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_80
        }
        verifier_common::SecurityModel::Security100 => {
            FULL_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_100
        }
    }
}

#[inline(always)]
pub const fn full_unsigned_machine_unrolled_circuits_verification_parameters(
    security: verifier_common::SecurityModel,
) -> &'static [(u32, u32, VerificationFunctionPointer)] {
    match security {
        verifier_common::SecurityModel::Security80 => {
            FULL_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_80
        }
        verifier_common::SecurityModel::Security100 => {
            FULL_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_100
        }
    }
}

#[inline(always)]
pub const fn recursion_word_only_unsigned_machine_unrolled_circuits_verification_parameters(
    security: verifier_common::SecurityModel,
) -> &'static [(u32, u32, VerificationFunctionPointer)] {
    match security {
        verifier_common::SecurityModel::Security80 => {
            RECURSION_WORD_ONLY_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_80
        }
        verifier_common::SecurityModel::Security100 => {
            RECURSION_WORD_ONLY_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS_100
        }
    }
}

#[inline(always)]
pub const fn inits_and_teardowns_verifier_ptr(
    security: verifier_common::SecurityModel,
) -> VerifierFunctionPointer<
    CAP_SIZE,
    NUM_COSETS,
    0,
    { inits_and_teardowns_verifier::concrete::size_constants::NUM_AUX_BOUNDARY_VALUES },
    0,
> {
    match security {
        verifier_common::SecurityModel::Security80 => INITS_AND_TEARDOWNS_VERIFIER_PTR_80,
        verifier_common::SecurityModel::Security100 => INITS_AND_TEARDOWNS_VERIFIER_PTR_100,
    }
}

/// If we recurse over user's program -> we must provide expected final PC,
/// and setup caps (that encode the program itself!),
/// otherwise we only need to provide final PC
#[allow(invalid_value)]
#[inline(never)]
pub unsafe fn verify_full_statement_for_unrolled_circuits<
    const BASE_LAYER: bool,
    const NUM_INIT_AND_TEARDOWN_SETS: usize,
>(
    circuits_families_setups: &[&[MerkleTreeCap<CAP_SIZE>; NUM_COSETS]],
    // circuit type/delegation type, capacity, setup, verifier function
    circuits_families_verifiers: &[(u32, u32, VerificationFunctionPointer)],
    // capacity per set, setup, verifier function
    inits_and_teardowns_verifier: (
        &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
        VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, 0, NUM_INIT_AND_TEARDOWN_SETS, 0, 0>,
    ),
    // circuit type/delegation type, capacity, setup, verifier function
    delegation_circuits_verifiers: &[(
        u32,
        u32,
        &[MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
        VerifierFunctionPointer<CAP_SIZE, NUM_COSETS, NUM_DELEGATION_CHALLENGES, 0, 0, 0>,
    )],
    security_model: verifier_common::SecurityModel,
) -> [u32; 16] {
    assert_eq!(
        circuits_families_setups.len(),
        circuits_families_verifiers.len()
    );
    debug_assert!(circuits_families_verifiers.is_sorted_by(|a, b| { a.0 < b.0 }));
    // we should in parallel verify proofs, and drag along the transcript to assert equality of challenges
    let mut transcript = Blake2sBufferingTranscript::new();

    let mut registers_buffer = MaybeUninit::<[u32; 32 + 2 * 32]>::uninit().assume_init();

    // first we need to get final register values and timestamps
    for reg_idx in 0..32 {
        let value = verifier_common::DefaultNonDeterminismSource::read_word();
        let timestamp_low = verifier_common::DefaultNonDeterminismSource::read_word();
        let timestamp_high = verifier_common::DefaultNonDeterminismSource::read_word();
        registers_buffer[reg_idx * 3] = value;
        registers_buffer[reg_idx * 3 + 1] = timestamp_low;
        registers_buffer[reg_idx * 3 + 2] = timestamp_high;
    }

    // x0 is always 0, for sanity
    assert_eq!(registers_buffer[0], 0);

    transcript.absorb(&registers_buffer);

    let mut final_pc_buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    let final_pc = verifier_common::DefaultNonDeterminismSource::read_word();
    let final_ts_low = verifier_common::DefaultNonDeterminismSource::read_word();
    let final_ts_high = verifier_common::DefaultNonDeterminismSource::read_word();
    final_pc_buffer[FINAL_PC_BUFFER_PC_IDX] = final_pc;
    final_pc_buffer[FINAL_PC_BUFFER_TS_LOW_IDX] = final_ts_low;
    final_pc_buffer[FINAL_PC_BUFFER_TS_HIGH_IDX] = final_ts_high;

    transcript.absorb(&final_pc_buffer);

    // continue with main RISC-V cycles
    let mut grand_product_accumulator = Mersenne31Quartic::ONE;
    let mut delegation_set_accumulator = Mersenne31Quartic::ZERO;

    let mut proof_output_for_reference_challenges: ProofOutput<CAP_SIZE, NUM_COSETS, 0, 0, 1> =
        MaybeUninit::uninit().assume_init();

    // loop over main circuit type
    let mut proof_output_0_scratch: ProofOutput<CAP_SIZE, NUM_COSETS, 0, 0, 1> =
        MaybeUninit::uninit().assume_init();
    let mut proof_output_1_scratch: ProofOutput<CAP_SIZE, NUM_COSETS, 0, 0, 1> =
        MaybeUninit::uninit().assume_init();
    let mut proof_output_with_delegation_0_scratch: ProofOutput<CAP_SIZE, NUM_COSETS, 1, 0, 1> =
        MaybeUninit::uninit().assume_init();
    let mut proof_output_with_delegation_1_scratch: ProofOutput<CAP_SIZE, NUM_COSETS, 1, 0, 1> =
        MaybeUninit::uninit().assume_init();
    let mut state_variables = ProofPublicInputs::uninit();
    let mut non_delegation_used = false;
    let mut delegation_used = false;

    // NOTE: in unrolled circuits we do have contribution from setup values into
    // memory or delegation, so we skip setups here (same as we do with delegation circuits in general)

    let mut total_cycles = 0u64;
    for ((circuit_family, capacity, verifier_fn), setup) in circuits_families_verifiers
        .iter()
        .zip(circuits_families_setups.iter())
    {
        let num_circuits = verifier_common::DefaultNonDeterminismSource::read_word();
        if num_circuits > 0 {
            let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            buffer[0] = *circuit_family;
            transcript.absorb(&buffer);
        }

        for circuit_sequence in 0..num_circuits {
            match verifier_fn {
                VerificationFunctionPointer::UnrolledNoDelegation(verifier_fn) => {
                    let (current, previous) = if circuit_sequence == 0 {
                        (&mut proof_output_0_scratch, &proof_output_1_scratch)
                    } else {
                        (&mut proof_output_1_scratch, &proof_output_0_scratch)
                    };
                    (verifier_fn)(current, &mut state_variables);

                    assert_eq!(current.circuit_sequence, 0);
                    assert_eq!(current.delegation_type, 0);

                    // and commit memory caps
                    transcript.absorb(current.memory_caps_flattened());

                    non_delegation_used |= true;

                    // we copy our first reference challenges
                    if total_cycles == 0 {
                        proof_output_for_reference_challenges = *current;
                    }

                    // we compare setups across different instances of the same type
                    if circuit_sequence > 0 {
                        assert!(MerkleTreeCap::compare(
                            &previous.setup_caps,
                            &current.setup_caps
                        ));
                    } else {
                        assert!(MerkleTreeCap::compare(*setup, &current.setup_caps));
                    }

                    // and challenges - against reference
                    if total_cycles > 0 {
                        // check that all challenges are the same as reference ones
                        assert_eq!(
                            proof_output_for_reference_challenges.memory_challenges,
                            current.memory_challenges
                        );
                        // there are no delegation challenges
                        assert_eq!(
                            proof_output_for_reference_challenges
                                .machine_state_permutation_challenges,
                            current.machine_state_permutation_challenges
                        );
                    }

                    // update accumulators
                    grand_product_accumulator.mul_assign(&current.grand_product_accumulator);
                    // no update for delegation accumulator
                }
                VerificationFunctionPointer::UnrolledWithDelegation(verifier_fn) => {
                    let (current, previous) = if circuit_sequence == 0 {
                        (
                            &mut proof_output_with_delegation_0_scratch,
                            &proof_output_with_delegation_1_scratch,
                        )
                    } else {
                        (
                            &mut proof_output_with_delegation_1_scratch,
                            &proof_output_with_delegation_0_scratch,
                        )
                    };
                    (verifier_fn)(current, &mut state_variables);

                    assert_eq!(current.circuit_sequence, 0);
                    assert_eq!(current.delegation_type, 0);

                    // and commit memory caps
                    transcript.absorb(current.memory_caps_flattened());

                    delegation_used |= true;

                    // we compare setups across different instances of the same type
                    if circuit_sequence > 0 {
                        assert!(MerkleTreeCap::compare(
                            &previous.setup_caps,
                            &current.setup_caps
                        ));
                        // and here we also compare delegation challenges
                        assert_eq!(
                            previous.delegation_challenges,
                            current.delegation_challenges
                        );
                    } else {
                        assert!(MerkleTreeCap::compare(*setup, &current.setup_caps));
                    }

                    // compare versus reference ones, and we expect that for any reasonable program
                    // there will be other circuit types before one with delegations
                    {
                        assert!(total_cycles > 0);
                        // check that all challenges are the same as reference ones
                        assert_eq!(
                            proof_output_for_reference_challenges.memory_challenges,
                            current.memory_challenges
                        );
                        // there are no delegation challenges
                        assert_eq!(
                            proof_output_for_reference_challenges
                                .machine_state_permutation_challenges,
                            current.machine_state_permutation_challenges
                        );
                    }

                    // update accumulators
                    grand_product_accumulator.mul_assign(&current.grand_product_accumulator);
                    delegation_set_accumulator
                        .add_assign(&current.delegation_argument_accumulator[0]);
                }
            }
            total_cycles += *capacity as u64;
            assert!(total_cycles < MAX_CYCLES);
        }
    }

    // Check that we actually run something meaningful
    assert!(total_cycles > 0);

    // Check that we have values initialized for challenge comparisons used below
    assert!(non_delegation_used);

    // then init/teardown circuits
    {
        let mut inits_and_teardowns_proof_output_0: ProofOutput<
            CAP_SIZE,
            NUM_COSETS,
            0,
            NUM_INIT_AND_TEARDOWN_SETS,
        > = MaybeUninit::uninit().assume_init();
        let mut inits_and_teardowns_proof_output_1: ProofOutput<
            CAP_SIZE,
            NUM_COSETS,
            0,
            NUM_INIT_AND_TEARDOWN_SETS,
        > = MaybeUninit::uninit().assume_init();
        let mut state_variables = ProofPublicInputs::uninit();

        let num_circuits = verifier_common::DefaultNonDeterminismSource::read_word();
        if num_circuits > 0 {
            let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
            buffer[0] =
                common_constants::circuit_families::INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX
                    as u32;
            transcript.absorb(&buffer);
        }

        let mut cells_initialized = 0;
        for circuit_sequence in 0..num_circuits {
            assert!(cells_initialized < MAX_MEMORY_CELLS_TO_INIT);
            let (setup, verifier_fn) = inits_and_teardowns_verifier;
            // NOTE: here we have some relations to check across circuits of the same type, so it's not just 0 check
            let (current, previous) = if circuit_sequence & 1 == 0 {
                (
                    &mut inits_and_teardowns_proof_output_0,
                    &inits_and_teardowns_proof_output_1,
                )
            } else {
                (
                    &mut inits_and_teardowns_proof_output_1,
                    &inits_and_teardowns_proof_output_0,
                )
            };
            (verifier_fn)(current, &mut state_variables);

            assert_eq!(current.circuit_sequence, 0);
            assert_eq!(current.delegation_type, 0);

            // and commit memory caps
            transcript.absorb(current.memory_caps_flattened());

            // check that all of them share the same setup

            if circuit_sequence > 0 {
                // and check equality of the setup
                assert!(MerkleTreeCap::compare(
                    &previous.setup_caps,
                    &current.setup_caps
                ));
            } else {
                assert!(MerkleTreeCap::compare(setup, &current.setup_caps));
            }

            // compare challenges against reference
            assert_eq!(
                proof_output_for_reference_challenges.memory_challenges,
                current.memory_challenges
            );

            // update accumulators
            grand_product_accumulator.mul_assign(&current.grand_product_accumulator);

            let mut last_previous = if circuit_sequence == 0 {
                InitAndTeardownTuple {
                    address: 0u32,
                    teardown_value: 0u32,
                    teardown_ts_pair: (0u32, 0u32),
                }
            } else {
                InitAndTeardownTuple::from_aux_values_one_before_last_row(
                    &previous.lazy_init_boundary_values[NUM_INIT_AND_TEARDOWN_SETS - 1],
                )
            };

            // check that addresses are sorted at juctions
            for i in 0..NUM_INIT_AND_TEARDOWN_SETS {
                cells_initialized += INITS_AND_TEARDOWNS_CAPACITY_PER_SET;
                let first_current_address = parse_field_els_as_u32_from_u16_limbs_checked(
                    current.lazy_init_boundary_values[i].lazy_init_first_row,
                );

                // if it's
                if last_previous.address < first_current_address {
                    // nothing, we are all good
                } else {
                    // we require padding of 0 init address, and 0 teardown value and timestamp
                    assert_eq!(last_previous.address, 0);
                    assert_eq!(last_previous.teardown_value, 0);

                    // just compare to 0 after reduction to avoid parsing u16 or timestamp bits
                    assert_eq!(last_previous.teardown_ts_pair.0, 0);
                    assert_eq!(last_previous.teardown_ts_pair.1, 0);
                }

                // circuits sort addresses in the column, so we just need to re-assign
                last_previous = InitAndTeardownTuple::from_aux_values_one_before_last_row(
                    &current.lazy_init_boundary_values[i],
                )
            }
        }
    }

    // If we will even want to break an execution here, we will have full buffer (unflushed)
    assert!(transcript.get_current_buffer_offset() == BLAKE2S_BLOCK_SIZE_U32_WORDS);

    // since we have > 0 main circuits, then we can always use `proof_output_0` below

    // ok, now we forget about main circuit and potentially parse delegations
    if NUM_DELEGATION_CHALLENGES > 0 {
        let mut previous_delegation_type = 0u32;
        let mut state_variables = ProofPublicInputs::uninit();
        let mut delegation_proof_output = MaybeUninit::uninit().assume_init();

        let mut total_delegation_requests = 0u64;

        for (delegation_type, delegation_requests_per_circuit, setup_caps, verification_function) in
            delegation_circuits_verifiers.iter()
        {
            assert!(previous_delegation_type < *delegation_type);
            previous_delegation_type = *delegation_type;

            let num_circuits = verifier_common::DefaultNonDeterminismSource::read_word();

            if num_circuits > 0 {
                // there should be some other circuit type to produce them
                assert!(delegation_used);
                let mut buffer = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
                buffer[0] = *delegation_type;
                transcript.absorb(&buffer);
            }

            for _circuit_sequence in 0..num_circuits {
                (verification_function)(&mut delegation_proof_output, &mut state_variables);

                assert_eq!(delegation_proof_output.circuit_sequence, 0);
                assert_eq!(delegation_proof_output.delegation_type, *delegation_type);
                assert!(MerkleTreeCap::compare(
                    &delegation_proof_output.setup_caps,
                    setup_caps
                ));

                // and commit memory caps
                transcript.absorb(delegation_proof_output.memory_caps_flattened());

                // check that we use the same challenges as base circuits

                // always compare memory
                assert_eq!(
                    delegation_proof_output.memory_challenges,
                    proof_output_for_reference_challenges.memory_challenges
                );

                // we checked that delegations were used, so `proof_output_with_delegation_0_scratch` is initialized
                assert_eq!(
                    delegation_proof_output.delegation_challenges,
                    proof_output_with_delegation_0_scratch.delegation_challenges
                );

                // update accumulators
                grand_product_accumulator
                    .mul_assign(&delegation_proof_output.grand_product_accumulator);
                delegation_set_accumulator
                    .sub_assign(&delegation_proof_output.delegation_argument_accumulator[0]);

                total_delegation_requests += (*delegation_requests_per_circuit) as u64;
            }

            // If we will even want to break an execution here, we will have full buffer (unflushed)
            assert!(transcript.get_current_buffer_offset() == BLAKE2S_BLOCK_SIZE_U32_WORDS);
        }

        // we use LogUp like argument for permutation between all delegation requests and responses.
        // All requests are unique (due to timestamps), so to ensure soundness we just require that total number
        // of responses processed it < field size
        assert!(total_delegation_requests < Mersenne31Field::CHARACTERISTICS as u64);
    }

    // so the only thing we need to compare are absolute values of memory and machine state permutation
    // versus external transcript, and delegation challenges if used

    // finish with the transcript, compare memory values from transcript with ones used in proofs
    let memory_seed = transcript.finalize_reset();

    let pow_challenge_low = verifier_common::DefaultNonDeterminismSource::read_word();
    let pow_challenge_high = verifier_common::DefaultNonDeterminismSource::read_word();
    let pow_challenge = (pow_challenge_high as u64) << 32 | (pow_challenge_low as u64);

    let memory_delegation_pow_bits = security_model.memory_delegation_pow_bits();

    let expected_challenges =
        ExternalChallenges::draw_from_transcript_seed_with_delegation_and_state_permutation(
            memory_seed,
            memory_delegation_pow_bits,
            pow_challenge,
        );

    assert_eq!(
        expected_challenges.memory_argument,
        proof_output_for_reference_challenges.memory_challenges
    );
    assert_eq!(
        expected_challenges
            .machine_state_permutation_argument
            .unwrap_unchecked(),
        proof_output_for_reference_challenges.machine_state_permutation_challenges[0]
    );

    if delegation_used {
        assert_eq!(
            expected_challenges.delegation_argument.unwrap_unchecked(),
            proof_output_with_delegation_0_scratch.delegation_challenges[0]
        );
    }

    // conclude that our memory argument is valid
    let register_contribution =
        prover::definitions::produce_register_contribution_into_memory_accumulator_raw(
            core::mem::transmute(&registers_buffer),
            proof_output_for_reference_challenges
                .memory_challenges
                .memory_argument_linearization_challenges,
            proof_output_for_reference_challenges
                .memory_challenges
                .memory_argument_gamma,
        );
    let machine_state_contribution =
        prover::definitions::produce_pc_into_permutation_accumulator_raw(
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            final_pc,
            (final_ts_low, final_ts_high),
            &proof_output_for_reference_challenges.machine_state_permutation_challenges[0]
                .linearization_challenges,
            &proof_output_for_reference_challenges.machine_state_permutation_challenges[0]
                .additive_term,
        );
    grand_product_accumulator.mul_assign(&register_contribution);
    grand_product_accumulator.mul_assign(&machine_state_contribution);

    assert_eq!(grand_product_accumulator, Mersenne31Quartic::ONE);
    assert_eq!(delegation_set_accumulator, Mersenne31Quartic::ZERO);

    // Now we only need to reason about "which program do we execute", and "did it finish successfully or not".

    let mut output: [u32; 16] = MaybeUninit::uninit().assume_init();
    // in any case we carry registers 10-17 to the next layer - those are the output of the base program
    for i in 0..8 {
        output[i] = registers_buffer[(10 + i) * 3];
    }

    // the final piece is to make sure that we ended on the PC that is "expected" (basically - loops to itself, and at the right place),
    // so the program ended logical execution and we can conclude that the set of register values is meaningful

    let mut result_hasher = Blake2sBufferingTranscript::new();
    // NOTE: for parameters we are no longer interested in the timestamp when we ended execution,
    // just on PC
    final_pc_buffer[FINAL_PC_BUFFER_TS_LOW_IDX] = 0;
    final_pc_buffer[FINAL_PC_BUFFER_TS_HIGH_IDX] = 0;

    result_hasher.absorb(&final_pc_buffer);
    for setup in circuits_families_setups.iter() {
        result_hasher.absorb(caps_flattened(*setup));
    }
    result_hasher.absorb(caps_flattened(&inits_and_teardowns_verifier.0));
    let end_params_output = result_hasher.finalize_reset();

    // `end_params_output` now fully describes an ending PC + setups (and setups include program binary)

    if BASE_LAYER {
        // we REQUIRE that remaining 8 registers are 0 in our convention
        let mut all_zeroes = true;
        for i in 8..16 {
            let value = registers_buffer[(10 + i) * 3];
            all_zeroes &= value == 0;
        }
        assert!(all_zeroes);

        // we only start a chain, so we will hash a concatenation of 8x0u32 and end_params_output
        let mut buffer = [0u32; 16];
        for i in 0..8 {
            buffer[8 + i] = end_params_output.0[i];
        }
        result_hasher.absorb(&buffer);
        let recursion_chain_output = result_hasher.finalize_reset();
        for i in 8..16 {
            output[i] = recursion_chain_output.0[i - 8];
        }
    } else {
        // we require that remaining 8 registers are some hash output in nature, that encodes our
        // chain of executed programs

        let mut aux_registers: [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] =
            MaybeUninit::uninit().assume_init();
        for i in 8..16 {
            let value = registers_buffer[(10 + i) * 3];
            aux_registers[i - 8] = value;
        }

        // So prover can ALWAYS present a preimage
        let mut preimage: [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS * 2] =
            MaybeUninit::uninit().assume_init();
        for i in 0..BLAKE2S_DIGEST_SIZE_U32_WORDS * 2 {
            preimage[i] = verifier_common::DefaultNonDeterminismSource::read_word();
        }
        result_hasher.absorb(&preimage);
        let preimage_hash = result_hasher.finalize_reset();
        // manually unrolled to avoid memcmp
        let mut equal = true;
        for i in 0..8 {
            equal &= preimage_hash.0[i] == aux_registers[i];
        }
        assert!(equal);

        // then if last elements of the preimage are equal to the current end parameters - we do not need to continue the chain
        let mut equal = true;
        for i in 0..8 {
            equal &= preimage[i + 8] == end_params_output.0[i];
        }

        if equal {
            // we do not need to continue the chain. So for valid recursion chain is
            // always just a blake ( blake([0u32; 8] || base_program_end_params) || recursion_step_end_params)
            // for the case of all successful ends of execution
            for i in 8..16 {
                output[i] = aux_registers[i - 8];
            }
        } else {
            // concatenate and hash
            let mut input: [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS * 2] =
                MaybeUninit::uninit().assume_init();
            for i in 0..8 {
                input[i] = aux_registers[i];
                input[i + 8] = end_params_output.0[i];
            }
            result_hasher.absorb(&input);
            let new_output_registers = result_hasher.finalize_reset();
            for i in 8..16 {
                output[i] = new_output_registers.0[i - 8];
            }
        }
    }

    output
}

pub fn verify_unrolled_base_layer(security: verifier_common::SecurityModel) -> [u32; 16] {
    unsafe {
        let circuits_setups = read_setups::<
            DefaultNonDeterminismSource,
            FULL_UNSIGNED_MACHINE_NUM_UNROLLED_CIRCUITS,
        >();
        let circuits_setups_refs = circuits_setups.each_ref();
        let inits_and_teardowns_setups = read_setups::<DefaultNonDeterminismSource, 1>();
        verify_full_statement_for_unrolled_circuits::<
            true,
            { inits_and_teardowns_verifier::concrete::size_constants::NUM_AUX_BOUNDARY_VALUES },
        >(
            &circuits_setups_refs,
            full_unsigned_machine_unrolled_circuits_verification_parameters(security),
            (
                &inits_and_teardowns_setups[0],
                inits_and_teardowns_verifier_ptr(security),
            ),
            base_layer_delegation_circuits_verification_parameters(security),
            security,
        )
    }
}

pub fn verify_unrolled_recursion_layer(security: verifier_common::SecurityModel) -> [u32; 16] {
    unsafe {
        let circuits_setups = read_setups::<
            DefaultNonDeterminismSource,
            RECURSION_WORD_ONLY_UNSIGNED_MACHINE_NUM_UNROLLED_CIRCUITS,
        >();
        let circuits_setups_refs = circuits_setups.each_ref();
        let inits_and_teardowns_setups = read_setups::<DefaultNonDeterminismSource, 1>();
        verify_full_statement_for_unrolled_circuits::<
            false,
            { inits_and_teardowns_verifier::concrete::size_constants::NUM_AUX_BOUNDARY_VALUES },
        >(
            &circuits_setups_refs,
            recursion_word_only_unsigned_machine_unrolled_circuits_verification_parameters(
                security,
            ),
            (
                &inits_and_teardowns_setups[0],
                inits_and_teardowns_verifier_ptr(security),
            ),
            recursion_layer_circuits_verification_parameters(security),
            security,
        )
    }
}

pub fn verify_base_or_recursion_unrolled_circuits(
    security: verifier_common::SecurityModel,
) -> [u32; 16] {
    // we just branch
    let op_type = DefaultNonDeterminismSource::read_word();
    use crate::definitions::*;
    match op_type {
        OP_VERIFY_BASE_LAYER_IN_UNROLLED_CIRCUITS => verify_unrolled_base_layer(security),
        OP_VERIFY_RECURSIVE_LAYER_IN_UNROLLED_CIRCUITS => verify_unrolled_recursion_layer(security),
        _ => {
            panic!("Unknown op");
        }
    }
}
