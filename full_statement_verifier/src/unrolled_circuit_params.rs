pub const NUM_BASE_LAYER_CIRCUITS: usize = 6;
pub const NUM_RECURSION_LAYER_CIRCUITS: usize = 4;

use crate::prover::definitions::GKRExternalChallenges;
use crate::NonDeterminismSource;
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;

pub fn unrolled_circuit_verifiers_for_base_layer<I: NonDeterminismSource, E: ErrorCreator>() -> [
    (u32, fn(&GKRExternalChallenges<BabyBearField, BabyBearExt4>, &mut I,) -> Result<crate::imports::UnrolledCircuitOutput, E::Error>);
    NUM_BASE_LAYER_CIRCUITS
]{
    [
        (
            common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
            crate::imports::add_sub_lui_auipc_mop_sec_80::verify::<I, E>,
        ),
        (
            common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
            crate::imports::jump_branch_slt_sec_80::verify::<I, E>,
        ),
        (
            common_constants::circuit_families::SHIFT_BINARY_CIRCUIT_FAMILY_IDX as u32,
            crate::imports::shift_binop_sec_80::verify::<I, E>,
        ),
        (
            common_constants::circuit_families::MUL_DIV_CIRCUIT_FAMILY_IDX as u32,
            crate::imports::unsigned_mul_div_sec_80::verify::<I, E>,
        ),
        (
            common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
            crate::imports::mem_word_only_sec_80::verify::<I, E>,
        ),
        (
            common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
            crate::imports::mem_subword_only_sec_80::verify::<I, E>,
        ),
    ]
}

pub fn unrolled_circuit_verifiers_for_recursion_layer<I: NonDeterminismSource, E: ErrorCreator>(
) -> [(
    u32,
    fn(
        &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        &mut I,
    ) -> Result<crate::imports::UnrolledCircuitOutput, E::Error>,
); NUM_RECURSION_LAYER_CIRCUITS] {
    [
        (
            common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
            crate::imports::add_sub_lui_auipc_mop_sec_80::verify::<I, E>,
        ),
        (
            common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
            crate::imports::jump_branch_slt_sec_80::verify::<I, E>,
        ),
        (
            common_constants::circuit_families::SHIFT_BINARY_CIRCUIT_FAMILY_IDX as u32,
            crate::imports::shift_binop_sec_80::verify::<I, E>,
        ),
        (
            common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
            crate::imports::mem_word_only_sec_80::verify::<I, E>,
        ),
    ]
}

pub fn inits_and_teardowns_verifier<I: NonDeterminismSource, E: ErrorCreator>() -> fn(
    &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    &mut I,
) -> Result<
    crate::imports::InitsAndTeardownsCircuitOutput,
    E::Error,
> {
    crate::imports::inits_and_teardowns_sec_80::verify::<I, E>
}
