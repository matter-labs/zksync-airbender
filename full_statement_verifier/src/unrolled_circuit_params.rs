//! The unrolled-circuit verifier tables, one module per soundness mode.

pub const NUM_BASE_LAYER_CIRCUITS: usize = 6;
pub const NUM_RECURSION_LAYER_CIRCUITS: usize = 4;

use crate::prover::definitions::GKRExternalChallenges;
use crate::NonDeterminismSource;
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;

/// (circuit family, log2 cycles per circuit, verifier)
pub type UnrolledCircuitVerifier<I, E> = (
    u32,
    u32,
    fn(
        &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        &mut I,
    ) -> Result<crate::imports::UnrolledCircuitOutput, <E as ErrorCreator>::Error>,
);

pub type InitsAndTeardownsVerifier<I, E> =
    fn(
        &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        &mut I,
    ) -> Result<crate::imports::InitsAndTeardownsCircuitOutput, <E as ErrorCreator>::Error>;

macro_rules! unrolled_circuit_tables {
    ($mode:ident) => {
        pub mod $mode {
            use super::*;
            use crate::imports::$mode as imports;

            pub fn unrolled_circuit_verifiers_for_base_layer<
                I: NonDeterminismSource<BabyBearField>,
                E: ErrorCreator,
            >() -> [UnrolledCircuitVerifier<I, E>; NUM_BASE_LAYER_CIRCUITS] {
                [
                    (
                        common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
                        imports::add_sub_lui_auipc_mop::TRACE_LEN_LOG2,
                        imports::add_sub_lui_auipc_mop::verify::<I, E>,
                    ),
                    (
                        common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
                        imports::jump_branch_slt::TRACE_LEN_LOG2,
                        imports::jump_branch_slt::verify::<I, E>,
                    ),
                    (
                        common_constants::circuit_families::SHIFT_BINARY_CIRCUIT_FAMILY_IDX as u32,
                        imports::shift_binop::TRACE_LEN_LOG2,
                        imports::shift_binop::verify::<I, E>,
                    ),
                    (
                        common_constants::circuit_families::MUL_DIV_CIRCUIT_FAMILY_IDX as u32,
                        imports::unsigned_mul_div::TRACE_LEN_LOG2,
                        imports::unsigned_mul_div::verify::<I, E>,
                    ),
                    (
                        common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
                        imports::mem_word_only::TRACE_LEN_LOG2,
                        imports::mem_word_only::verify::<I, E>,
                    ),
                    (
                        common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
                        imports::mem_subword_only::TRACE_LEN_LOG2,
                        imports::mem_subword_only::verify::<I, E>,
                    ),
                ]
            }

            pub fn unrolled_circuit_verifiers_for_recursion_layer<
                I: NonDeterminismSource<BabyBearField>,
                E: ErrorCreator,
            >() -> [UnrolledCircuitVerifier<I, E>; NUM_RECURSION_LAYER_CIRCUITS] {
                [
                    (
                        common_constants::circuit_families::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
                        imports::add_sub_lui_auipc_mop::TRACE_LEN_LOG2,
                        imports::add_sub_lui_auipc_mop::verify::<I, E>,
                    ),
                    (
                        common_constants::circuit_families::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
                        imports::jump_branch_slt::TRACE_LEN_LOG2,
                        imports::jump_branch_slt::verify::<I, E>,
                    ),
                    (
                        common_constants::circuit_families::SHIFT_BINARY_CIRCUIT_FAMILY_IDX as u32,
                        imports::shift_binop::TRACE_LEN_LOG2,
                        imports::shift_binop::verify::<I, E>,
                    ),
                    (
                        common_constants::circuit_families::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
                        imports::mem_word_only::TRACE_LEN_LOG2,
                        imports::mem_word_only::verify::<I, E>,
                    ),
                ]
            }

            pub fn inits_and_teardowns_verifier<
                I: NonDeterminismSource<BabyBearField>,
                E: ErrorCreator,
            >() -> InitsAndTeardownsVerifier<I, E> {
                imports::inits_and_teardowns::verify::<I, E>
            }
        }
    };
}

unrolled_circuit_tables!(pessimistic_conjecture);
unrolled_circuit_tables!(ethproofs_soundcalc);

// The inits/teardowns geometry does not depend on the soundness mode.
const NUM_INIT_WORDS_PER_INIT_TEARDOWN_CIRCUIT: u32 = (1
    << crate::imports::pessimistic_conjecture::inits_and_teardowns::TRACE_LEN_LOG2)
    * (crate::imports::pessimistic_conjecture::inits_and_teardowns::INIT_AND_TEARDOWN_SETS as u32);
const MAX_NUM_INIT_WORDS: u32 = 1 << 30; // initialize 1<<30 of 4-byte words

const _: () = const {
    assert!(MAX_NUM_INIT_WORDS.is_multiple_of(NUM_INIT_WORDS_PER_INIT_TEARDOWN_CIRCUIT));
    assert!(
        crate::imports::ethproofs_soundcalc::inits_and_teardowns::TRACE_LEN_LOG2
            == crate::imports::pessimistic_conjecture::inits_and_teardowns::TRACE_LEN_LOG2
    );
};
pub const MAX_INITS_AND_TEARDOWN_CIRCUITS: u32 =
    MAX_NUM_INIT_WORDS / NUM_INIT_WORDS_PER_INIT_TEARDOWN_CIRCUIT;
pub const TOP_BITS_UPPER_BOUND: u32 = MAX_INITS_AND_TEARDOWN_CIRCUITS
    * (crate::imports::pessimistic_conjecture::inits_and_teardowns::INIT_AND_TEARDOWN_SETS as u32);
