pub mod census;

use crate::program_proof::ProgramProof;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum CircuitId {
    Riscv(u32),
    Delegation(u32),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EstimateError {
    UnknownBinary {
        program: FsvProgram,
        mode: BlakeMode,
    },
    UnpricedCircuit {
        circuit: CircuitId,
    },
    UnexpectedInitsAndTeardowns {
        found: usize,
    },
}

impl core::fmt::Display for EstimateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnknownBinary { program, mode } => write!(
                f,
                "no census table for {program:?}/{}; recalibrate with \
                 `cargo test -p full_statement_verifier --features host_utils,verifiers \
                 --test cost_model_trace -- --ignored`",
                mode.tag()
            ),
            Self::UnpricedCircuit { circuit } => write!(
                f,
                "no per-proof cost for {circuit:?}; it was absent from every calibration \
                 fixture. Recalibrate against a fixture set that exercises it with \
                 `cargo test -p full_statement_verifier --features host_utils,verifiers \
                 --test cost_model_trace -- --ignored`"
            ),
            Self::UnexpectedInitsAndTeardowns { found } => {
                write!(f, "expected exactly 1 inits/teardowns proof, found {found}")
            }
        }
    }
}

/// Estimated cycles for verifying `proof` with the given fsv binary.
///
/// **Domain: valid canonical proofs only.** The generated verifier returns early
/// on content checks, so this is a scheduling estimate and never a bound on the
/// cost of a malformed proof. Affine in the per-circuit proof counts, and held to
/// 0.05% of the measured cycle count on every calibration fixture by
/// `estimate_matches_measurement_on_every_fixture` in `tests/cost_model_trace.rs`.
pub fn estimate_verifier_cycles(
    proof: &ProgramProof,
    program: FsvProgram,
    mode: BlakeMode,
) -> Result<u64, EstimateError> {
    // The census family dims partition the cycle count (the calibration test
    // `census_family_cycles_sum_to_total` asserts it), so total cycles are the
    // family sum of the same fit.
    let totals = census::census_totals(proof, program, mode)?;
    Ok(totals[..census::NUM_FAMILY_DIMS].iter().sum())
}

#[must_use]
pub fn proof_counts(proof: &ProgramProof) -> Vec<(CircuitId, usize)> {
    proof
        .riscv_proofs
        .iter()
        .map(|(k, v)| (CircuitId::Riscv(*k), v.len()))
        .chain(
            proof
                .delegation_proofs
                .iter()
                .map(|(k, v)| (CircuitId::Delegation(*k), v.len())),
        )
        .collect()
}

pub const DELEGATION_TYPES: &[u32] = &[
    common_constants::BLAKE2S_DELEGATION_CSR_REGISTER,
    common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    common_constants::KECCAK_SPECIAL5_CSR_REGISTER,
    common_constants::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER,
];

#[must_use]
pub fn riscv_order(program: FsvProgram) -> &'static [u32] {
    match program {
        FsvProgram::UnrolledBaseLayer => &[
            common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
            common_constants::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
            common_constants::SHIFT_BINARY_CIRCUIT_FAMILY_IDX as u32,
            common_constants::MUL_DIV_CIRCUIT_FAMILY_IDX as u32,
            common_constants::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
            common_constants::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        ],
        FsvProgram::UnrolledRecursionLayer => &[
            common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
            common_constants::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
            common_constants::SHIFT_BINARY_CIRCUIT_FAMILY_IDX as u32,
            common_constants::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
        ],
        other => panic!("{other:?} is not an unrolled program"),
    }
}

#[must_use]
pub fn compiled_circuits(program: FsvProgram) -> Vec<CircuitId> {
    riscv_order(program)
        .iter()
        .map(|k| CircuitId::Riscv(*k))
        .chain(DELEGATION_TYPES.iter().map(|k| CircuitId::Delegation(*k)))
        .collect()
}

#[cfg(all(test, feature = "verifiers"))]
mod order_tests {
    use super::*;
    use crate::imports;
    use verifier_common::errors::{DebugErrorCreator, ErrorCreator};
    use verifier_common::field::baby_bear::base::BabyBearField;
    use verifier_common::field::baby_bear::ext4::BabyBearExt4;
    use verifier_common::prover::definitions::GKRExternalChallenges;

    type I = std::vec::IntoIter<u32>;
    type E = DebugErrorCreator;

    type DelegVerifier = fn(
        &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        &mut I,
    )
        -> Result<imports::DelegationCircuitOutput, <E as ErrorCreator>::Error>;

    #[test]
    fn base_layer_riscv_order_matches_verifier_list() {
        let actual: Vec<u32> =
            crate::unrolled_circuit_params::unrolled_circuit_verifiers_for_base_layer_sec_80::<I, E>(
            )
            .iter()
            .map(|(k, _)| *k)
            .collect();
        assert_eq!(
            riscv_order(FsvProgram::UnrolledBaseLayer),
            actual.as_slice()
        );
    }

    #[test]
    fn recursion_layer_riscv_order_matches_verifier_list() {
        let actual: Vec<u32> =
            crate::unrolled_circuit_params::unrolled_circuit_verifiers_for_recursion_layer_sec_80::<
                I,
                E,
            >()
            .iter()
            .map(|(k, _)| *k)
            .collect();
        assert_eq!(
            riscv_order(FsvProgram::UnrolledRecursionLayer),
            actual.as_slice()
        );
    }

    #[test]
    fn delegation_order_matches_verifier_functions() {
        let actual = crate::delegation_params::all_delegation_circuit_verifiers_sec_80::<I, E>();
        let expected: [DelegVerifier; 4] = [
            imports::blake2_with_extended_control_sec_80::verify::<I, E>,
            imports::bigint_with_extended_control_sec_80::verify::<I, E>,
            imports::keccak_special5_sec_80::verify::<I, E>,
            imports::blake2_g_function_sec_80::verify::<I, E>,
        ];
        for (i, (a, b)) in actual.iter().zip(expected.iter()).enumerate() {
            assert_eq!(
                *a as usize, *b as usize,
                "delegation verifier {i} out of order"
            );
        }
    }

    #[test]
    fn delegation_metadata_matches_setup_param_order() {
        let actual: Vec<u32> = crate::constants::DELEGATION_CIRCUITS_SETUP_PARAMS
            .iter()
            .map(|p| p.delegation_type)
            .collect();
        assert_eq!(DELEGATION_TYPES, actual.as_slice());
    }
}
