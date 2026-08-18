pub mod table;

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
                "no cost table for {program:?}/{}; recalibrate with \
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

impl std::error::Error for EstimateError {}

pub struct CostTable {
    pub c0: u64,
    pub v: &'static [(CircuitId, u64)],
}

impl CostTable {
    fn lookup(&self, circuit: CircuitId) -> Result<u64, EstimateError> {
        self.v
            .iter()
            .find(|(c, _)| *c == circuit)
            .map(|(_, v)| *v)
            .ok_or(EstimateError::UnpricedCircuit { circuit })
    }
}

#[must_use]
pub fn table_for(program: FsvProgram, mode: BlakeMode) -> Option<&'static CostTable> {
    table::TABLES
        .iter()
        .find(|(p, m, _)| *p == program && *m == mode)
        .map(|(_, _, t)| t)
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
    let table = table_for(program, mode).ok_or(EstimateError::UnknownBinary { program, mode })?;
    estimate_from_table(table, proof)
}

pub fn estimate_from_table(table: &CostTable, proof: &ProgramProof) -> Result<u64, EstimateError> {
    estimate_from_counts(
        table,
        &proof_counts(proof),
        proof.inits_and_teardown_proofs.len(),
    )
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

pub fn estimate_from_counts(
    table: &CostTable,
    counts: &[(CircuitId, usize)],
    inits_and_teardowns: usize,
) -> Result<u64, EstimateError> {
    if inits_and_teardowns != 1 {
        return Err(EstimateError::UnexpectedInitsAndTeardowns {
            found: inits_and_teardowns,
        });
    }
    let mut total = table.c0;
    for (circuit, n) in counts {
        if *n == 0 {
            continue;
        }
        total += table.lookup(*circuit)? * *n as u64;
    }
    Ok(total)
}

pub const BASE_LAYER_RISCV: &[u32] = &[
    common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
    common_constants::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
    common_constants::SHIFT_BINARY_CIRCUIT_FAMILY_IDX as u32,
    common_constants::MUL_DIV_CIRCUIT_FAMILY_IDX as u32,
    common_constants::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
    common_constants::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
];

pub const RECURSION_LAYER_RISCV: &[u32] = &[
    common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32,
    common_constants::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32,
    common_constants::SHIFT_BINARY_CIRCUIT_FAMILY_IDX as u32,
    common_constants::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32,
];

pub const DELEGATION_TYPES: &[u32] = &[
    common_constants::BLAKE2S_DELEGATION_CSR_REGISTER,
    common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    common_constants::KECCAK_SPECIAL5_CSR_REGISTER,
    common_constants::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER,
];

#[must_use]
pub fn riscv_order(program: FsvProgram) -> &'static [u32] {
    match program {
        FsvProgram::UnrolledBaseLayer => BASE_LAYER_RISCV,
        FsvProgram::UnrolledRecursionLayer => RECURSION_LAYER_RISCV,
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

#[cfg(test)]
mod tests {
    use super::*;
    use common_constants::{
        ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX, JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX,
        KECCAK_SPECIAL5_CSR_REGISTER,
    };

    const ADD_SUB: CircuitId = CircuitId::Riscv(ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32);
    const JUMP_BR: CircuitId = CircuitId::Riscv(JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32);
    const KECCAK: CircuitId = CircuitId::Delegation(KECCAK_SPECIAL5_CSR_REGISTER);

    fn test_table() -> CostTable {
        CostTable {
            c0: 1_000,
            v: &[(ADD_SUB, 10), (JUMP_BR, 100), (KECCAK, 1_000)],
        }
    }

    #[test]
    fn sums_counts_times_per_proof_cost() {
        let counts = [(ADD_SUB, 3), (JUMP_BR, 2)];
        assert_eq!(
            estimate_from_counts(&test_table(), &counts, 1).unwrap(),
            1_000 + 30 + 200
        );
    }

    #[test]
    fn absent_circuits_contribute_nothing() {
        let counts = [(ADD_SUB, 1)];
        assert_eq!(
            estimate_from_counts(&test_table(), &counts, 1).unwrap(),
            1_010
        );
    }

    #[test]
    fn zero_count_is_treated_as_absent_not_unpriced() {
        let counts = [(ADD_SUB, 1), (CircuitId::Delegation(9999), 0)];
        assert_eq!(
            estimate_from_counts(&test_table(), &counts, 1).unwrap(),
            1_010
        );
    }

    #[test]
    fn unpriced_circuit_is_a_hard_error() {
        let counts = [(CircuitId::Riscv(4242), 1)];
        assert!(matches!(
            estimate_from_counts(&test_table(), &counts, 1),
            Err(EstimateError::UnpricedCircuit {
                circuit: CircuitId::Riscv(4242)
            })
        ));
    }

    #[test]
    fn inits_and_teardowns_must_be_exactly_one() {
        let counts = [(ADD_SUB, 1)];
        assert!(matches!(
            estimate_from_counts(&test_table(), &counts, 2),
            Err(EstimateError::UnexpectedInitsAndTeardowns { found: 2 })
        ));
        assert!(matches!(
            estimate_from_counts(&test_table(), &counts, 0),
            Err(EstimateError::UnexpectedInitsAndTeardowns { found: 0 })
        ));
    }

    #[test]
    fn delegation_and_riscv_keys_do_not_collide() {
        let table = CostTable {
            c0: 0,
            v: &[(CircuitId::Riscv(7), 5), (CircuitId::Delegation(7), 50)],
        };
        let counts = [(CircuitId::Riscv(7), 1), (CircuitId::Delegation(7), 1)];
        assert_eq!(estimate_from_counts(&table, &counts, 1).unwrap(), 55);
    }
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
        assert_eq!(BASE_LAYER_RISCV, actual.as_slice());
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
        assert_eq!(RECURSION_LAYER_RISCV, actual.as_slice());
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
