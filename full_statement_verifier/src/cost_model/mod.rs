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
                "no per-proof cost for {circuit:?}; it was absent from every calibration fixture"
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
/// cost of a malformed proof. Affine in the per-circuit proof counts, with the
/// error budget documented in the design spec.
pub fn estimate_verifier_cycles(
    proof: &ProgramProof,
    program: FsvProgram,
    mode: BlakeMode,
) -> Result<u64, EstimateError> {
    let table = table_for(program, mode).ok_or(EstimateError::UnknownBinary { program, mode })?;
    estimate_from_table(table, proof)
}

pub fn estimate_from_table(
    table: &CostTable,
    proof: &ProgramProof,
) -> Result<u64, EstimateError> {
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
        assert_eq!(estimate_from_counts(&test_table(), &counts, 1).unwrap(), 1_010);
    }

    #[test]
    fn zero_count_is_treated_as_absent_not_unpriced() {
        let counts = [(ADD_SUB, 1), (CircuitId::Delegation(9999), 0)];
        assert_eq!(estimate_from_counts(&test_table(), &counts, 1).unwrap(), 1_010);
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
