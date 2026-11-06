//! Affine census of the next verifier run: per-family cycles and delegation
//! calls, `c0 + Σ n_c · v_c` over the proof's per-circuit counts. Family dims
//! partition total cycles. Standalone i&t is priced per proof; its verification
//! work contributes to the same family and delegation dimensions.
//!
//! Every `CENSUS_TABLES` row is calibrated for the exact guest of its
//! [`FsvDescriptor`]: soundness mode, program, profile and blake
//! mode. Each soundness mode's guests run different verifier code, so each has
//! its own rows; a descriptor without a row panics, never another row's
//! coefficients. The rows cover the guests the unrolled-to-unified switch
//! prices: the Sec100 standard unrolled base and recursion verifiers, built
//! with `Compression`, in every soundness mode. Regenerate them locally via
//! `emit_census_tables` when a guest changes; see that test for fixture
//! generation. blake2 g-function is unpriced → `UnpricedCircuit`.

use super::{proof_counts, CircuitId, EstimateError};
use crate::program_proof::ProgramProof;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProgram, SoundnessMode};

pub const NUM_CENSUS_DIMS: usize = 10;
pub const NUM_FAMILY_DIMS: usize = 6;
pub type CensusVec = [u64; NUM_CENSUS_DIMS];

/// `Riscv(f)` slots: cycles executed in family `f`. `Delegation(csr)` slots:
/// calls made.
pub const CENSUS_DIMS: [CircuitId; NUM_CENSUS_DIMS] = [
    CircuitId::Riscv(common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX as u32),
    CircuitId::Riscv(common_constants::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX as u32),
    CircuitId::Riscv(common_constants::SHIFT_BINARY_CIRCUIT_FAMILY_IDX as u32),
    CircuitId::Riscv(common_constants::MUL_DIV_CIRCUIT_FAMILY_IDX as u32),
    CircuitId::Riscv(common_constants::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX as u32),
    CircuitId::Riscv(common_constants::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX as u32),
    CircuitId::Delegation(common_constants::BLAKE2S_DELEGATION_CSR_REGISTER),
    CircuitId::Delegation(common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER),
    CircuitId::Delegation(common_constants::KECCAK_SPECIAL5_CSR_REGISTER),
    CircuitId::Delegation(common_constants::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER),
];

pub struct CensusTable {
    /// Decoded-ROM digest of the guest the table was calibrated on.
    pub guest_digest: &'static str,
    pub c0: CensusVec,
    /// Frozen empirical max-deviation envelope emitted from calibration proofs:
    /// the ten census dimensions, then total family cycles. Accuracy gates use
    /// this same reference for every acceptance corpus; point estimates ignore it.
    pub per_proof_spread: [u64; NUM_CENSUS_DIMS + 1],
    pub v: &'static [(CircuitId, CensusVec)],
}

impl CensusTable {
    fn lookup(&self, circuit: CircuitId) -> Result<&CensusVec, EstimateError> {
        self.v
            .iter()
            .find(|(c, _)| *c == circuit)
            .map(|(_, v)| v)
            .ok_or(EstimateError::UnpricedCircuit { circuit })
    }
}

/// Census of verifying `proof`, as `(dim, value)` pairs in `CENSUS_DIMS`
/// order. Valid canonical proofs only.
pub fn estimate_verifier_census_for(
    proof: &ProgramProof,
    descriptor: &FsvDescriptor,
) -> Result<Vec<(CircuitId, u64)>, EstimateError> {
    Ok(CENSUS_DIMS
        .into_iter()
        .zip(census_totals(proof, descriptor)?)
        .collect())
}

/// The table calibrated for exactly `descriptor`; panics if none exists.
pub fn census_table(descriptor: &FsvDescriptor) -> &'static CensusTable {
    CENSUS_TABLES
        .iter()
        .find(|(d, _)| d == descriptor)
        .map(|(_, table)| table)
        .unwrap_or_else(|| panic!("no census table for {descriptor:?}"))
}

pub(super) fn census_totals(
    proof: &ProgramProof,
    descriptor: &FsvDescriptor,
) -> Result<CensusVec, EstimateError> {
    let table = census_table(descriptor);
    totals_from_counts(
        table,
        &proof_counts(proof),
        proof.inits_and_teardown_proofs.len(),
    )
}

fn totals_from_counts(
    table: &CensusTable,
    counts: &[(CircuitId, usize)],
    inits_and_teardowns: usize,
) -> Result<CensusVec, EstimateError> {
    if inits_and_teardowns == 0 {
        return Err(EstimateError::UnexpectedInitsAndTeardowns {
            found: inits_and_teardowns,
        });
    }
    let mut total = table.c0;
    for (circuit, n) in counts {
        if *n == 0 {
            continue;
        }
        let row = table.lookup(*circuit)?;
        for (acc, v) in total.iter_mut().zip(row) {
            *acc += v * *n as u64;
        }
    }
    Ok(total)
}

mod pessimistic_conjecture {
    use super::*;
    include!("census_tables/pessimistic_conjecture.rs");
}

mod ethproofs_soundcalc {
    use super::*;
    include!("census_tables/ethproofs_soundcalc.rs");
}

pub static CENSUS_TABLES: &[(FsvDescriptor, CensusTable)] = &{
    let [base, recursion] = pessimistic_conjecture::TABLES;
    let [ethproofs_base, ethproofs_recursion] = ethproofs_soundcalc::TABLES;
    [base, recursion, ethproofs_base, ethproofs_recursion]
};

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

    const fn vec0(v: u64) -> CensusVec {
        let mut out = [0; NUM_CENSUS_DIMS];
        out[0] = v;
        out
    }

    const TEST_ROWS: [(CircuitId, CensusVec); 4] = [
        (ADD_SUB, vec0(10)),
        (JUMP_BR, vec0(100)),
        (KECCAK, vec0(1_000)),
        (CircuitId::InitsAndTeardowns, vec0(200)),
    ];

    fn test_table() -> CensusTable {
        CensusTable {
            guest_digest: "",
            c0: vec0(800),
            per_proof_spread: [0; NUM_CENSUS_DIMS + 1],
            v: &TEST_ROWS,
        }
    }

    fn total0(counts: &[(CircuitId, usize)], inits: usize) -> Result<u64, EstimateError> {
        let mut counts = counts.to_vec();
        counts.push((CircuitId::InitsAndTeardowns, inits));
        totals_from_counts(&test_table(), &counts, inits).map(|t| t[0])
    }

    #[test]
    fn every_switch_guest_has_its_own_table() {
        use verifier_common::fsv_binaries::{FsvProfile, FSV_REGISTRY};
        let switch_guests: Vec<FsvDescriptor> = FSV_REGISTRY
            .iter()
            .map(|entry| entry.descriptor)
            .filter(|d| {
                d.profile == FsvProfile::Standard
                    && matches!(
                        d.program,
                        FsvProgram::UnrolledBaseLayer | FsvProgram::UnrolledRecursionLayer
                    )
            })
            .collect();
        assert_eq!(
            switch_guests.len(),
            2 * SoundnessMode::ALL.len(),
            "one unrolled base and one unrolled recursion guest per soundness mode"
        );
        for descriptor in &switch_guests {
            census_table(descriptor);
        }
        assert_eq!(CENSUS_TABLES.len(), switch_guests.len());
        for (descriptor, table) in CENSUS_TABLES {
            let digest = crate::host_utils::load_fsv_exact(
                crate::host_utils::canonical_fsv_dir(),
                descriptor,
            )
            .digest()
            .to_string();
            assert_eq!(
                table.guest_digest, digest,
                "{descriptor:?}: the table was calibrated on another guest; recalibrate it"
            );
        }
        for (descriptor, table) in CENSUS_TABLES {
            let priced: Vec<CircuitId> = table.v.iter().map(|(circuit, _)| *circuit).collect();
            let compiled = super::super::compiled_circuits(descriptor.program);
            // The recursion verifiers reject every delegation but blake2s.
            let accepted = compiled.iter().filter(|circuit| match circuit {
                CircuitId::Delegation(csr) => {
                    descriptor.program == FsvProgram::UnrolledBaseLayer
                        || *csr == common_constants::BLAKE2S_DELEGATION_CSR_REGISTER
                }
                _ => true,
            });
            for circuit in accepted {
                assert!(
                    priced.contains(circuit),
                    "{descriptor:?}: {circuit:?} is unpriced"
                );
            }
            for circuit in &priced {
                assert!(
                    compiled.contains(circuit),
                    "{descriptor:?}: {circuit:?} is not a circuit of this verifier"
                );
            }
        }
        for (i, (a, _)) in CENSUS_TABLES.iter().enumerate() {
            assert!(
                CENSUS_TABLES[..i].iter().all(|(b, _)| b != a),
                "duplicate table for {a:?}"
            );
        }
    }

    #[test]
    fn sums_counts_times_per_proof_cost() {
        assert_eq!(total0(&[(ADD_SUB, 3), (JUMP_BR, 2)], 1).unwrap(), 1_230);
    }

    #[test]
    fn absent_circuits_contribute_nothing() {
        assert_eq!(total0(&[(ADD_SUB, 1)], 1).unwrap(), 1_010);
    }

    #[test]
    fn zero_count_is_treated_as_absent_not_unpriced() {
        assert_eq!(
            total0(&[(ADD_SUB, 1), (CircuitId::Delegation(9999), 0)], 1).unwrap(),
            1_010
        );
    }

    #[test]
    fn unpriced_circuit_is_a_hard_error() {
        assert!(matches!(
            total0(&[(CircuitId::Riscv(4242), 1)], 1),
            Err(EstimateError::UnpricedCircuit {
                circuit: CircuitId::Riscv(4242)
            })
        ));
    }

    #[test]
    fn inits_and_teardowns_counts_are_priced() {
        assert!(matches!(
            total0(&[(ADD_SUB, 1)], 0),
            Err(EstimateError::UnexpectedInitsAndTeardowns { found: 0 })
        ));
        assert_eq!(total0(&[(ADD_SUB, 1)], 2).unwrap(), 1_210);
        assert_eq!(total0(&[(ADD_SUB, 1)], 8).unwrap(), 2_410);
    }

    #[test]
    fn delegation_and_riscv_keys_do_not_collide() {
        const ROWS: [(CircuitId, CensusVec); 2] = [
            (CircuitId::Riscv(7), vec0(5)),
            (CircuitId::Delegation(7), vec0(50)),
        ];
        let table = CensusTable {
            guest_digest: "",
            c0: vec0(0),
            per_proof_spread: [0; NUM_CENSUS_DIMS + 1],
            v: &ROWS,
        };
        let counts = [(CircuitId::Riscv(7), 1), (CircuitId::Delegation(7), 1)];
        assert_eq!(totals_from_counts(&table, &counts, 1).unwrap()[0], 55);
    }
}
