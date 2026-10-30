//! Affine census of the next verifier run: per-family cycles and delegation
//! calls, `c0 + Σ n_c · v_c` over the proof's per-circuit counts. Family dims
//! partition total cycles. Standalone i&t is priced per proof; its verification
//! work contributes to the same family and delegation dimensions.
//!
//! The committed table is calibrated for the Sec100 Compression verifier
//! programs. Regenerate it locally via `emit_census_tables` when a guest
//! changes; see that test for fixture generation. blake2 g-function is
//! unpriced → `UnpricedCircuit`.
//!
//! Every `CENSUS_TABLES` row is calibrated for [`CENSUS_CALIBRATION`] and keyed by
//! `(FsvProgram, BlakeMode)` within it. Lookups check a descriptor's security level,
//! soundness mode and profile against [`CENSUS_CALIBRATION`] first, so another level
//! or mode (ethproofs_soundcalc guests run different verifier code) gets
//! `UnknownDescriptor`, never these coefficients. Pricing another one needs its own
//! calibrated table.

use super::{proof_counts, CircuitId, EstimateError};
use crate::program_proof::ProgramProof;
use verifier_common::fsv_binaries::{
    BlakeMode, FsvDescriptor, FsvProfile, FsvProgram, SecurityLevel, SoundnessMode,
};

/// The security level, soundness mode and profile of the guests `CENSUS_TABLES`
/// was calibrated on.
pub const CENSUS_CALIBRATION: (SecurityLevel, SoundnessMode, FsvProfile) = (
    SecurityLevel::Sec100,
    SoundnessMode::PessimisticConjecture,
    FsvProfile::Standard,
);

/// The calibrated descriptor of `program` built with `mode`.
#[must_use]
pub const fn calibrated_descriptor(program: FsvProgram, mode: BlakeMode) -> FsvDescriptor {
    let (security, soundness_mode, profile) = CENSUS_CALIBRATION;
    FsvDescriptor {
        security,
        soundness_mode,
        program,
        profile,
        blake: mode,
    }
}

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

/// [`estimate_verifier_census_for`] the Sec100 pessimistic-conjecture guest of
/// `program` built with `mode`.
pub fn estimate_verifier_census(
    proof: &ProgramProof,
    program: FsvProgram,
    mode: BlakeMode,
) -> Result<Vec<(CircuitId, u64)>, EstimateError> {
    estimate_verifier_census_for(proof, &calibrated_descriptor(program, mode))
}

pub(super) fn census_totals(
    proof: &ProgramProof,
    descriptor: &FsvDescriptor,
) -> Result<CensusVec, EstimateError> {
    if (
        descriptor.security,
        descriptor.soundness_mode,
        descriptor.profile,
    ) != CENSUS_CALIBRATION
    {
        return Err(EstimateError::UnknownDescriptor {
            descriptor: *descriptor,
        });
    }
    let (program, mode) = (descriptor.program, descriptor.blake);
    let table = CENSUS_TABLES
        .iter()
        .find(|(p, m, _)| *p == program && *m == mode)
        .map(|(_, _, t)| t)
        .ok_or(EstimateError::UnknownBinary { program, mode })?;
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

// Generated by `emit_census_tables`.
pub static CENSUS_TABLES: &[(FsvProgram, BlakeMode, CensusTable)] = &[
    (
        FsvProgram::UnrolledBaseLayer,
        BlakeMode::Compression,
        CensusTable {
            c0: [20537, 5419, 1028, 0, 87122, 0, 504, 0, 0, 0],
            per_proof_spread: [123, 205, 235, 0, 0, 0, 0, 0, 0, 0, 500],
            v: &[
                (
                    CircuitId::Riscv(1),
                    [484489, 54574, 35954, 0, 216287, 0, 55552, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(2),
                    [501029, 55801, 36029, 0, 224512, 0, 56833, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(3),
                    [509687, 56653, 36451, 0, 227650, 0, 56896, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(4),
                    [472050, 52457, 33690, 0, 210308, 0, 53144, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(16),
                    [475363, 53995, 35836, 0, 214190, 0, 55552, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(17),
                    [486620, 54800, 36148, 0, 219164, 0, 56210, 0, 0, 0],
                ),
                (
                    CircuitId::InitsAndTeardowns,
                    [342836, 39989, 28035, 0, 148426, 0, 27146, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1991),
                    [1631820, 141519, 48440, 0, 698465, 0, 102662, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1994),
                    [812501, 73824, 36556, 0, 354520, 0, 66255, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1995),
                    [813885, 74283, 36189, 0, 357523, 0, 66367, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1996),
                    [698168, 67765, 35341, 0, 302917, 0, 61194, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1997),
                    [623010, 62777, 34255, 0, 280103, 0, 58443, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1998),
                    [653822, 64498, 34033, 0, 290264, 0, 60816, 0, 0, 0],
                ),
            ],
        },
    ),
    (
        FsvProgram::UnrolledRecursionLayer,
        BlakeMode::Compression,
        CensusTable {
            c0: [17602, 4527, 949, 0, 79288, 0, 364, 0, 0, 0],
            per_proof_spread: [94, 128, 129, 0, 0, 0, 0, 0, 0, 0, 351],
            v: &[
                (
                    CircuitId::Riscv(1),
                    [484461, 54533, 35923, 0, 216287, 0, 55552, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(2),
                    [501016, 55774, 35971, 0, 224512, 0, 56833, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(3),
                    [509706, 56681, 36473, 0, 227650, 0, 56896, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(16),
                    [475371, 54023, 35879, 0, 214190, 0, 55552, 0, 0, 0],
                ),
                (
                    CircuitId::InitsAndTeardowns,
                    [342814, 39973, 28019, 0, 148426, 0, 27146, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1991),
                    [1631804, 141505, 48404, 0, 698466, 0, 102662, 0, 0, 0],
                ),
                // K2 rows: special5's row scaled by layout size, not calibrated
                (
                    CircuitId::Delegation(1997),
                    [805590, 82564, 44879, 0, 335103, 0, 61453, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1996),
                    [969650, 95042, 48588, 0, 404768, 0, 68866, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1998),
                    [837692, 85875, 45178, 0, 354250, 0, 63896, 0, 0, 0],
                ),
            ],
        },
    ),
];

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
    fn only_the_calibrated_descriptor_is_priced() {
        let proof = ProgramProof {
            riscv_proofs: Default::default(),
            compiled_riscv_circuits: Default::default(),
            inits_and_teardown_proofs: vec![],
            inits_and_teardowns_circuit: None,
            delegation_proofs: Default::default(),
            compiled_delegation_circuits: Default::default(),
            register_final_values: vec![],
            final_pc: 0,
            final_timestamp: 0,
            end_params: [0; 8],
            recursion_chain_preimage: None,
            recursion_chain_hash: None,
            pow_challenge: 0,
            num_it_circuits: None,
        };
        let calibrated =
            calibrated_descriptor(FsvProgram::UnrolledBaseLayer, BlakeMode::Compression);
        // Past the guard: the table is found and the (empty) proof is priced.
        assert_eq!(
            census_totals(&proof, &calibrated),
            Err(EstimateError::UnexpectedInitsAndTeardowns { found: 0 })
        );
        let ethproofs = FsvDescriptor {
            soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
            ..calibrated
        };
        let feeder = FsvDescriptor {
            profile: FsvProfile::L1Feeder,
            ..calibrated
        };
        for descriptor in [ethproofs, feeder] {
            assert_eq!(
                census_totals(&proof, &descriptor),
                Err(EstimateError::UnknownDescriptor { descriptor })
            );
            assert_eq!(
                super::super::estimate_verifier_cycles_for(&proof, &descriptor),
                Err(EstimateError::UnknownDescriptor { descriptor })
            );
            assert!(estimate_verifier_census_for(&proof, &descriptor).is_err());
        }
        // The legacy entry points are the calibrated descriptor.
        assert_eq!(
            super::super::estimate_verifier_cycles(
                &proof,
                FsvProgram::UnifiedRecursionLayer,
                BlakeMode::Compression
            ),
            Err(EstimateError::UnknownBinary {
                program: FsvProgram::UnifiedRecursionLayer,
                mode: BlakeMode::Compression
            })
        );
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
            c0: vec0(0),
            per_proof_spread: [0; NUM_CENSUS_DIMS + 1],
            v: &ROWS,
        };
        let counts = [(CircuitId::Riscv(7), 1), (CircuitId::Delegation(7), 1)];
        assert_eq!(totals_from_counts(&table, &counts, 1).unwrap()[0], 55);
    }
}
