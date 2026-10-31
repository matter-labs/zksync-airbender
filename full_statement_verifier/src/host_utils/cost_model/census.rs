//! Affine census of the next verifier run: per-family cycles and delegation
//! calls, `c0 + Σ n_c · v_c` over the proof's per-circuit counts. Family dims
//! partition total cycles. Standalone i&t is priced per proof; its verification
//! work contributes to the same family and delegation dimensions.
//!
//! Every `CENSUS_TABLES` row is calibrated for the exact guest of its
//! [`FsvDescriptor`]: security level, soundness mode, program, profile and blake
//! mode. Each soundness mode's guests run different verifier code, so each has
//! its own rows; a descriptor without a row is an error, never another row's
//! coefficients. The rows cover the guests the unrolled-to-unified switch
//! prices: the Sec100 standard unrolled base and recursion verifiers, built
//! with `Compression`, in every soundness mode. Regenerate them locally via
//! `emit_census_tables` when a guest changes; see that test for fixture
//! generation. blake2 g-function is unpriced → `UnpricedCircuit`.

use super::{proof_counts, CircuitId, EstimateError};
use crate::program_proof::ProgramProof;
use verifier_common::fsv_binaries::{
    BlakeMode, FsvDescriptor, FsvProgram, SecurityLevel, SoundnessMode,
};

/// The Sec100 pessimistic-conjecture standard-profile guest of `program` built with
/// `mode`: what the legacy `(program, mode)` entry points price.
#[must_use]
pub const fn pessimistic_descriptor(program: FsvProgram, mode: BlakeMode) -> FsvDescriptor {
    FsvDescriptor::new(
        SecurityLevel::Sec100,
        SoundnessMode::PessimisticConjecture,
        program,
        mode,
    )
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
    /// FSV manifest digest of the guest the table was calibrated on.
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

/// [`estimate_verifier_census_for`] the [`pessimistic_descriptor`] of `program` built
/// with `mode`.
pub fn estimate_verifier_census(
    proof: &ProgramProof,
    program: FsvProgram,
    mode: BlakeMode,
) -> Result<Vec<(CircuitId, u64)>, EstimateError> {
    estimate_verifier_census_for(proof, &pessimistic_descriptor(program, mode))
}

/// The table calibrated for exactly `descriptor`. [`EstimateError::UnknownDescriptor`]
/// if no table shares its security level, soundness mode and profile,
/// [`EstimateError::UnknownBinary`] if only its program or blake mode is missing.
pub fn census_table(descriptor: &FsvDescriptor) -> Result<&'static CensusTable, EstimateError> {
    if let Some((_, table)) = CENSUS_TABLES.iter().find(|(d, _)| d == descriptor) {
        return Ok(table);
    }
    let same_guest_family = |d: &FsvDescriptor| {
        (d.security, d.soundness_mode, d.profile)
            == (
                descriptor.security,
                descriptor.soundness_mode,
                descriptor.profile,
            )
    };
    if CENSUS_TABLES.iter().any(|(d, _)| same_guest_family(d)) {
        Err(EstimateError::UnknownBinary {
            program: descriptor.program,
            mode: descriptor.blake,
        })
    } else {
        Err(EstimateError::UnknownDescriptor {
            descriptor: *descriptor,
        })
    }
}

pub(super) fn census_totals(
    proof: &ProgramProof,
    descriptor: &FsvDescriptor,
) -> Result<CensusVec, EstimateError> {
    let table = census_table(descriptor)?;
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
pub static CENSUS_TABLES: &[(FsvDescriptor, CensusTable)] = &[
    (
        FsvDescriptor::new(
            SecurityLevel::Sec100,
            SoundnessMode::PessimisticConjecture,
            FsvProgram::UnrolledBaseLayer,
            BlakeMode::Compression,
        ),
        CensusTable {
            guest_digest: "e7f30eb9b95a6be9c9ee937e14d9c0effd3ea1bf922cb0a5da04837468d4ac90",
            c0: [20342, 5605, 940, 0, 86776, 0, 476, 0, 0, 0],
            per_proof_spread: [171, 197, 170, 0, 92, 0, 0, 0, 0, 0, 540],
            v: &[
                (
                    CircuitId::Riscv(1),
                    [496006, 56449, 37693, 0, 220376, 0, 55797, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(2),
                    [512244, 57660, 37912, 0, 228672, 0, 57078, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(3),
                    [520950, 58490, 38199, 0, 231848, 0, 57141, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(4),
                    [481963, 54064, 35311, 0, 214831, 0, 53326, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(16),
                    [486165, 55855, 37554, 0, 218260, 0, 55797, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(17),
                    [497996, 56655, 38002, 0, 223259, 0, 56455, 0, 0, 0],
                ),
                (
                    CircuitId::InitsAndTeardowns,
                    [354524, 41913, 29969, 0, 156050, 0, 27391, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1991),
                    [792546, 95075, 48349, 0, 371355, 0, 58821, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1994),
                    [697971, 78875, 38410, 0, 345185, 0, 59759, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1995),
                    [691711, 78728, 38161, 0, 339271, 0, 59248, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1996),
                    [613299, 72106, 37597, 0, 296998, 0, 56567, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1997),
                    [560970, 67335, 36785, 0, 272472, 0, 55062, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1998),
                    [575480, 69625, 36132, 0, 282973, 0, 56189, 0, 0, 0],
                ),
            ],
        },
    ),
    (
        FsvDescriptor::new(
            SecurityLevel::Sec100,
            SoundnessMode::PessimisticConjecture,
            FsvProgram::UnrolledRecursionLayer,
            BlakeMode::Compression,
        ),
        CensusTable {
            guest_digest: "406e0afd223c56b01032f48dc7b11ff0d0e1efaeb4a6f8a0baf952938479b3ef",
            c0: [14274, 3417, 670, 0, 46194, 0, 364, 0, 0, 0],
            per_proof_spread: [74, 114, 84, 0, 49, 0, 0, 0, 0, 0, 280],
            v: &[
                (
                    CircuitId::Riscv(1),
                    [496002, 56463, 37701, 0, 220367, 0, 55797, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(2),
                    [512214, 57731, 37971, 0, 228674, 0, 57078, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(3),
                    [521044, 58612, 38338, 0, 231864, 0, 57141, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(16),
                    [486048, 55851, 37567, 0, 218241, 0, 55797, 0, 0, 0],
                ),
                (
                    CircuitId::InitsAndTeardowns,
                    [354372, 41868, 29961, 0, 156020, 0, 27391, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1991),
                    [792533, 95060, 48348, 0, 371349, 0, 58821, 0, 0, 0],
                ),
            ],
        },
    ),
    (
        FsvDescriptor::new(
            SecurityLevel::Sec100,
            SoundnessMode::EthproofsSoundnessCalc,
            FsvProgram::UnrolledBaseLayer,
            BlakeMode::Compression,
        ),
        CensusTable {
            guest_digest: "9fc7694c913564e10d0d00d43555b0aa5eb358222752fbc9d690dec66f688617",
            c0: [20512, 5803, 1332, 0, 86794, 0, 476, 0, 0, 0],
            per_proof_spread: [358, 293, 241, 0, 142, 0, 0, 0, 0, 0, 908],
            v: &[
                (
                    CircuitId::Riscv(1),
                    [823544, 99144, 66335, 0, 360674, 0, 103068, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(2),
                    [853604, 101142, 66813, 0, 374241, 0, 105539, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(3),
                    [865859, 102215, 66949, 0, 378386, 0, 105602, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(4),
                    [772242, 91841, 60374, 0, 345257, 0, 97153, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(16),
                    [806146, 97977, 66099, 0, 355550, 0, 103068, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(17),
                    [825437, 99249, 66694, 0, 364255, 0, 104321, 0, 0, 0],
                ),
                (
                    CircuitId::InitsAndTeardowns,
                    [585841, 72429, 51259, 0, 246811, 0, 48482, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1991),
                    [1180664, 147711, 75591, 0, 565987, 0, 107387, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1994),
                    [1142011, 137001, 66464, 0, 564002, 0, 110705, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1995),
                    [1142187, 137662, 65998, 0, 567755, 0, 110194, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1996),
                    [1012802, 125428, 64886, 0, 495138, 0, 105133, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1997),
                    [929261, 117703, 63665, 0, 460661, 0, 102438, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1998),
                    [967119, 123077, 63774, 0, 478398, 0, 104755, 0, 0, 0],
                ),
            ],
        },
    ),
    (
        FsvDescriptor::new(
            SecurityLevel::Sec100,
            SoundnessMode::EthproofsSoundnessCalc,
            FsvProgram::UnrolledRecursionLayer,
            BlakeMode::Compression,
        ),
        CensusTable {
            guest_digest: "ad956ef9e8ef96f3f7b55e0d518cb16628835bf72bcf6763c6ff80b7b50d40ed",
            c0: [15396, 3902, 921, 0, 46771, 0, 364, 0, 0, 0],
            per_proof_spread: [274, 191, 143, 0, 136, 0, 0, 0, 0, 0, 665],
            v: &[
                (
                    CircuitId::Riscv(1),
                    [823495, 99100, 66362, 0, 360652, 0, 103068, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(2),
                    [853490, 101167, 66824, 0, 374255, 0, 105539, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(3),
                    [865889, 102234, 66883, 0, 378391, 0, 105602, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(16),
                    [805936, 97913, 66060, 0, 355534, 0, 103068, 0, 0, 0],
                ),
                (
                    CircuitId::InitsAndTeardowns,
                    [585730, 72566, 51504, 0, 246770, 0, 48482, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1991),
                    [1180663, 147719, 75619, 0, 565992, 0, 107387, 0, 0, 0],
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
    fn only_calibrated_descriptors_are_priced() {
        use verifier_common::fsv_binaries::FsvProfile;
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
        for &mode in SoundnessMode::ALL {
            let priced = FsvDescriptor::new(
                SecurityLevel::Sec100,
                mode,
                FsvProgram::UnrolledBaseLayer,
                BlakeMode::Compression,
            );
            // Past the lookup: the table is found and the (empty) proof is priced.
            assert_eq!(
                census_totals(&proof, &priced),
                Err(EstimateError::UnexpectedInitsAndTeardowns { found: 0 })
            );
            let feeder = FsvDescriptor {
                profile: FsvProfile::L1Feeder,
                ..priced
            };
            assert_eq!(
                super::super::estimate_verifier_cycles_for(&proof, &feeder),
                Err(EstimateError::UnknownDescriptor { descriptor: feeder })
            );
            assert!(estimate_verifier_census_for(&proof, &feeder).is_err());
            let unified = FsvDescriptor {
                program: FsvProgram::UnifiedRecursionLayer,
                ..priced
            };
            assert_eq!(
                super::super::estimate_verifier_cycles_for(&proof, &unified),
                Err(EstimateError::UnknownBinary {
                    program: FsvProgram::UnifiedRecursionLayer,
                    mode: BlakeMode::Compression
                })
            );
        }
        // The legacy entry points price the pessimistic descriptor.
        assert_eq!(
            super::super::estimate_verifier_cycles(
                &proof,
                FsvProgram::UnrolledBaseLayer,
                BlakeMode::Compression
            ),
            Err(EstimateError::UnexpectedInitsAndTeardowns { found: 0 })
        );
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
            census_table(descriptor).unwrap_or_else(|error| panic!("{error}"));
        }
        assert_eq!(CENSUS_TABLES.len(), switch_guests.len());
        for (descriptor, table) in CENSUS_TABLES {
            let digest = crate::host_utils::fsv_manifest_entry(descriptor)
                .unwrap()
                .digest
                .to_string();
            assert_eq!(
                table.guest_digest, digest,
                "{descriptor}: the table was calibrated on another guest; recalibrate it"
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
                    "{descriptor}: {circuit:?} is unpriced"
                );
            }
            for circuit in &priced {
                assert!(
                    compiled.contains(circuit),
                    "{descriptor}: {circuit:?} is not a circuit of this verifier"
                );
            }
        }
        for (i, (a, _)) in CENSUS_TABLES.iter().enumerate() {
            assert!(
                CENSUS_TABLES[..i].iter().all(|(b, _)| b != a),
                "duplicate table for {a}"
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
