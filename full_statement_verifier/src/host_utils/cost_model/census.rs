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
            guest_digest: "6c5f36e3282f8459599a9e7de4f1042140e7d50228f1fe806fdf1b89b99be530",
            c0: [20467, 5595, 1112, 0, 86841, 0, 476, 0, 0, 0],
            per_proof_spread: [237, 195, 181, 0, 105, 0, 0, 0, 0, 0, 628],
            v: &[
                (
                    CircuitId::Riscv(1),
                    [496003, 56379, 37662, 0, 220374, 0, 55797, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(2),
                    [512243, 57594, 37880, 0, 228671, 0, 57078, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(3),
                    [520926, 58406, 38141, 0, 231843, 0, 57141, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(4),
                    [481961, 54016, 35290, 0, 214829, 0, 53326, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(16),
                    [486152, 55778, 37503, 0, 218258, 0, 55797, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(17),
                    [498005, 56580, 37968, 0, 223267, 0, 56455, 0, 0, 0],
                ),
                (
                    CircuitId::InitsAndTeardowns,
                    [354542, 41841, 29912, 0, 156061, 0, 27391, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1991),
                    [793693, 95268, 48525, 0, 372871, 0, 59003, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1994),
                    [700971, 79081, 38617, 0, 347795, 0, 59941, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1995),
                    [692381, 78907, 38329, 0, 343383, 0, 59430, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1996),
                    [616536, 72302, 37765, 0, 296495, 0, 56749, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1997),
                    [562763, 67546, 36967, 0, 273568, 0, 55244, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1998),
                    [577143, 69854, 36371, 0, 284010, 0, 56371, 0, 0, 0],
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
            guest_digest: "77b3026ca07225fc8b9b98a2d0b51a9b365d8363f2e8ce8ff1597168ce7a91a8",
            c0: [14682, 3493, 694, 0, 46392, 0, 364, 0, 0, 0],
            per_proof_spread: [106, 118, 75, 0, 49, 0, 0, 0, 0, 0, 260],
            v: &[
                (
                    CircuitId::Riscv(1),
                    [495993, 56363, 37624, 0, 220371, 0, 55797, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(2),
                    [512190, 57653, 37924, 0, 228676, 0, 57078, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(3),
                    [520960, 58432, 38237, 0, 231870, 0, 57141, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(16),
                    [486049, 55766, 37537, 0, 218244, 0, 55797, 0, 0, 0],
                ),
                (
                    CircuitId::InitsAndTeardowns,
                    [354230, 41745, 29932, 0, 155935, 0, 27391, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1991),
                    [793692, 95307, 48560, 0, 372844, 0, 59003, 0, 0, 0],
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
            guest_digest: "97b098fb825a3212e4a074e8222c41101124a2c513a76ee5ae2be3c37ddf567d",
            c0: [20263, 5712, 1169, 0, 86523, 0, 476, 0, 0, 0],
            per_proof_spread: [210, 295, 227, 0, 118, 0, 0, 0, 0, 0, 661],
            v: &[
                (
                    CircuitId::Riscv(1),
                    [922376, 110549, 73465, 0, 402744, 0, 111643, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(2),
                    [960279, 112576, 74224, 0, 418046, 0, 114184, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(3),
                    [972066, 113735, 74584, 0, 422253, 0, 114247, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(4),
                    [831056, 98771, 64751, 0, 369687, 0, 102732, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(16),
                    [905312, 109317, 73439, 0, 398616, 0, 111643, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(17),
                    [921888, 110545, 73775, 0, 407479, 0, 112931, 0, 0, 0],
                ),
                (
                    CircuitId::InitsAndTeardowns,
                    [678727, 83180, 58570, 0, 284782, 0, 55517, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1991),
                    [1268166, 157461, 80395, 0, 600696, 0, 114156, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1994),
                    [1229301, 147139, 71644, 0, 600838, 0, 117614, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1995),
                    [1223876, 147718, 71245, 0, 607946, 0, 117103, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1996),
                    [1103103, 135184, 70121, 0, 529928, 0, 111902, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1997),
                    [1018170, 127377, 68955, 0, 491472, 0, 109137, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1998),
                    [1053061, 132753, 68556, 0, 514604, 0, 111524, 0, 0, 0],
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
            guest_digest: "8b16c81e8d3df3afb8c4ea171e364eccfcffb5686ac660d5fa219d97c083c8f9",
            c0: [14577, 3702, 1233, 0, 46274, 0, 364, 0, 0, 0],
            per_proof_spread: [184, 219, 248, 0, 80, 0, 0, 0, 0, 0, 691],
            v: &[
                (
                    CircuitId::Riscv(1),
                    [922305, 110520, 73481, 0, 402702, 0, 111643, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(2),
                    [960120, 112607, 74263, 0, 418040, 0, 114184, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(3),
                    [972097, 113736, 74545, 0, 422254, 0, 114247, 0, 0, 0],
                ),
                (
                    CircuitId::Riscv(16),
                    [905155, 109326, 73464, 0, 398606, 0, 111643, 0, 0, 0],
                ),
                (
                    CircuitId::InitsAndTeardowns,
                    [678541, 83186, 58667, 0, 284740, 0, 55517, 0, 0, 0],
                ),
                (
                    CircuitId::Delegation(1991),
                    [1268140, 157419, 80371, 0, 600697, 0, 114156, 0, 0, 0],
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
