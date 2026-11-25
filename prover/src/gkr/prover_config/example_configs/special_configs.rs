//! Compression and L1 wrap configs. See `soundcalc/README.md` for the proven-regime schedules.

use super::*;
use crate::gkr::whir::proximity_testing_modes::{PessimisticConjectureMode, ProximityTestingMode};

fn queries_and_pow_under_pessimistic_conjecture<const ROUNDS: usize>(
    level: SecurityLevel,
    base_lde_factor: usize,
    whir_steps_lde_factors: &[usize],
    pow_bits: [u32; ROUNDS],
) -> [(usize, u32); ROUNDS] {
    assert_eq!(whir_steps_lde_factors.len() + 1, ROUNDS);
    let security_bits = level.security_bits() as u32;
    let lde_factors =
        core::iter::once(base_lde_factor).chain(whir_steps_lde_factors.iter().copied());
    let mut rounds = [(0, 0); ROUNDS];
    for ((round, pow), lde_factor) in rounds.iter_mut().zip(pow_bits).zip(lde_factors) {
        let queries = PessimisticConjectureMode.num_queries_for_rate_and_bits_of_security(
            security_bits - pow,
            lde_factor.trailing_zeros(),
        );
        *round = (queries as usize, pow);
    }
    rounds
}

const COMPRESSION_FINAL_BASE_LDE_FACTOR: usize = 16;
const COMPRESSION_FINAL_WHIR_STEPS_LDE_FACTORS: [usize; 4] = [32, 1024, 32768, 1048576];

/// The deliberate 25-bit PoW cap fixes the query count at the fewest queries
/// that can meet the security target. Each value is the least PoW that meets it.
pub const COMPRESSION_FINAL_POW_BITS: [u32; 5] = [24, 25, 25, 25, 17];

const PESSIMISTIC_COMPRESSION_BASE_LDE_FACTOR: usize = 4;

/// Repeatable Compression uses a deliberate 25-bit PoW cap to fix the query
/// count at the fewest queries that can meet the security target. Each value is
/// the least PoW that meets it.
pub const PESSIMISTIC_COMPRESSION_POW_BITS: [u32; 5] = [25, 25, 25, 25, 17];

/// The cap must equal the base LDE: coset commitment requires cap <= LDE,
/// while splitting the memory cap requires cap >= LDE.
fn compression_config_for_schedule(
    trace_len_log2: usize,
    base_soundness: BaseSoundness,
    whir_schedule: WhirSchedule,
) -> ProverConfig {
    assert_eq!(
        whir_schedule.cap_size,
        whir_schedule.base_round.lde_factor(),
        "a compression config's cap must equal its base LDE"
    );
    ProverConfig {
        trace_len_log2,
        same_size_sumcheck_schedule: crate::gkr::prover_config::windowed_same_size_schedule(
            trace_len_log2,
        ),
        commitment_mode: CommitmentMode::MergedMemoryAndWitness,
        dimension_reducing_sumcheck_schedule: Default::default(),
        cap_size: whir_schedule.cap_size,
        sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
        security_level: SecurityLevel::Sec100,
        base_soundness,
        whir_schedule,
    }
}

fn compression_config(
    trace_len_log2: usize,
    base_lde_factor: usize,
    whir_steps_schedule: Vec<usize>,
    queries_and_pow: &[(usize, u32); 5],
) -> ProverConfig {
    compression_config_for_schedule(
        trace_len_log2,
        BaseSoundness::PessimisticConjecture,
        WhirSchedule::from_legacy_arrays(
            base_lde_factor,
            base_lde_factor,
            0,
            &whir_steps_schedule,
            &queries_and_pow
                .iter()
                .map(|(queries, _)| *queries)
                .collect::<Vec<_>>(),
            &COMPRESSION_FINAL_WHIR_STEPS_LDE_FACTORS,
            &queries_and_pow
                .iter()
                .map(|(_, pow)| *pow)
                .collect::<Vec<_>>(),
        ),
    )
}

/// The terminal CompressionFinal profile.
pub fn compression_final_config_for_2_22() -> ProverConfig {
    compression_config(
        22,
        COMPRESSION_FINAL_BASE_LDE_FACTOR,
        vec![1, 5, 5, 5, 3],
        &queries_and_pow_under_pessimistic_conjecture(
            SecurityLevel::Sec100,
            COMPRESSION_FINAL_BASE_LDE_FACTOR,
            &COMPRESSION_FINAL_WHIR_STEPS_LDE_FACTORS,
            COMPRESSION_FINAL_POW_BITS,
        ),
    )
}

/// Repeatable Compression profile.
pub fn pessimistic_compression_config_for_2_23() -> ProverConfig {
    compression_config(
        23,
        PESSIMISTIC_COMPRESSION_BASE_LDE_FACTOR,
        vec![1, 5, 5, 5, 4],
        &queries_and_pow_under_pessimistic_conjecture(
            SecurityLevel::Sec100,
            PESSIMISTIC_COMPRESSION_BASE_LDE_FACTOR,
            &COMPRESSION_FINAL_WHIR_STEPS_LDE_FACTORS,
            PESSIMISTIC_COMPRESSION_POW_BITS,
        ),
    )
}

/// Repeatable Compression profile under [`SoundnessMode::EthproofsSoundnessCalc`].
pub fn ethproofs_compression_config_for_2_23() -> ProverConfig {
    let entry = &super::ethproofs_soundcalc::COMPRESSION_2_23;
    compression_config_for_schedule(
        23,
        BaseSoundness::Ethproofs(entry.base_analysis.regime),
        entry.schedule(0),
    )
}

/// L1 wrap over the 512 KiB wrap ROM.
pub mod l1_wrap {
    use super::*;
    use std::path::PathBuf;
    use std::sync::OnceLock;

    pub const PESSIMISTIC_TRACE_LEN_LOG2: usize = 21;
    pub const ETHPROOFS_TRACE_LEN_LOG2: usize = 22;
    pub const PACK_LOG2: usize = 3;
    pub const EXPLICIT_OUTPUT_LOG2: usize = 2;
    pub const EXTERNAL_CHALLENGES_POW_BITS: u32 = 20;

    const PESSIMISTIC_BASE_LDE_FACTOR: usize = 1 << 8;
    const PESSIMISTIC_INTERNAL_LDE_FACTORS: [usize; 4] = [1 << 9, 1 << 12, 1 << 17, 1 << 21];

    /// Each round uses the least PoW satisfying `6 * pow + 5 * queries * rate_bits >= 600`.
    pub const PESSIMISTIC_QUERY_POW_BITS: [u32; 5] = [27, 25, 30, 30, 30];

    /// The largest list size each oracle's binding term tolerates at the
    /// configured PoW. These are tolerances, not derived list bounds.
    pub const PESSIMISTIC_LIST_SIZE_CEILINGS: [usize; 5] =
        [1_044_721_774, 673, 5_387, 172_384, 2_758_157];

    /// 100-bit WHIR accounting under the pessimistic conjecture: queries
    /// contribute r/1.2 bits (`PessimisticConjectureMode` in
    /// `whir/proximity_testing_modes.rs`), and the linear proximity-gap charge
    /// in `pow_bits.rs` is applied to each fold. With mu = 37/2^128, every
    /// WHIR RS substep keeps 100 bits for list sizes up to
    /// [`PESSIMISTIC_LIST_SIZE_CEILINGS`]. Nominal-100 shifts have an accepted
    /// deficit below 10^-6 bit. The base commitment has no OOD sample. The GKR
    /// evaluation claims bind it for the WHIR rounds; the conjecture assumes
    /// that the lookup and GKR challenges drawn before them carry no list
    /// factor.
    pub fn pessimistic_packed_prover_config() -> ProverConfig {
        const SCHEDULE_ENV: &str = "AB_PESSIMISTIC_L1_WHIR_SCHEDULE";
        static CONFIG: OnceLock<ProverConfig> = OnceLock::new();
        CONFIG
            .get_or_init(|| {
                let mut config = default_pessimistic_packed_prover_config();
                let Some(path) = std::env::var_os(SCHEDULE_ENV).map(PathBuf::from) else {
                    return config;
                };
                let data = std::fs::read(&path).unwrap_or_else(|error| {
                    panic!("{SCHEDULE_ENV}: could not read {}: {error}", path.display())
                });
                let schedule: WhirSchedule =
                    serde_json::from_slice(&data).unwrap_or_else(|error| {
                        panic!(
                            "{SCHEDULE_ENV}: invalid WHIR schedule in {}: {error}",
                            path.display()
                        )
                    });
                config.cap_size = schedule.cap_size;
                config.whir_schedule = schedule;
                eprintln!(
                    "{SCHEDULE_ENV}: using L1 WHIR schedule from {}",
                    path.display()
                );
                config.validate_for_whir_message_size(config.whir_message_size_log2());
                config
            })
            .clone()
    }

    fn default_pessimistic_packed_prover_config() -> ProverConfig {
        const CAP_SIZE: usize = 8;
        let level = SecurityLevel::Sec100;
        let queries_and_pow = queries_and_pow_under_pessimistic_conjecture(
            level,
            PESSIMISTIC_BASE_LDE_FACTOR,
            &PESSIMISTIC_INTERNAL_LDE_FACTORS,
            PESSIMISTIC_QUERY_POW_BITS,
        );
        ProverConfig {
            trace_len_log2: PESSIMISTIC_TRACE_LEN_LOG2,
            commitment_mode: CommitmentMode::MergedMemoryAndWitness,
            same_size_sumcheck_schedule: windowed_same_size_schedule(PESSIMISTIC_TRACE_LEN_LOG2),
            dimension_reducing_sumcheck_schedule: Default::default(),
            cap_size: CAP_SIZE,
            sumcheck_explicit_output_size_log_2: EXPLICIT_OUTPUT_LOG2,
            security_level: level,
            base_soundness: BaseSoundness::PessimisticConjecture,
            whir_schedule: WhirSchedule {
                cap_size: CAP_SIZE,
                base_round: crate::gkr::prover_config::WhirBaseRoundSchedule {
                    lde_factor_log2: PESSIMISTIC_BASE_LDE_FACTOR.trailing_zeros() as usize,
                    physical_packing_log2: PACK_LOG2,
                    fold_log2: 1,
                    batching_pow_bits: None,
                    folding_pow_bits: 10,
                    num_queries: queries_and_pow[0].0,
                    queries_pow_bits: queries_and_pow[0].1,
                },
                internal_rounds: PESSIMISTIC_INTERNAL_LDE_FACTORS
                    .iter()
                    .enumerate()
                    .map(|(i, lde)| crate::gkr::prover_config::WhirInternalRound {
                        lde_factor_log2: lde.trailing_zeros() as usize,
                        folding_log2: [4, 4, 4, 5][i],
                        num_queries: queries_and_pow[i + 1].0,
                        queries_pow_bits: queries_and_pow[i + 1].1,
                        folding_pow_bits: [10, 9, 10, 10][i],
                        num_ood_samples: 1,
                        ood_pow_bits: [18, 20, 26, 30][i],
                    })
                    .collect(),
            },
        }
    }

    pub fn packed_prover_config_in_mode(mode: SoundnessMode) -> ProverConfig {
        match mode {
            SoundnessMode::PessimisticConjecture => pessimistic_packed_prover_config(),
            SoundnessMode::EthproofsSoundnessCalc => ethproofs_packed_prover_config(),
        }
    }

    /// The Proth120 L1 wrap at 100 bits per PCS term under the
    /// Johnson bound with multiplicity 3. `soundcalc/l1_wrap.py` certifies the
    /// schedule using the maximum challenge point mass `37/2^128`.
    pub fn ethproofs_packed_prover_config() -> ProverConfig {
        use crate::gkr::prover_config::{WhirBaseRoundSchedule, WhirInternalRound};

        const CAP_SIZE: usize = 32;
        const JOHNSON_MULTIPLICITY: u32 = 3;
        ProverConfig {
            trace_len_log2: ETHPROOFS_TRACE_LEN_LOG2,
            commitment_mode: CommitmentMode::MergedMemoryAndWitness,
            same_size_sumcheck_schedule: windowed_same_size_schedule(ETHPROOFS_TRACE_LEN_LOG2),
            dimension_reducing_sumcheck_schedule: Default::default(),
            cap_size: CAP_SIZE,
            sumcheck_explicit_output_size_log_2: EXPLICIT_OUTPUT_LOG2,
            security_level: SecurityLevel::Sec100,
            base_soundness: BaseSoundness::Ethproofs(ProximityRegime::JohnsonBound {
                m: JOHNSON_MULTIPLICITY,
            }),
            whir_schedule: WhirSchedule {
                cap_size: CAP_SIZE,
                base_round: WhirBaseRoundSchedule {
                    lde_factor_log2: 7,
                    physical_packing_log2: PACK_LOG2,
                    fold_log2: 1,
                    batching_pow_bits: Some(32),
                    folding_pow_bits: 28,
                    num_queries: 22,
                    queries_pow_bits: 31,
                },
                internal_rounds: (0..5)
                    .map(|i| WhirInternalRound {
                        lde_factor_log2: [8, 9, 10, 12, 13][i],
                        folding_log2: [1, 4, 4, 4, 4][i],
                        num_queries: [19, 17, 15, 12, 11][i],
                        queries_pow_bits: [29, 28, 29, 31, 31][i],
                        folding_pow_bits: [29, 31, 29, 30, 29][i],
                        num_ood_samples: 1,
                        ood_pow_bits: [12, 12, 9, 7, 4][i],
                    })
                    .collect(),
            },
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::gkr::prover_config::ProofProfile;

        #[test]
        fn ethproofs_l1_wrap_geometry() {
            let config =
                ProofProfile::L1Wrap.prover_config(22, SoundnessMode::EthproofsSoundnessCalc);
            config.validate_for_whir_message_size(25);
            assert!(config.merged_memory_and_witness());
            assert_eq!(config.cap_size, 32);
            assert_eq!(config.sumcheck_explicit_output_size_log_2, 2);
        }
    }
}
