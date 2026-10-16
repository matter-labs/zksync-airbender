use crate::definitions::*;
use crate::gkr::whir::proximity_testing_modes::{PessimisticConjectureMode, ProximityTestingMode};
use std::sync::LazyLock;

use super::*;

pub fn config_for_security_level_under_pessimistic_conjecture(
    trace_len_log_2: usize,
    level: SecurityLevel,
) -> ProverConfig {
    match level {
        SecurityLevel::Sec100 => config_for_100_bits_under_pessimistic_conjecture(trace_len_log_2),
    }
}

/// The PoW ceiling of the L1 feeder configuration: no grind in the WHIR
/// schedule (nor the lookup, batched-proximity or external-challenge PoWs of
/// the feeder proofs) exceeds it; the security is filled with queries.
pub const L1_FEEDER_MAX_POW_BITS: u32 = 25;

/// The per-round queries for `pow_bits`: each round gets the pessimistic
/// conjecture's query count for the security its PoW leaves, at the rate of
/// its oracle (`base_lde_factor`, then `whir_steps_lde_factors`).
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

const L1_FEEDER_BASE_LDE_FACTOR: usize = 16;
const L1_FEEDER_WHIR_STEPS_LDE_FACTORS: [usize; 4] = [32, 1024, 32768, 1048576];

/// The per-round PoW bits of the L1 feeder configuration, rounds 0..5 at
/// rates 2^-4 / 2^-5 / 2^-10 / 2^-15 / 2^-20. Every round's PoW is the
/// smallest that satisfies `6 * pow + 5 * queries * rate_bits >= 600` with
/// its queries, and none exceeds [`L1_FEEDER_MAX_POW_BITS`]; both are
/// asserted by `l1_feeder_22_shape_and_security`.
pub const L1_FEEDER_POW_BITS: [u32; 5] = [24, 25, 25, 25, 17];

/// The per-round (queries, PoW bits) of the L1 feeder configuration, in ONE
/// place so a tuple is swapped as a unit: the queries are derived from
/// [`L1_FEEDER_POW_BITS`] and the round rates; pinned by
/// `l1_feeder_22_rounds_are_pinned`.
pub static L1_FEEDER_QUERIES_AND_POW: LazyLock<[(usize, u32); 5]> = LazyLock::new(|| {
    queries_and_pow_under_pessimistic_conjecture(
        SecurityLevel::Sec100,
        L1_FEEDER_BASE_LDE_FACTOR,
        &L1_FEEDER_WHIR_STEPS_LDE_FACTORS,
        L1_FEEDER_POW_BITS,
    )
});

/// The "L1 feeder" configuration for the 2^22 unified circuit: base LDE 16
/// (2^22 x 16 = 2^26) and every intermediate oracle domain at 2^26 too
/// (ladder [32, 1024, 32768, 1048576] for the post-fold poly sizes
/// [2^21, 2^16, 2^11, 2^6]); the schedule stops at the 2^3 polynomial
/// (plain-text tail). Cap 16 is forced at LDE 16 (coset commit cap <= LDE,
/// memory-cap split cap >= LDE). The queries and PoW of every round are
/// [`L1_FEEDER_QUERIES_AND_POW`]. Purpose: make proofs of every feeder
/// layer cheap to VERIFY so a layer verifying two 2^22 chunks fits one
/// 2^22 chunk and the last layer's verification fits the L1 (Proth120)
/// wrapper's 2^21 unified circuit; prove these layers with the RS/tree
/// RECOMPUTATION storage policy.
pub fn l1_feeder_config_for_2_22() -> ProverConfig {
    const L1_FEEDER_TRACE_LEN_LOG2: usize = 22;
    const L1_FEEDER_CAP_SIZE: usize = 16;
    let whir_queries_schedule = L1_FEEDER_QUERIES_AND_POW
        .iter()
        .map(|(queries, _)| *queries)
        .collect();
    let whir_pow_schedule = L1_FEEDER_QUERIES_AND_POW
        .iter()
        .map(|(_, pow)| *pow)
        .collect();
    ProverConfig {
        trace_len_log2: L1_FEEDER_TRACE_LEN_LOG2,
        same_size_sumcheck_schedule: crate::gkr::prover_config::windowed_same_size_schedule(
            L1_FEEDER_TRACE_LEN_LOG2,
        ),
        dimension_reducing_sumcheck_schedule: Default::default(),
        lde_factor: L1_FEEDER_BASE_LDE_FACTOR,
        cap_size: L1_FEEDER_CAP_SIZE,
        base_oracles_values_per_leaf: 2,
        sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
        security_level: SecurityLevel::Sec100,
        whir_schedule: WhirSchedule {
            base_lde_factor: L1_FEEDER_BASE_LDE_FACTOR,
            cap_size: L1_FEEDER_CAP_SIZE,
            // Total fold 19: the WHIR run STOPS at the 2^3 polynomial and
            // ships its 8 monomial coefficients in plain text.
            whir_steps_schedule: vec![1, 5, 5, 5, 3],
            whir_queries_schedule,
            // every oracle domain = 2^26
            whir_steps_lde_factors: L1_FEEDER_WHIR_STEPS_LDE_FACTORS.to_vec(),
            whir_pow_schedule,
        },
    }
}

pub fn config_for_100_bits_under_pessimistic_conjecture(trace_len_log_2: usize) -> ProverConfig {
    match trace_len_log_2 {
        20 => ProverConfig {
            trace_len_log2: trace_len_log_2,
            same_size_sumcheck_schedule: crate::gkr::prover_config::windowed_same_size_schedule(
                trace_len_log_2,
            ),
            dimension_reducing_sumcheck_schedule: Default::default(),
            lde_factor: DEFAULT_LDE_FACTOR,
            cap_size: DEFAULT_CAP_SIZE,
            base_oracles_values_per_leaf: 2,
            sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            security_level: SecurityLevel::Sec100,
            whir_schedule: WhirSchedule {
                base_lde_factor: DEFAULT_LDE_FACTOR,
                cap_size: DEFAULT_CAP_SIZE,
                whir_steps_schedule: vec![1, 5, 5, 4, 4],
                whir_queries_schedule: vec![89, 11, 7, 6, 5],
                whir_steps_lde_factors: vec![256, 8192, 32768, 524288],
                whir_pow_schedule: vec![26, 27, 25, 25, 21],
            },
        },
        21 => ProverConfig {
            trace_len_log2: trace_len_log_2,
            same_size_sumcheck_schedule: crate::gkr::prover_config::windowed_same_size_schedule(
                trace_len_log_2,
            ),
            dimension_reducing_sumcheck_schedule: Default::default(),
            lde_factor: DEFAULT_LDE_FACTOR,
            cap_size: DEFAULT_CAP_SIZE,
            base_oracles_values_per_leaf: 2,
            sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            security_level: SecurityLevel::Sec100,
            whir_schedule: WhirSchedule {
                base_lde_factor: DEFAULT_LDE_FACTOR,
                cap_size: DEFAULT_CAP_SIZE,
                whir_steps_schedule: vec![1, 5, 5, 5, 4],
                whir_queries_schedule: vec![89, 15, 8, 6, 5],
                whir_steps_lde_factors: vec![64, 2048, 32768, 524288],
                whir_pow_schedule: vec![26, 25, 27, 25, 21],
            },
        },
        22 => ProverConfig {
            trace_len_log2: trace_len_log_2,
            same_size_sumcheck_schedule: crate::gkr::prover_config::windowed_same_size_schedule(
                trace_len_log_2,
            ),
            dimension_reducing_sumcheck_schedule: Default::default(),
            lde_factor: DEFAULT_LDE_FACTOR,
            cap_size: DEFAULT_CAP_SIZE,
            base_oracles_values_per_leaf: 2,
            sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            security_level: SecurityLevel::Sec100,
            whir_schedule: WhirSchedule {
                base_lde_factor: DEFAULT_LDE_FACTOR,
                cap_size: DEFAULT_CAP_SIZE,
                whir_steps_schedule: vec![1, 5, 5, 5, 5],
                whir_queries_schedule: vec![89, 15, 8, 6, 5],
                whir_steps_lde_factors: vec![64, 2048, 32768, 524288],
                whir_pow_schedule: vec![26, 25, 27, 25, 21],
            },
        },
        23 => ProverConfig {
            trace_len_log2: trace_len_log_2,
            same_size_sumcheck_schedule: crate::gkr::prover_config::windowed_same_size_schedule(
                trace_len_log_2,
            ),
            dimension_reducing_sumcheck_schedule: Default::default(),
            lde_factor: DEFAULT_LDE_FACTOR,
            cap_size: DEFAULT_CAP_SIZE,
            base_oracles_values_per_leaf: 2,
            sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            security_level: SecurityLevel::Sec100,
            whir_schedule: WhirSchedule {
                base_lde_factor: DEFAULT_LDE_FACTOR,
                cap_size: DEFAULT_CAP_SIZE,
                // Stops at the 2^3 polynomial (plain-text tail): the former
                // sixth round folded 2^3 -> 2^1 through ANOTHER committed
                // oracle — an LDE of a degree-8 polynomial, below the
                // 2^DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2 floor now enforced by
                // `ProverConfig::validate_for_whir_message_size`.
                whir_steps_schedule: vec![1, 5, 5, 5, 4],
                whir_queries_schedule: vec![89, 23, 10, 7, 5],
                whir_steps_lde_factors: vec![16, 512, 16384, 524288],
                whir_pow_schedule: vec![26, 24, 25, 19, 21],
            },
        },
        24 => ProverConfig {
            trace_len_log2: trace_len_log_2,
            same_size_sumcheck_schedule: crate::gkr::prover_config::windowed_same_size_schedule(
                trace_len_log_2,
            ),
            dimension_reducing_sumcheck_schedule: Default::default(),
            lde_factor: DEFAULT_LDE_FACTOR,
            cap_size: DEFAULT_CAP_SIZE,
            base_oracles_values_per_leaf: 2,
            sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            security_level: SecurityLevel::Sec100,
            whir_schedule: WhirSchedule {
                base_lde_factor: DEFAULT_LDE_FACTOR,
                cap_size: DEFAULT_CAP_SIZE,
                whir_steps_schedule: vec![1, 5, 5, 5, 4, 3],
                whir_queries_schedule: vec![89, 23, 10, 7, 5, 5],
                whir_steps_lde_factors: vec![16, 512, 16384, 524288, 524288],
                whir_pow_schedule: vec![26, 24, 25, 19, 21, 21],
            },
        },
        a => {
            unimplemented!("not yet computed for 2^{} size", a);
        }
    }
}

/// The 2^21 Proth120 L1 wrap over the 512 KiB wrap ROM: a 2^21 base trace
/// packed by [`PACK_LOG2`](l1_wrap_2p21::PACK_LOG2) into the
/// `message_log2 = 24` WHIR input, base LDE 128, every oracle on a 2^31
/// codeword.
pub mod l1_wrap_2p21 {
    use super::*;

    pub const TRACE_LEN_LOG2: usize = 21;
    pub const PACK_LOG2: usize = 3;
    pub const EXPLICIT_OUTPUT_LOG2: usize = 2;
    pub const EXTERNAL_CHALLENGES_POW_BITS: u32 = 20;
    /// No WHIR round grinds above it.
    pub const MAX_POW_BITS: u32 = 30;

    const BASE_LDE_FACTOR: usize = 1 << 7;
    const WHIR_STEPS_LDE_FACTORS: [usize; 4] = [1 << 8, 1 << 12, 1 << 16, 1 << 20];

    /// The per-round PoW bits, rounds 0..5 at rates 2^-7 / 2^-8 / 2^-12 /
    /// 2^-16 / 2^-20. Every round satisfies
    /// `6 * pow + 5 * queries * rate_bits >= 600` at the least PoW that
    /// does; asserted by `l1_wrap_2p21_shape_and_security`.
    pub const POW_BITS: [u32; 5] = [30, 27, 30, 20, 17];

    /// The per-round (queries, PoW bits): the queries are derived from
    /// [`POW_BITS`] and the round rates; pinned by
    /// `l1_wrap_2p21_rounds_are_pinned`.
    pub static QUERIES_AND_POW: LazyLock<[(usize, u32); 5]> =
        LazyLock::new(|| queries_and_pow(SecurityLevel::Sec100));

    fn queries_and_pow(level: SecurityLevel) -> [(usize, u32); 5] {
        queries_and_pow_under_pessimistic_conjecture(
            level,
            BASE_LDE_FACTOR,
            &WHIR_STEPS_LDE_FACTORS,
            POW_BITS,
        )
    }

    pub fn packed_prover_config(level: SecurityLevel) -> ProverConfig {
        const CAP_SIZE: usize = 8;
        let queries_and_pow = queries_and_pow(level);
        ProverConfig {
            trace_len_log2: TRACE_LEN_LOG2,
            same_size_sumcheck_schedule: windowed_same_size_schedule(TRACE_LEN_LOG2),
            dimension_reducing_sumcheck_schedule: Default::default(),
            lde_factor: BASE_LDE_FACTOR,
            cap_size: CAP_SIZE,
            base_oracles_values_per_leaf: 1 << 1,
            sumcheck_explicit_output_size_log_2: EXPLICIT_OUTPUT_LOG2,
            security_level: level,
            whir_schedule: WhirSchedule {
                base_lde_factor: BASE_LDE_FACTOR,
                cap_size: CAP_SIZE,
                whir_steps_schedule: vec![1, 4, 4, 4, 4],
                whir_queries_schedule: queries_and_pow.iter().map(|(q, _)| *q).collect(),
                whir_steps_lde_factors: WHIR_STEPS_LDE_FACTORS.to_vec(),
                whir_pow_schedule: queries_and_pow.iter().map(|(_, p)| *p).collect(),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr::whir::proximity_testing_modes::{
        PessimisticConjectureMode, ProximityTestingMode,
    };

    fn assert_every_round_preserves_security_margin(config: &ProverConfig) {
        let schedule = &config.whir_schedule;
        let security_bits = config.security_level.security_bits() as u32;
        assert_eq!(
            schedule.whir_queries_schedule.len(),
            schedule.whir_pow_schedule.len()
        );
        assert_eq!(
            schedule.whir_queries_schedule.len(),
            schedule.whir_steps_lde_factors.len() + 1
        );
        let rates = std::iter::once(schedule.base_lde_factor)
            .chain(schedule.whir_steps_lde_factors.iter().copied())
            .map(|lde_factor| lde_factor.trailing_zeros());
        for (round, ((&queries, &pow), rate_bits)) in schedule
            .whir_queries_schedule
            .iter()
            .zip(&schedule.whir_pow_schedule)
            .zip(rates)
            .enumerate()
        {
            let queries = queries as u32;
            assert!(
                6 * pow + 5 * queries * rate_bits >= 6 * security_bits,
                "round {round}: {queries} queries at rate 2^-{rate_bits} with {pow} PoW bits"
            );
            assert!(
                queries
                    >= PessimisticConjectureMode
                        .num_queries_for_rate_and_bits_of_security(security_bits - pow, rate_bits)
            );
        }
    }

    #[test]
    fn standard_and_l1_rounds_preserve_security_margin() {
        for trace_log2 in 20..=24 {
            let config = config_for_100_bits_under_pessimistic_conjecture(trace_log2);
            let schedule = &config.whir_schedule;
            assert_eq!(
                (
                    schedule.whir_pow_schedule[0],
                    schedule.whir_queries_schedule[0]
                ),
                (26, 89)
            );
            assert_every_round_preserves_security_margin(&config);
        }
        assert_every_round_preserves_security_margin(&l1_feeder_config_for_2_22());
        assert_every_round_preserves_security_margin(&l1_wrap_2p21::packed_prover_config(
            SecurityLevel::Sec100,
        ));
    }

    #[test]
    fn l1_wrap_2p21_shape_and_security() {
        use l1_wrap_2p21::*;
        let config = packed_prover_config(SecurityLevel::Sec100);
        let message_log2 = TRACE_LEN_LOG2 + PACK_LOG2;
        assert_eq!(config.trace_len_log2, 21);
        assert_eq!(message_log2, 24);
        assert_eq!(
            config.same_size_sumcheck_schedule,
            windowed_same_size_schedule(21)
        );
        assert_eq!(config.lde_factor, 128);
        assert_eq!(config.cap_size, 8);
        assert_eq!(config.base_oracles_values_per_leaf, 2);
        assert_eq!(config.sumcheck_explicit_output_size_log_2, 2);
        config.validate_for_whir_message_size(message_log2);
        assert!(EXTERNAL_CHALLENGES_POW_BITS <= 25);

        let schedule = &config.whir_schedule;
        assert_eq!(schedule.whir_steps_schedule, vec![1, 4, 4, 4, 4]);
        assert_eq!(
            schedule.whir_steps_lde_factors,
            vec![1 << 8, 1 << 12, 1 << 16, 1 << 20]
        );
        for (round, (queries, pow)) in QUERIES_AND_POW.iter().enumerate() {
            assert_eq!(schedule.whir_queries_schedule[round], *queries);
            assert_eq!(schedule.whir_pow_schedule[round], *pow);
        }

        // every oracle on the 2^31 codeword; rate = base LDE bits + the
        // preceding folds
        let base_lde_log2 = schedule.base_lde_factor.trailing_zeros() as usize;
        assert_eq!(message_log2 + base_lde_log2, 31);
        let num_rounds = schedule.whir_steps_schedule.len();
        let mut poly_size_log2 = message_log2;
        let mut committed_logs = vec![message_log2];
        let mut rate_bits_per_round = Vec::new();
        let mut oracle_round_queries = 0;
        for round in 0..num_rounds {
            let rate_bits = base_lde_log2 + (message_log2 - poly_size_log2);
            rate_bits_per_round.push(rate_bits as u32);
            poly_size_log2 -= schedule.whir_steps_schedule[round];
            if round + 1 < num_rounds {
                let lde_log2 = schedule.whir_steps_lde_factors[round].trailing_zeros() as usize;
                assert_eq!(poly_size_log2 + lde_log2, 31, "round {round}");
                assert!(schedule.cap_size.trailing_zeros() as usize <= lde_log2);
                committed_logs.push(poly_size_log2);
                oracle_round_queries += schedule.whir_queries_schedule[round];
            }
        }
        assert_eq!(rate_bits_per_round, vec![7, 8, 12, 16, 20]);
        assert_eq!(committed_logs, vec![24, 23, 19, 15, 11]);
        assert!(committed_logs.iter().all(|log| *log >= 8));
        assert_eq!(poly_size_log2, 7);
        assert!(oracle_round_queries <= 256);

        // every round: within the PoW budget, `6 * pow + 5 * queries *
        // rate_bits >= 600`, and one bit less of PoW would break it
        for round in 0..num_rounds {
            let rate_bits = rate_bits_per_round[round];
            let pow = schedule.whir_pow_schedule[round];
            let queries = schedule.whir_queries_schedule[round] as u32;
            assert!(pow <= MAX_POW_BITS, "round {round}: PoW {pow}");
            assert!(
                6 * pow + 5 * queries * rate_bits >= 600,
                "round {round}: 6 * {pow} + 5 * {queries} * {rate_bits} < 600"
            );
            assert!(
                6 * (pow - 1) + 5 * queries * rate_bits < 600,
                "round {round}: PoW {pow} is not minimal for {queries} queries"
            );
        }
    }

    #[test]
    fn l1_feeder_22_shape_and_security() {
        let config = l1_feeder_config_for_2_22();
        assert_eq!(config.trace_len_log2, 22);
        assert_eq!(config.lde_factor, 16);
        assert_eq!(config.cap_size, 16);
        assert_eq!(config.base_oracles_values_per_leaf, 2);
        config.validate_for_whir_message_size(22);

        let schedule = &config.whir_schedule;
        assert_eq!(schedule.whir_steps_schedule, vec![1, 5, 5, 5, 3]);
        assert_eq!(
            schedule.whir_steps_lde_factors,
            vec![32, 1024, 32768, 1048576]
        );
        for (round, (queries, pow)) in L1_FEEDER_QUERIES_AND_POW.iter().enumerate() {
            assert_eq!(schedule.whir_queries_schedule[round], *queries);
            assert_eq!(schedule.whir_pow_schedule[round], *pow);
        }

        // every oracle domain is 2^26
        let mut poly_size_log2 = config.trace_len_log2;
        let mut lde_factors = core::iter::once(schedule.base_lde_factor)
            .chain(schedule.whir_steps_lde_factors.iter().copied());
        let mut rate_bits_per_round = Vec::new();
        for fold_log2 in &schedule.whir_steps_schedule {
            let lde_factor = lde_factors.next().unwrap();
            assert_eq!(poly_size_log2 + lde_factor.trailing_zeros() as usize, 26);
            rate_bits_per_round.push(lde_factor.trailing_zeros());
            poly_size_log2 -= fold_log2;
        }
        assert_eq!(poly_size_log2, 3);
        assert!(lde_factors.next().is_none());
        assert_eq!(rate_bits_per_round, vec![4, 5, 10, 15, 20]);

        // every round: no grind above the ceiling, the first-round security
        // margin of the standard configs, and at least the pessimistic
        // conjecture's query count at its PoW
        for round in 0..5 {
            let rate_bits = rate_bits_per_round[round];
            let pow = schedule.whir_pow_schedule[round];
            let queries = schedule.whir_queries_schedule[round] as u32;
            assert!(pow <= L1_FEEDER_MAX_POW_BITS, "round {round}: PoW {pow}");
            assert!(
                6 * pow + 5 * queries * rate_bits >= 600,
                "round {round}: 6 * {pow} + 5 * {queries} * {rate_bits} < 600"
            );
            assert!(
                pow == 0 || 6 * (pow - 1) + 5 * queries * rate_bits < 600,
                "round {round}: PoW {pow} is not the smallest for {queries} queries"
            );
            assert!(
                queries
                    >= PessimisticConjectureMode
                        .num_queries_for_rate_and_bits_of_security(100 - pow, rate_bits),
                "round {round}"
            );
        }
    }

    /// (rate bits, queries, PoW bits) of every WHIR round.
    fn rounds(config: &ProverConfig) -> Vec<(u32, usize, u32)> {
        let schedule = &config.whir_schedule;
        std::iter::once(schedule.base_lde_factor)
            .chain(schedule.whir_steps_lde_factors.iter().copied())
            .zip(&schedule.whir_queries_schedule)
            .zip(&schedule.whir_pow_schedule)
            .map(|((lde_factor, &queries), &pow)| (lde_factor.trailing_zeros(), queries, pow))
            .collect()
    }

    #[test]
    fn l1_feeder_22_rounds_are_pinned() {
        assert_eq!(
            rounds(&l1_feeder_config_for_2_22()),
            [
                (4, 23, 24),
                (5, 18, 25),
                (10, 9, 25),
                (15, 6, 25),
                (20, 5, 17)
            ]
        );
    }

    #[test]
    fn l1_wrap_2p21_rounds_are_pinned() {
        assert_eq!(
            rounds(&l1_wrap_2p21::packed_prover_config(SecurityLevel::Sec100)),
            [
                (7, 12, 30),
                (8, 11, 27),
                (12, 7, 30),
                (16, 6, 20),
                (20, 5, 17)
            ]
        );
    }
}
