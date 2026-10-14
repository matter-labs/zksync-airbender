use crate::definitions::*;

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

/// The per-round (queries, PoW bits) of the L1 feeder configuration, rounds
/// 0..5 at rates 2^-5 / 2^-6 / 2^-11 / 2^-16 / 2^-21, in ONE place so a
/// tuple is swapped as a unit. Every round grinds at most
/// [`L1_FEEDER_MAX_POW_BITS`] and satisfies `6 * pow + 5 * queries *
/// rate_bits >= 600`; both are asserted by `l1_feeder_22_shape_and_security`.
pub const L1_FEEDER_QUERIES_AND_POW: [(usize, u32); 5] =
    [(18, 25), (15, 25), (9, 25), (6, 25), (5, 25)];

/// The "L1 feeder" configuration for the 2^22 unified circuit: the standard
/// 2^22 entry of [`config_for_100_bits_under_pessimistic_conjecture`] with
/// EVERY oracle — the base one and each intermediate — committed at the
/// LARGEST LDE factor BabyBear admits: every oracle domain
/// (poly_size x lde_factor) is pinned at 2^27, the field's full two-adicity
/// (`BabyBearField::TWO_ADICITY = 27`). Base 2 -> 32 (2^22 x 32 = 2^27);
/// intermediate ladder [64, 2048, 65536, 2097152] for the post-fold poly
/// sizes [2^21, 2^16, 2^11, 2^6]; the schedule stops at the 2^3 polynomial
/// (plain-text tail). Cap 32 is forced at LDE 32 (coset commit cap <= LDE,
/// memory-cap split cap >= LDE). The queries and PoW of every round are
/// [`L1_FEEDER_QUERIES_AND_POW`]: no grind above [`L1_FEEDER_MAX_POW_BITS`],
/// the rest of the security from queries, each round meeting
/// `6 * pow + 5 * queries * rate_bits >= 600` and the
/// [`PessimisticConjectureMode`] query count at its PoW. Purpose: make
/// proofs of every
/// feeder layer maximally cheap to VERIFY (fewer Merkle paths + leaf hashes
/// in every round) so a layer verifying two 2^22 chunks fits one 2^22 chunk
/// and the last layer's verification fits the L1 (Proth120) wrapper's 2^21
/// unified circuit; the LDE prover overhead is paid only on those small
/// layers (prove them with the RS/tree RECOMPUTATION storage policy — the
/// materialized codewords no longer fit in memory).
///
/// [`PessimisticConjectureMode`]: crate::gkr::whir::proximity_testing_modes::PessimisticConjectureMode
pub fn l1_feeder_config_for_2_22() -> ProverConfig {
    const L1_FEEDER_TRACE_LEN_LOG2: usize = 22;
    const L1_FEEDER_BASE_LDE_FACTOR: usize = 32;
    const L1_FEEDER_CAP_SIZE: usize = 32;
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
            // every oracle domain = 2^27 exactly (BabyBear's two-adicity cap)
            whir_steps_lde_factors: vec![64, 2048, 65536, 2097152],
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

/// Base trace length of the EVM-production packed mode (the single 2^22
/// unified circuit chunk the L1 verifies).
pub const EVM_PRODUCTION_TRACE_LEN_LOG2: usize = 22;
/// Base-layer packing factor of the EVM-production packed mode: the 2^22 base
/// trace becomes a single 2^26-variate multilinear per packed column.
pub const EVM_PRODUCTION_PACK_LOG2: usize = 4;
/// PoW bits gating the self-derived external challenges of the packed mode.
pub const EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS: u32 = 20;

/// The EVM-production prover config: a 2^22 base trace packed by
/// [`EVM_PRODUCTION_PACK_LOG2`] into the `message_log2 = 26` WHIR input — the
/// exact parameters the deployed gkr.sol/whir.sol pair is generated for.
/// Reused by the packed fibonacci fixture test AND the L1 compression /
/// wrap drivers.
pub fn evm_production_packed_prover_config(level: SecurityLevel) -> ProverConfig {
    ProverConfig {
        // circuit trace length; the WHIR message is 2^(22 + pack_log2) = 2^26
        trace_len_log2: EVM_PRODUCTION_TRACE_LEN_LOG2,
        // the EVM verifier (gkr.sol) consumes monomial [c0..c3] rounds;
        // keep these proofs on the windowed schedule (transcript-identical
        // to naive)
        same_size_sumcheck_schedule: windowed_same_size_schedule(EVM_PRODUCTION_TRACE_LEN_LOG2),
        dimension_reducing_sumcheck_schedule: Default::default(),
        lde_factor: 1 << 5, // base LDE factor 32 (base_lde_log2 = 5)
        cap_size: 8,
        // round-0 values-per-leaf = 2^whir_steps_schedule[0] = 2^2
        base_oracles_values_per_leaf: 1 << 2,
        // The GKR dimension-reduction stops at 2^4 and outputs explicit
        // evaluations (this is the GKR-side knob gkr.sol is generated for —
        // NOT the WHIR plain-text tail, which the WHIR schedule determines).
        sumcheck_explicit_output_size_log_2: 4,
        security_level: level,
        whir_schedule: WhirSchedule {
            base_lde_factor: 1 << 5,
            cap_size: 8,
            // 6 rounds ending in a 2^4 plain-text tail; the 6th round's
            // huge-LDE oracle (the 2^8 poly on a 2^31 domain) is cheap with
            // the continuous intermediate-oracle mode.
            whir_steps_schedule: vec![2, 4, 4, 4, 4, 4],
            whir_queries_schedule: vec![17, 12, 8, 6, 5, 4],
            whir_steps_lde_factors: vec![1 << 7, 1 << 11, 1 << 15, 1 << 19, 1 << 23],
            whir_pow_schedule: vec![30, 30, 27, 25, 21, 24],
        },
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
    fn standard_and_evm_rounds_preserve_security_margin() {
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
        assert_every_round_preserves_security_margin(&evm_production_packed_prover_config(
            SecurityLevel::Sec100,
        ));
    }

    #[test]
    fn l1_feeder_22_shape_and_security() {
        let config = l1_feeder_config_for_2_22();
        assert_eq!(config.trace_len_log2, 22);
        assert_eq!(config.lde_factor, 32);
        assert_eq!(config.cap_size, 32);
        assert_eq!(config.base_oracles_values_per_leaf, 2);
        config.validate_for_whir_message_size(22);

        let schedule = &config.whir_schedule;
        assert_eq!(schedule.whir_steps_schedule, vec![1, 5, 5, 5, 3]);
        assert_eq!(
            schedule.whir_steps_lde_factors,
            vec![64, 2048, 65536, 2097152]
        );
        for (round, (queries, pow)) in L1_FEEDER_QUERIES_AND_POW.iter().enumerate() {
            assert_eq!(schedule.whir_queries_schedule[round], *queries);
            assert_eq!(schedule.whir_pow_schedule[round], *pow);
        }

        // every oracle domain sits at BabyBear's two-adicity cap
        let mut poly_size_log2 = config.trace_len_log2;
        let mut lde_factors = core::iter::once(schedule.base_lde_factor)
            .chain(schedule.whir_steps_lde_factors.iter().copied());
        let mut rate_bits_per_round = Vec::new();
        for fold_log2 in &schedule.whir_steps_schedule {
            let lde_factor = lde_factors.next().unwrap();
            assert_eq!(poly_size_log2 + lde_factor.trailing_zeros() as usize, 27);
            rate_bits_per_round.push(lde_factor.trailing_zeros());
            poly_size_log2 -= fold_log2;
        }
        assert_eq!(poly_size_log2, 3);
        assert!(lde_factors.next().is_none());
        assert_eq!(rate_bits_per_round, vec![5, 6, 11, 16, 21]);

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
                queries
                    >= PessimisticConjectureMode
                        .num_queries_for_rate_and_bits_of_security(100 - pow, rate_bits),
                "round {round}"
            );
        }
    }
}
