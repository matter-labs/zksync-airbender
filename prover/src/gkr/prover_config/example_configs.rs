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

/// The "L1 feeder" configuration for the 2^23 unified circuit: identical to
/// the standard [`config_for_100_bits_under_pessimistic_conjecture`] 2^23
/// entry except EVERY oracle — the base one and each intermediate — is
/// committed at the LARGEST LDE factor BabyBear admits: every oracle domain
/// (poly_size x lde_factor) is pinned at 2^27, the field's full two-adicity
/// (a larger domain does not exist — `BabyBearField::TWO_ADICITY = 27`; a
/// uniform x8 ladder was tried first and produced invalid 2^29 domains).
/// Base 2 -> 16 (2^23 x 16 = 2^27); intermediate ladder
/// [16, 512, 16384, 524288] -> [32, 1024, 32768, 1048576] for the post-fold
/// poly sizes [2^22, 2^17, 2^12, 2^7]; the schedule stops at the 2^3
/// polynomial (plain-text tail). Under [`PessimisticConjectureMode`]
/// accounting (`queries = ceil(1.2 * floor((100 - pow) / rate_bits))`, which
/// reproduces each committed schedule) with per-round PoW pushed to the next
/// query-count boundary (grinds capped at 2^30), the query ladder drops
/// [89, 23, 10, 7, 5] -> [21, 17, 9, 5, 4]. Purpose: make proofs of the
/// LAST BabyBear recursion layer(s) maximally cheap to VERIFY (fewer Merkle
/// paths + leaf hashes in every round) so the verification run fits the L1
/// (Proth120) wrapper's 2^22-cycle unified circuit; the LDE prover overhead
/// is paid only on those final small layers (prove such layers with the
/// RS/tree RECOMPUTATION storage policy — the materialized codewords no
/// longer fit in memory).
///
/// [`PessimisticConjectureMode`]: crate::gkr::whir::proximity_testing_modes::PessimisticConjectureMode
pub fn l1_feeder_config_for_2_23() -> ProverConfig {
    const L1_FEEDER_BASE_LDE_FACTOR: usize = 16;
    ProverConfig {
        trace_len_log2: 23,
        pack_log2: 0,
        // the L1 feeder flow commits the single merged memory+witness tree
        commitment_mode: CommitmentMode::MergedMemoryAndWitness,
        same_size_sumcheck_schedule: crate::gkr::prover_config::windowed_same_size_schedule(23),
        dimension_reducing_sumcheck_schedule: Default::default(),
        lde_factor: L1_FEEDER_BASE_LDE_FACTOR,
        cap_size: DEFAULT_CAP_SIZE,
        base_oracles_values_per_leaf: 2,
        sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
        security_level: SecurityLevel::Sec100,
        whir_schedule: WhirSchedule {
            base_lde_factor: L1_FEEDER_BASE_LDE_FACTOR,
            cap_size: DEFAULT_CAP_SIZE,
            // Total fold 20: the WHIR run STOPS at the 2^3 polynomial and
            // ships its 8 monomial coefficients in plain text — no LDE/oracle
            // for the degree-8 tail (the extra fold-by-2 round on a
            // 2^27-domain oracle is dropped entirely).
            whir_steps_schedule: vec![1, 5, 5, 5, 4],
            // rates 2^-4 / 2^-5 / 2^-10 / 2^-15 / 2^-20; per-round PoW pushed
            // to the next query-count boundary (grinds capped at 2^30):
            //   ceil(1.2 * floor(71 / 4))  = 21  (pow 29)
            //   ceil(1.2 * floor(74 / 5))  = 17  (pow 26)
            //   ceil(1.2 * floor(75 / 10)) = 9   (pow 25; no boundary <= 30)
            //   ceil(1.2 * floor(74 / 15)) = 5   (pow 26)
            //   ceil(1.2 * floor(79 / 20)) = 4   (pow 21; no boundary <= 30)
            whir_queries_schedule: vec![21, 17, 9, 5, 4],
            // every oracle domain = 2^27 exactly (BabyBear's two-adicity cap)
            whir_steps_lde_factors: vec![32, 1024, 32768, 1048576],
            whir_pow_schedule: vec![29, 26, 25, 26, 21],
        },
    }
}

pub fn config_for_100_bits_under_pessimistic_conjecture(trace_len_log_2: usize) -> ProverConfig {
    match trace_len_log_2 {
        20 => ProverConfig {
            trace_len_log2: trace_len_log_2,
            pack_log2: 0,
            commitment_mode: CommitmentMode::SeparateMemoryAndWitness,
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
            pack_log2: 0,
            commitment_mode: CommitmentMode::SeparateMemoryAndWitness,
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
            pack_log2: 0,
            commitment_mode: CommitmentMode::SeparateMemoryAndWitness,
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
            pack_log2: 0,
            commitment_mode: CommitmentMode::SeparateMemoryAndWitness,
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
            pack_log2: 0,
            commitment_mode: CommitmentMode::SeparateMemoryAndWitness,
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

/// [`config_for_security_level_under_pessimistic_conjecture`] for a PACKED base
/// commitment (`pack_log2 > 0`): the GKR side (trace length, same-size
/// sumcheck schedule, explicit sumcheck output) is the `trace_len_log2`
/// config's, while the WHIR side (base LDE factor, cap, values per leaf and
/// the whole fold/query/PoW schedule) is the config of the packed message size
/// `trace_len_log2 + pack_log2` — the WHIR run starts from the
/// `2^(trace_len_log2 + pack_log2)`-variate packed polynomials, so its
/// schedule must be the one computed for that size. `pack_log2 == 0` returns
/// the plain config.
pub fn packed_config_for_security_level_under_pessimistic_conjecture(
    trace_len_log2: usize,
    pack_log2: usize,
    level: SecurityLevel,
) -> ProverConfig {
    let mut config = config_for_security_level_under_pessimistic_conjecture(trace_len_log2, level);
    if pack_log2 > 0 {
        let whir_side = config_for_security_level_under_pessimistic_conjecture(
            trace_len_log2 + pack_log2,
            level,
        );
        config.pack_log2 = pack_log2;
        config.lde_factor = whir_side.lde_factor;
        config.cap_size = whir_side.cap_size;
        config.base_oracles_values_per_leaf = whir_side.base_oracles_values_per_leaf;
        config.whir_schedule = whir_side.whir_schedule;
        config.validate_for_whir_message_size(config.whir_message_size_log2());
    }
    config
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
        pack_log2: EVM_PRODUCTION_PACK_LOG2,
        commitment_mode: CommitmentMode::MergedMemoryAndWitness,
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
}
