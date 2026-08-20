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
/// [87, 23, 10, 7, 5] -> [21, 17, 9, 5, 4]. Purpose: make proofs of the
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
                whir_queries_schedule: vec![87, 11, 7, 6, 5],
                whir_steps_lde_factors: vec![256, 8192, 32768, 524288],
                whir_pow_schedule: vec![28, 27, 25, 25, 21],
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
                whir_queries_schedule: vec![87, 15, 8, 6, 5],
                whir_steps_lde_factors: vec![64, 2048, 32768, 524288],
                whir_pow_schedule: vec![28, 25, 27, 25, 21],
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
                whir_queries_schedule: vec![87, 23, 10, 7, 5],
                whir_steps_lde_factors: vec![16, 512, 16384, 524288],
                whir_pow_schedule: vec![28, 24, 25, 19, 21],
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
                whir_queries_schedule: vec![87, 23, 10, 7, 5, 5],
                whir_steps_lde_factors: vec![16, 512, 16384, 524288, 524288],
                whir_pow_schedule: vec![28, 24, 25, 19, 21, 21],
            },
        },
        a @ _ => {
            unimplemented!("not yet computed for 2^{} size", a);
        }
    }
}
