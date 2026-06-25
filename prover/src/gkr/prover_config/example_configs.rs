use crate::definitions::*;

use super::*;

pub fn config_for_security_level_under_pessimistic_conjecture(
    trace_len_log_2: usize,
    level: SecurityLevel,
) -> ProverConfig {
    match level {
        SecurityLevel::Sec80 => config_for_80_bits_under_pessimistic_conjecture(trace_len_log_2),
        SecurityLevel::Sec100 => config_for_100_bits_under_pessimistic_conjecture(trace_len_log_2),
    }
}

pub fn config_for_80_bits_under_pessimistic_conjecture(trace_len_log_2: usize) -> ProverConfig {
    match trace_len_log_2 {
        20 => ProverConfig {
            lde_factor: DEFAULT_LDE_FACTOR,
            cap_size: DEFAULT_CAP_SIZE,
            base_oracles_values_per_leaf: 2,
            lookup_challenges_pow_bits: pow_bits::lookup_challenges_pow_bits(80, trace_len_log_2),
            sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            batched_proximity_check_challenge_pow_bits: pow_bits::batched_proximity_check_pow_bits(
                80,
                trace_len_log_2,
                DEFAULT_LDE_FACTOR.trailing_zeros() as usize,
            ),
            whir_schedule: WhirSchedule {
                base_lde_factor: DEFAULT_LDE_FACTOR,
                cap_size: DEFAULT_CAP_SIZE,
                whir_steps_schedule: vec![1, 5, 5, 4, 4],
                whir_queries_schedule: vec![63, 9, 5, 4, 3],
                whir_steps_lde_factors: vec![256, 8192, 32768, 524288],
                whir_pow_schedule: vec![28, 16, 15, 20, 23],
            },
        },
        22 => ProverConfig {
            lde_factor: DEFAULT_LDE_FACTOR,
            cap_size: DEFAULT_CAP_SIZE,
            base_oracles_values_per_leaf: 2,
            lookup_challenges_pow_bits: pow_bits::lookup_challenges_pow_bits(80, trace_len_log_2),
            sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            batched_proximity_check_challenge_pow_bits: pow_bits::batched_proximity_check_pow_bits(
                80,
                trace_len_log_2,
                DEFAULT_LDE_FACTOR.trailing_zeros() as usize,
            ),
            whir_schedule: WhirSchedule {
                base_lde_factor: DEFAULT_LDE_FACTOR,
                cap_size: DEFAULT_CAP_SIZE,
                whir_steps_schedule: vec![1, 5, 5, 5, 5],
                whir_queries_schedule: vec![63, 11, 6, 4, 3],
                whir_steps_lde_factors: vec![64, 2048, 32768, 524288],
                whir_pow_schedule: vec![28, 20, 14, 20, 23],
            },
        },
        24 => ProverConfig {
            lde_factor: DEFAULT_LDE_FACTOR,
            cap_size: DEFAULT_CAP_SIZE,
            base_oracles_values_per_leaf: 2,
            lookup_challenges_pow_bits: pow_bits::lookup_challenges_pow_bits(80, trace_len_log_2),
            sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            batched_proximity_check_challenge_pow_bits: pow_bits::batched_proximity_check_pow_bits(
                80,
                trace_len_log_2,
                DEFAULT_LDE_FACTOR.trailing_zeros() as usize,
            ),
            whir_schedule: WhirSchedule {
                base_lde_factor: DEFAULT_LDE_FACTOR,
                cap_size: DEFAULT_CAP_SIZE,
                whir_steps_schedule: vec![1, 5, 5, 5, 4, 3],
                whir_queries_schedule: vec![63, 17, 8, 5, 3, 3],
                whir_steps_lde_factors: vec![16, 512, 16384, 524288, 524288],
                whir_pow_schedule: vec![28, 20, 17, 10, 23, 23],
            },
        },
        a @ _ => {
            unimplemented!("not yet computed for 2^{} size", a);
        }
    }
}

fn whir_queries_for_target(
    target_security_bits: u32,
    base_lde_factor: usize,
    whir_steps_lde_factors: &[usize],
    whir_pow_schedule: &[u32],
) -> Vec<usize> {
    use crate::gkr::whir::proximity_testing_modes::{
        PessimisticConjectureMode, ProximityTestingMode,
    };
    let mode = PessimisticConjectureMode;
    core::iter::once(&base_lde_factor)
        .chain(whir_steps_lde_factors.iter())
        .zip(whir_pow_schedule.iter())
        .map(|(lde, pow)| {
            let proximity_bits = target_security_bits - *pow;
            let neg_rate_log_2 = lde.trailing_zeros();
            mode.num_queries_for_rate_and_bits_of_security(proximity_bits, neg_rate_log_2) as usize
        })
        .collect()
}

/// Build a 100-bit config by reusing an 80-bit fold structure (fold steps, LDE
/// factors, per-round query PoW) and recomputing the query counts + the
/// lookup/batched-proximity PoW for the 100-bit target. This is conservative and
/// not cost-optimised (e.g. round-0 query counts grow)
fn config_for_100_bits_from_structure(
    trace_len_log_2: usize,
    whir_steps_schedule: Vec<usize>,
    whir_steps_lde_factors: Vec<usize>,
    whir_pow_schedule: Vec<u32>,
) -> ProverConfig {
    let whir_queries_schedule = whir_queries_for_target(
        100,
        DEFAULT_LDE_FACTOR,
        &whir_steps_lde_factors,
        &whir_pow_schedule,
    );
    ProverConfig {
        lde_factor: DEFAULT_LDE_FACTOR,
        cap_size: DEFAULT_CAP_SIZE,
        base_oracles_values_per_leaf: 2,
        lookup_challenges_pow_bits: pow_bits::lookup_challenges_pow_bits(100, trace_len_log_2),
        sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
        batched_proximity_check_challenge_pow_bits: pow_bits::batched_proximity_check_pow_bits(
            100,
            trace_len_log_2,
            DEFAULT_LDE_FACTOR.trailing_zeros() as usize,
        ),
        whir_schedule: WhirSchedule {
            base_lde_factor: DEFAULT_LDE_FACTOR,
            cap_size: DEFAULT_CAP_SIZE,
            whir_steps_schedule,
            whir_queries_schedule,
            whir_steps_lde_factors,
            whir_pow_schedule,
        },
    }
}

pub fn config_for_100_bits_under_pessimistic_conjecture(trace_len_log_2: usize) -> ProverConfig {
    match trace_len_log_2 {
        20 => config_for_100_bits_from_structure(
            20,
            vec![1, 5, 5, 4, 4],
            vec![256, 8192, 32768, 524288],
            vec![28, 16, 15, 20, 23],
        ),
        22 => config_for_100_bits_from_structure(
            22,
            vec![1, 5, 5, 5, 5],
            vec![64, 2048, 32768, 524288],
            vec![28, 20, 14, 20, 23],
        ),
        24 => config_for_100_bits_from_structure(
            24,
            vec![1, 5, 5, 5, 4, 3],
            vec![16, 512, 16384, 524288, 524288],
            vec![28, 20, 17, 10, 23, 23],
        ),
        a @ _ => {
            unimplemented!("not yet computed for 2^{} size", a);
        }
    }
}
