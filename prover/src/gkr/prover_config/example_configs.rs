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

pub fn config_for_100_bits_under_pessimistic_conjecture(trace_len_log_2: usize) -> ProverConfig {
    match trace_len_log_2 {
        20 => ProverConfig {
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
                whir_steps_schedule: vec![1, 5, 5, 5, 4, 2],
                whir_queries_schedule: vec![87, 23, 10, 7, 5, 5],
                whir_steps_lde_factors: vec![16, 512, 16384, 524288, 524288],
                whir_pow_schedule: vec![28, 24, 25, 19, 21, 21],
            },
        },
        24 => ProverConfig {
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
