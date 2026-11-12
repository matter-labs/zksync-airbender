//! compression and wrap configs, supported only in pessimistic-conjecture mode.
//! Ethproofs support is deferred; see `soundcalc/README.md`.

use super::*;
use crate::gkr::whir::proximity_testing_modes::{PessimisticConjectureMode, ProximityTestingMode};

impl ProverConfigProfile {
    /// The compression and EVM profiles exist only in the pessimistic-conjecture
    /// mode; Ethproofs for them is deferred product scope.
    pub fn assert_supports(self, soundness_mode: SoundnessMode) {
        assert!(
            self == Self::Standard || soundness_mode == SoundnessMode::PessimisticConjecture,
            "{self:?} supports only the pessimistic-conjecture soundness mode, not {soundness_mode:?}"
        );
    }
}

/// PoW ceiling for compression WHIR, lookup, batching and external challenges.
pub const COMPRESSION_MAX_POW_BITS: u32 = 25;

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

/// Each round uses the least PoW satisfying `6 * pow + 5 * queries * rate_bits >= 600`,
/// bounded by [`COMPRESSION_MAX_POW_BITS`].
pub const COMPRESSION_FINAL_POW_BITS: [u32; 5] = [24, 25, 25, 25, 17];

const COMPRESSION_BASE_LDE_FACTOR: usize = 4;

/// The repeatable Compression step follows the same rule and ceiling as [`COMPRESSION_FINAL_POW_BITS`].
pub const COMPRESSION_POW_BITS: [u32; 5] = [25, 25, 25, 25, 17];

/// The cap must equal the base LDE: coset commitment requires cap <= LDE,
/// while splitting the memory cap requires cap >= LDE.
fn compression_config(
    trace_len_log2: usize,
    base_lde_factor: usize,
    whir_steps_schedule: Vec<usize>,
    queries_and_pow: &[(usize, u32); 5],
) -> ProverConfig {
    ProverConfig {
        trace_len_log2,
        same_size_sumcheck_schedule: crate::gkr::prover_config::windowed_same_size_schedule(
            trace_len_log2,
        ),
        commitment_mode: CommitmentMode::MergedMemoryAndWitness,
        dimension_reducing_sumcheck_schedule: Default::default(),
        cap_size: base_lde_factor,
        sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
        security_level: SecurityLevel::Sec100,
        whir_schedule: WhirSchedule::from_legacy_arrays(
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
    }
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
pub fn compression_config_for_2_23() -> ProverConfig {
    compression_config(
        23,
        COMPRESSION_BASE_LDE_FACTOR,
        vec![1, 5, 5, 5, 4],
        &queries_and_pow_under_pessimistic_conjecture(
            SecurityLevel::Sec100,
            COMPRESSION_BASE_LDE_FACTOR,
            &COMPRESSION_FINAL_WHIR_STEPS_LDE_FACTORS,
            COMPRESSION_POW_BITS,
        ),
    )
}

/// L1 wrap over the 512 KiB wrap ROM.
pub mod l1_wrap {
    use super::*;

    pub const TRACE_LEN_LOG2: usize = 21;
    pub const PACK_LOG2: usize = 3;
    pub const EXPLICIT_OUTPUT_LOG2: usize = 2;
    pub const EXTERNAL_CHALLENGES_POW_BITS: u32 = 20;
    /// No WHIR round grinds above it.
    pub const MAX_POW_BITS: u32 = 30;

    const BASE_LDE_FACTOR: usize = 1 << 7;
    const WHIR_STEPS_LDE_FACTORS: [usize; 4] = [1 << 8, 1 << 12, 1 << 16, 1 << 20];

    /// Each round uses the least PoW satisfying `6 * pow + 5 * queries * rate_bits >= 600`.
    pub const POW_BITS: [u32; 5] = [30, 27, 30, 20, 17];

    pub fn packed_prover_config() -> ProverConfig {
        const CAP_SIZE: usize = 8;
        let level = SecurityLevel::Sec100;
        let queries_and_pow = queries_and_pow_under_pessimistic_conjecture(
            level,
            BASE_LDE_FACTOR,
            &WHIR_STEPS_LDE_FACTORS,
            POW_BITS,
        );
        ProverConfig {
            trace_len_log2: TRACE_LEN_LOG2,
            commitment_mode: CommitmentMode::MergedMemoryAndWitness,
            same_size_sumcheck_schedule: windowed_same_size_schedule(TRACE_LEN_LOG2),
            dimension_reducing_sumcheck_schedule: Default::default(),
            cap_size: CAP_SIZE,
            sumcheck_explicit_output_size_log_2: EXPLICIT_OUTPUT_LOG2,
            security_level: level,
            whir_schedule: WhirSchedule::from_legacy_arrays(
                BASE_LDE_FACTOR,
                CAP_SIZE,
                PACK_LOG2,
                &[1, 4, 4, 4, 4],
                &queries_and_pow.iter().map(|(q, _)| *q).collect::<Vec<_>>(),
                &WHIR_STEPS_LDE_FACTORS,
                &queries_and_pow.iter().map(|(_, p)| *p).collect::<Vec<_>>(),
            ),
        }
    }
}
