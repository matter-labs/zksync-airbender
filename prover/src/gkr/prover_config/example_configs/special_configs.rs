//! Hand-tuned configs outside the per-circuit ladders: the L1-feeder schedule
//! of the last BabyBear recursion layer and the EVM-production Proth120
//! config. Both are [`SoundnessMode::PessimisticConjecture`] accountings.
//! Ethproofs L1 feeder/wrap/EVM implementation is deferred product scope;
//! [`ProverConfigProfile::assert_supports`] rejects that combination (see
//! `soundcalc/README.md`).

use super::*;
use crate::gkr::whir::proximity_testing_modes::{PessimisticConjectureMode, ProximityTestingMode};
use std::sync::LazyLock;

impl ProverConfigProfile {
    /// The L1 feeder and EVM profiles exist only in the pessimistic-conjecture
    /// mode; Ethproofs for them is deferred product scope.
    pub fn assert_supports(self, soundness_mode: SoundnessMode) {
        assert!(
            self == Self::Standard || soundness_mode == SoundnessMode::PessimisticConjecture,
            "{self:?} supports only the pessimistic-conjecture soundness mode, not {soundness_mode:?}"
        );
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
/// its queries, and none exceeds [`L1_FEEDER_MAX_POW_BITS`].
pub const L1_FEEDER_POW_BITS: [u32; 5] = [24, 25, 25, 25, 17];

/// The per-round (queries, PoW bits) of the L1 feeder configuration, in ONE
/// place so a tuple is swapped as a unit: the queries are derived from
/// [`L1_FEEDER_POW_BITS`] and the round rates.
pub static L1_FEEDER_QUERIES_AND_POW: LazyLock<[(usize, u32); 5]> = LazyLock::new(|| {
    queries_and_pow_under_pessimistic_conjecture(
        SecurityLevel::Sec100,
        L1_FEEDER_BASE_LDE_FACTOR,
        &L1_FEEDER_WHIR_STEPS_LDE_FACTORS,
        L1_FEEDER_POW_BITS,
    )
});

const L1_FEEDER_A_BASE_LDE_FACTOR: usize = 4;

/// The per-round PoW bits of the 2^23 L1 feeder configuration (profile A),
/// rounds 0..5 at rates 2^-2 / 2^-5 / 2^-10 / 2^-15 / 2^-20, under the same
/// rule and ceiling as [`L1_FEEDER_POW_BITS`].
pub const L1_FEEDER_A_POW_BITS: [u32; 5] = [25, 25, 25, 25, 17];

/// The per-round (queries, PoW bits) of profile A, derived from
/// [`L1_FEEDER_A_POW_BITS`] and the round rates.
pub static L1_FEEDER_A_QUERIES_AND_POW: LazyLock<[(usize, u32); 5]> = LazyLock::new(|| {
    queries_and_pow_under_pessimistic_conjecture(
        SecurityLevel::Sec100,
        L1_FEEDER_A_BASE_LDE_FACTOR,
        &L1_FEEDER_WHIR_STEPS_LDE_FACTORS,
        L1_FEEDER_A_POW_BITS,
    )
});

/// An L1 feeder configuration over the ladder [32, 1024, 32768, 1048576]:
/// cap = base LDE (coset commit cap <= LDE, memory-cap split cap >= LDE), and
/// the folds stop at the 2^3 polynomial, whose 8 monomial coefficients ship
/// in plain text.
fn l1_feeder_config(
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
            &L1_FEEDER_WHIR_STEPS_LDE_FACTORS,
            &queries_and_pow
                .iter()
                .map(|(_, pow)| *pow)
                .collect::<Vec<_>>(),
        ),
    }
}

/// The "L1 feeder" configuration for the 2^22 unified circuit (profile C):
/// base LDE 16 (2^22 x 16 = 2^26) and every intermediate oracle domain at
/// 2^26 too (post-fold poly sizes [2^21, 2^16, 2^11, 2^6]), folds
/// [1, 5, 5, 5, 3]. The queries and PoW of every round are
/// [`L1_FEEDER_QUERIES_AND_POW`]. Purpose: make proofs of every feeder
/// layer cheap to VERIFY so the last layer's verification fits the L1
/// (Proth120) wrapper's 2^21 unified circuit; prove these layers with the
/// RS/tree RECOMPUTATION storage policy.
pub fn l1_feeder_config_for_2_22() -> ProverConfig {
    l1_feeder_config(
        22,
        L1_FEEDER_BASE_LDE_FACTOR,
        vec![1, 5, 5, 5, 3],
        &L1_FEEDER_QUERIES_AND_POW,
    )
}

/// The 2^23 L1 feeder configuration (profile A): base LDE 4 (2^23 x 4 =
/// 2^25), every intermediate oracle domain at 2^27 (post-fold poly sizes
/// [2^22, 2^17, 2^12, 2^7]), folds [1, 5, 5, 5, 4], the queries and PoW of
/// [`L1_FEEDER_A_QUERIES_AND_POW`]. Feeder layers whose verifier program
/// exceeds one 2^22 chunk are proven here: the low base LDE keeps the
/// coset-by-coset proving work small, and a proof still verifies within one
/// 2^22 chunk.
pub fn l1_feeder_a_config_for_2_23() -> ProverConfig {
    l1_feeder_config(
        23,
        L1_FEEDER_A_BASE_LDE_FACTOR,
        vec![1, 5, 5, 5, 4],
        &L1_FEEDER_A_QUERIES_AND_POW,
    )
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
    /// does.
    pub const POW_BITS: [u32; 5] = [30, 27, 30, 20, 17];

    /// The per-round (queries, PoW bits): the queries are derived from
    /// [`POW_BITS`] and the round rates.
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
            schedule.queries_per_round().len(),
            schedule.queries_pow_bits_per_round().len()
        );
        assert_eq!(
            schedule.queries_per_round().len(),
            schedule.intermediate_lde_factors().len() + 1
        );
        let rates = std::iter::once(schedule.base_lde_factor())
            .chain(schedule.intermediate_lde_factors())
            .map(|lde_factor| lde_factor.trailing_zeros());
        for (round, ((&queries, &pow), rate_bits)) in schedule
            .queries_per_round()
            .iter()
            .zip(&schedule.queries_pow_bits_per_round())
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
    fn l1_rounds_preserve_security_margin() {
        for (config, max_pow) in [
            (l1_feeder_config_for_2_22(), L1_FEEDER_MAX_POW_BITS),
            (l1_feeder_a_config_for_2_23(), L1_FEEDER_MAX_POW_BITS),
            (
                l1_wrap_2p21::packed_prover_config(SecurityLevel::Sec100),
                l1_wrap_2p21::MAX_POW_BITS,
            ),
        ] {
            assert_every_round_preserves_security_margin(&config);
            assert!(config
                .whir_schedule
                .queries_pow_bits_per_round()
                .iter()
                .all(|&bits| bits <= max_pow));
        }
    }
}
