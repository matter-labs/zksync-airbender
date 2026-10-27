//! The WHIR proving schedule: how the committed base columns enter WHIR (the
//! BASE round) and one [`WhirInternalRound`] per committed intermediate
//! oracle.
//!
//! Round numbering: round 0 is the base round — it opens the base oracles
//! (memory / witness / setup trees) and commits intermediate oracle 0 (the
//! batched, possibly folded, polynomial). Internal round `i` (1-based in the
//! transcript, `internal_rounds[i - 1]` here) folds intermediate oracle
//! `i - 1` by its `folding_log2` sumcheck steps, commits the next oracle (or
//! ships the plain-text tail), samples that next oracle out of domain, and
//! queries oracle `i - 1`. Every per-oracle knob (LDE factor, leaf width =
//! the fold applied to it, query count and PoW, folding-challenge PoW, OOD
//! sample count and PoW) therefore lives on the oracle's own
//! [`WhirInternalRound`].

use crate::definitions::BlakeMode;
use serde::{Deserialize, Serialize};

use crate::gkr::whir::proximity_testing_modes::ProximityTestingMode;

/// The base round: the committed base oracles' RS rate, their packing, how
/// they are opened (the round-0 fold) and how many base queries are drawn
/// under how much PoW.
///
/// Physical and virtual packing are independent knobs. `physical_packing_log2`
/// packs every committed set by `2^physical_packing_log2` consecutive
/// columns into one `(trace_len_log2 + physical_packing_log2)`-variate
/// committed column (`0` = unpacked; a short tail group is zero-padded).
/// `fold_log2` is the number of round-0 sumcheck steps, so every base leaf
/// holds the `2^fold_log2`-point fibre of every committed column; `fold_log2
/// = 0` is VIRTUAL packing: one value per committed column per leaf, no
/// round-0 sumcheck, and the batching challenge is read as the `2^k`-ary fold
/// of the virtual `(message + k)`-variate interleaving of the committed
/// columns (`2^k` = the committed column count rounded up) — the batched
/// polynomial itself is committed as intermediate oracle 0 and a base query
/// opens one column per tree whose dot product with the batching powers is
/// the folded value (the ReedWeave / LiftWHIR layout).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct WhirBaseRoundSchedule {
    /// `log2` of the base oracles' LDE factor (the base RS rate is
    /// `2^-lde_factor_log2`), `>= 1`.
    pub lde_factor_log2: usize,
    /// `log2` of the physical base-commitment packing factor (`0` = unpacked).
    pub physical_packing_log2: usize,
    /// Round-0 sumcheck steps = `log2` of the values every base leaf holds per
    /// committed column; `0` = virtual packing.
    pub fold_log2: usize,
    /// PoW bits gating the batching-challenge draw: the batched-proximity PoW
    /// when `fold_log2 > 0`, the initial-folding PoW when `fold_log2 == 0`
    /// (the challenge plays the same role either way: a random linear
    /// combination of the committed columns at the base rate). `None`:
    /// derived from the security level, the message size, the base rate and
    /// the committed column count by
    /// [`pow_bits::batched_proximity_check_pow_bits`](super::pow_bits::batched_proximity_check_pow_bits).
    pub batching_pow_bits: Option<u32>,
    /// PoW bits gating EACH round-0 folding-challenge draw (`0`: plain draws,
    /// no nonces in the proof; irrelevant when `fold_log2 == 0`).
    pub folding_pow_bits: u32,
    /// Round-0 shift queries into the base oracles.
    pub num_queries: usize,
    /// PoW bits gating the round-0 query-index draw.
    pub queries_pow_bits: u32,
}

impl Default for WhirBaseRoundSchedule {
    fn default() -> Self {
        Self {
            lde_factor_log2: 1,
            physical_packing_log2: 0,
            fold_log2: 1,
            batching_pow_bits: None,
            folding_pow_bits: 0,
            num_queries: 1,
            queries_pow_bits: 0,
        }
    }
}

impl WhirBaseRoundSchedule {
    pub fn lde_factor(&self) -> usize {
        1usize << self.lde_factor_log2
    }

    /// Values every base leaf holds per committed column.
    pub fn values_per_leaf(&self) -> usize {
        1usize << self.fold_log2
    }

    /// Whether the base round is the virtual-packing one (`fold_log2 == 0`).
    pub fn is_virtual_packing(&self) -> bool {
        self.fold_log2 == 0
    }

    /// The PoW bits gating the batching challenge (`fold_log2 > 0`) / initial
    /// folding challenge (`fold_log2 == 0`) draw: the configured value, or the
    /// security-level derivation for `num_committed_columns` columns of
    /// `2^message_size_log2` evaluations at this base rate.
    pub fn batching_pow_bits<F: field::PrimeField, E: field::FieldExtension<F>>(
        &self,
        security_bits: usize,
        message_size_log2: usize,
        num_committed_columns: usize,
    ) -> u32 {
        self.batching_pow_bits.unwrap_or_else(|| {
            super::pow_bits::batched_proximity_check_pow_bits::<F, E>(
                security_bits,
                message_size_log2,
                self.lde_factor_log2,
                num_committed_columns,
            )
        })
    }
}

/// One committed intermediate oracle and the round that consumes it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct WhirInternalRound {
    /// `log2` of this oracle's LDE factor, `>= 1`.
    pub lde_factor_log2: usize,
    /// Sumcheck steps folding this oracle's polynomial, `>= 1`; its leaves
    /// hold `2^folding_log2` values.
    pub folding_log2: usize,
    /// Shift queries into this oracle.
    pub num_queries: usize,
    /// PoW bits gating the query-index draw.
    pub queries_pow_bits: u32,
    /// PoW bits gating EACH folding-challenge draw (`0`: plain draws, no
    /// nonces in the proof).
    pub folding_pow_bits: u32,
    /// Out-of-domain samples of this oracle's polynomial, drawn right after
    /// its commitment, `>= 1`.
    pub num_ood_samples: usize,
    /// PoW bits gating the OOD point draw (`0`: a plain draw, no nonce).
    pub ood_pow_bits: u32,
}

impl WhirInternalRound {
    pub fn lde_factor(&self) -> usize {
        1usize << self.lde_factor_log2
    }

    pub fn values_per_leaf(&self) -> usize {
        1usize << self.folding_log2
    }
}

/// The whole WHIR schedule of a config.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[serde(from = "legacy_compat::WhirScheduleRepr")]
pub struct WhirSchedule {
    /// Merkle cap size (top nodes absorbed into the transcript) of EVERY
    /// committed oracle, base and intermediate.
    pub cap_size: usize,
    pub base_round: WhirBaseRoundSchedule,
    pub internal_rounds: Vec<WhirInternalRound>,
}

impl WhirSchedule {
    /// Whether round `round_idx`'s openings are flattened for, and verified
    /// by, a verifier built with `blake` as ONE pruned Merkle multiproof
    /// instead of a path per query (the verifier sorts the queries by tree
    /// index, walks them in that order and hashes every distinct ancestor
    /// once; siblings that are themselves on a queried path come from the
    /// walk, not the proof). The proof structure is the same either way: the
    /// prover opens every query with its full path, and the flattener prunes.
    /// The policy is [`BlakeMode::merkle_multiproofs`].
    pub fn merkle_multiproof_for_round(&self, blake: BlakeMode, round_idx: usize) -> bool {
        blake.merkle_multiproofs(self.queries_per_round()[round_idx], self.cap_size)
    }

    /// Build a schedule from the pre-refactor arrays: the base round is
    /// `(base_lde_factor, steps[0], queries[0], pows[0])` with an explicit
    /// `pack_log2` packing; intermediate oracle `i` is
    /// `(lde_factors[i], steps[i + 1], queries[i + 1], pows[i + 1])` with one
    /// OOD sample and no OOD / folding PoW. Used by the example configs (whose
    /// numbers predate the refactor) and by the legacy JSON decoder.
    pub fn from_legacy_arrays(
        base_lde_factor: usize,
        cap_size: usize,
        pack_log2: usize,
        whir_steps_schedule: &[usize],
        whir_queries_schedule: &[usize],
        whir_steps_lde_factors: &[usize],
        whir_pow_schedule: &[u32],
    ) -> Self {
        let num_rounds = whir_steps_schedule.len();
        assert!(num_rounds >= 1, "empty WHIR schedule");
        assert_eq!(whir_queries_schedule.len(), num_rounds);
        assert_eq!(whir_pow_schedule.len(), num_rounds);
        assert_eq!(whir_steps_lde_factors.len(), num_rounds - 1);
        assert!(base_lde_factor.is_power_of_two());
        let base_round = WhirBaseRoundSchedule {
            lde_factor_log2: base_lde_factor.trailing_zeros() as usize,
            physical_packing_log2: pack_log2,
            fold_log2: whir_steps_schedule[0],
            batching_pow_bits: None,
            folding_pow_bits: 0,
            num_queries: whir_queries_schedule[0],
            queries_pow_bits: whir_pow_schedule[0],
        };
        let internal_rounds = (0..num_rounds - 1)
            .map(|i| {
                let lde_factor = whir_steps_lde_factors[i];
                assert!(lde_factor.is_power_of_two());
                WhirInternalRound {
                    lde_factor_log2: lde_factor.trailing_zeros() as usize,
                    folding_log2: whir_steps_schedule[i + 1],
                    num_queries: whir_queries_schedule[i + 1],
                    queries_pow_bits: whir_pow_schedule[i + 1],
                    folding_pow_bits: 0,
                    num_ood_samples: 1,
                    ood_pow_bits: 0,
                }
            })
            .collect();
        Self {
            cap_size,
            base_round,
            internal_rounds,
        }
    }

    /// The VIRTUAL-PACKING twin of a schedule with a round-0 fold of 1: the
    /// base round folds by nothing (one value per column per leaf), so
    /// intermediate oracle 0 is the whole batched polynomial — its domain is
    /// kept (LDE factor halved, i.e. one rate bit worse) and it is folded one
    /// step further, so every later oracle is unchanged. Its query count is
    /// recomputed for the worse rate under `proximity_testing_mode` at
    /// `security_bits` with the same PoW. The physical packing is kept.
    pub fn to_virtual_packing(
        &self,
        security_bits: u32,
        proximity_testing_mode: &impl ProximityTestingMode,
    ) -> Self {
        assert_eq!(
            self.base_round.fold_log2, 1,
            "the virtual-packing twin is defined for a schedule with a round-0 fold of 1"
        );
        let mut result = self.clone();
        result.base_round.fold_log2 = 0;
        let first = &mut result.internal_rounds[0];
        assert!(
            first.lde_factor_log2 >= 2,
            "intermediate oracle 0 must keep an LDE factor >= 2 after halving"
        );
        first.lde_factor_log2 -= 1;
        first.folding_log2 += 1;
        first.num_queries = proximity_testing_mode.num_queries_for_rate_and_bits_of_security(
            security_bits - first.queries_pow_bits,
            first.lde_factor_log2 as u32,
        ) as usize;
        result
    }

    /// Base round + internal rounds.
    pub fn num_rounds(&self) -> usize {
        1 + self.internal_rounds.len()
    }

    pub fn base_lde_factor(&self) -> usize {
        self.base_round.lde_factor()
    }

    pub fn base_lde_factor_log2(&self) -> usize {
        self.base_round.lde_factor_log2
    }

    pub fn pack_log2(&self) -> usize {
        self.base_round.physical_packing_log2
    }

    /// Round-0 sumcheck steps (`0` under virtual packing).
    pub fn base_folding_log2(&self) -> usize {
        self.base_round.fold_log2
    }

    /// Values every base leaf holds per committed column.
    pub fn base_values_per_leaf(&self) -> usize {
        self.base_round.values_per_leaf()
    }

    pub fn is_virtual_packing(&self) -> bool {
        self.base_round.is_virtual_packing()
    }

    /// Fold steps per round: the base round's, then every internal round's.
    pub fn fold_steps(&self) -> Vec<usize> {
        core::iter::once(self.base_folding_log2())
            .chain(self.internal_rounds.iter().map(|r| r.folding_log2))
            .collect()
    }

    /// Query counts per round: the base round's, then every internal round's.
    pub fn queries_per_round(&self) -> Vec<usize> {
        core::iter::once(self.base_round.num_queries)
            .chain(self.internal_rounds.iter().map(|r| r.num_queries))
            .collect()
    }

    /// Query-draw PoW bits per round: the base round's, then every internal
    /// round's.
    pub fn queries_pow_bits_per_round(&self) -> Vec<u32> {
        core::iter::once(self.base_round.queries_pow_bits)
            .chain(self.internal_rounds.iter().map(|r| r.queries_pow_bits))
            .collect()
    }

    /// LDE factors of the intermediate oracles, in order.
    pub fn intermediate_lde_factors(&self) -> Vec<usize> {
        self.internal_rounds
            .iter()
            .map(|r| r.lde_factor())
            .collect()
    }

    pub fn total_queries(&self) -> usize {
        self.queries_per_round().iter().sum()
    }

    pub fn total_poly_size_reduction(&self) -> usize {
        self.fold_steps().iter().sum()
    }

    /// Total OOD samples across the internal rounds.
    pub fn total_ood_samples(&self) -> usize {
        self.internal_rounds.iter().map(|r| r.num_ood_samples).sum()
    }

    /// `log2` of the plain-text tail polynomial for a `2^message_size_log2`
    /// WHIR message.
    pub fn final_poly_size_log2(&self, message_size_log2: usize) -> usize {
        let reduction = self.total_poly_size_reduction();
        assert!(
            message_size_log2 >= reduction,
            "the WHIR schedule folds by {reduction} but the message has {message_size_log2} variables"
        );
        message_size_log2 - reduction
    }
}

// LEGACY-COMPAT (delete once every tracked proof / config fixture has been
// regenerated with the refactored layout): the pre-refactor JSON shape of
// `WhirSchedule` was six flat arrays (`base_lde_factor`, `cap_size`,
// `whir_steps_schedule`, `whir_queries_schedule`, `whir_steps_lde_factors`,
// `whir_pow_schedule`). The decoder accepts either shape; a legacy schedule
// decodes as an UNPACKED one — the enclosing `ProverConfig` decoder re-applies
// a legacy `pack_log2` to it.
pub(crate) mod legacy_compat {
    use super::*;

    #[derive(Deserialize)]
    pub(crate) struct WhirScheduleRepr {
        pub cap_size: usize,
        #[serde(default)]
        pub base_round: Option<WhirBaseRoundSchedule>,
        #[serde(default)]
        pub internal_rounds: Option<Vec<WhirInternalRound>>,
        #[serde(default)]
        pub base_lde_factor: Option<usize>,
        #[serde(default)]
        pub whir_steps_schedule: Option<Vec<usize>>,
        #[serde(default)]
        pub whir_queries_schedule: Option<Vec<usize>>,
        #[serde(default)]
        pub whir_steps_lde_factors: Option<Vec<usize>>,
        #[serde(default)]
        pub whir_pow_schedule: Option<Vec<u32>>,
    }

    impl From<WhirScheduleRepr> for WhirSchedule {
        fn from(repr: WhirScheduleRepr) -> Self {
            match (repr.base_round, repr.internal_rounds) {
                (Some(base_round), Some(internal_rounds)) => Self {
                    cap_size: repr.cap_size,
                    base_round,
                    internal_rounds,
                },
                (None, None) => WhirSchedule::from_legacy_arrays(
                    repr.base_lde_factor
                        .expect("legacy WHIR schedule: base_lde_factor"),
                    repr.cap_size,
                    0,
                    &repr
                        .whir_steps_schedule
                        .expect("legacy WHIR schedule: whir_steps_schedule"),
                    &repr
                        .whir_queries_schedule
                        .expect("legacy WHIR schedule: whir_queries_schedule"),
                    &repr
                        .whir_steps_lde_factors
                        .expect("legacy WHIR schedule: whir_steps_lde_factors"),
                    &repr
                        .whir_pow_schedule
                        .expect("legacy WHIR schedule: whir_pow_schedule"),
                ),
                _ => panic!("WHIR schedule JSON mixes the current and the legacy layout"),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn legacy_arrays_round_trip_through_accessors() {
        let schedule = WhirSchedule::from_legacy_arrays(
            2,
            16,
            0,
            &[1, 5, 5, 4, 4],
            &[89, 11, 7, 6, 5],
            &[256, 8192, 32768, 524288],
            &[26, 27, 25, 25, 21],
        );
        assert_eq!(schedule.fold_steps(), vec![1, 5, 5, 4, 4]);
        assert_eq!(schedule.queries_per_round(), vec![89, 11, 7, 6, 5]);
        assert_eq!(
            schedule.queries_pow_bits_per_round(),
            vec![26, 27, 25, 25, 21]
        );
        assert_eq!(
            schedule.intermediate_lde_factors(),
            vec![256, 8192, 32768, 524288]
        );
        assert_eq!(schedule.base_lde_factor(), 2);
        assert_eq!(schedule.base_values_per_leaf(), 2);
        assert_eq!(schedule.final_poly_size_log2(20), 1);
        assert_eq!(schedule.total_ood_samples(), 4);
    }

    #[test]
    fn legacy_json_decodes() {
        let json = r#"{"base_lde_factor": 2, "cap_size": 16, "whir_steps_schedule": [1, 5, 5, 4, 4],
            "whir_queries_schedule": [89, 11, 7, 6, 5], "whir_steps_lde_factors": [256, 8192, 32768, 524288],
            "whir_pow_schedule": [26, 27, 25, 25, 21]}"#;
        let decoded: WhirSchedule = serde_json::from_str(json).unwrap();
        let expected = WhirSchedule::from_legacy_arrays(
            2,
            16,
            0,
            &[1, 5, 5, 4, 4],
            &[89, 11, 7, 6, 5],
            &[256, 8192, 32768, 524288],
            &[26, 27, 25, 25, 21],
        );
        assert_eq!(decoded, expected);
        // and the current layout round-trips
        let reencoded = serde_json::to_string(&expected).unwrap();
        let decoded: WhirSchedule = serde_json::from_str(&reencoded).unwrap();
        assert_eq!(decoded, expected);
    }
}
