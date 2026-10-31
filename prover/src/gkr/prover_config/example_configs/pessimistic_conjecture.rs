//! The [`SoundnessMode::PessimisticConjecture`] ladders: the production
//! sec-100 schedules, keyed by the committed polynomial size.
//!
//! Accounting ([`PessimisticConjectureMode`]): a query into an oracle at rate
//! `2^-r` is worth `r` bits, the query count is `ceil(1.2 * (100 - pow) / r)`
//! per round, the batching challenge is gated by the field-size proof of
//! work of [`pow_bits`](super::super::pow_bits), and the folding challenges
//! and the single OOD sample per oracle draw without proof of work.

use crate::gkr::whir::proximity_testing_modes::PessimisticConjectureMode;

use super::*;

fn whir_schedule(
    level: SecurityLevel,
    message_size_log2: usize,
    packing: BasePacking,
) -> WhirSchedule {
    let input = WhirInput {
        message_size_log2,
        physical_packing_log2: packing.physical_packing_log2,
        virtual_packing: packing.virtual_packing,
        num_committed_polys: None,
    };
    try_whir_schedule(level, &input).unwrap_or_else(|error| panic!("{error}"))
}

/// The schedule for `2^message_size_log2` committed polynomials under
/// `packing` (the physical packing is recorded on the base round; virtual
/// packing is the [`WhirSchedule::to_virtual_packing`] twin of the ladder).
pub(super) fn try_whir_schedule(
    level: SecurityLevel,
    input: &WhirInput,
) -> Result<WhirSchedule, ConfigSelectionError> {
    let packing = input.packing();
    let mut schedule = match level {
        SecurityLevel::Sec100 => ladder_for_100_bits(input)?,
    };
    if packing.virtual_packing {
        // The twin re-commits the batched polynomial as intermediate oracle 0
        // at HALF the ladder's LDE factor. Under the Johnson bound that costs
        // the oracle about one bit (the 2^22 ladder: 69 -> 68 bits, see
        // `soundcalc/late_round_rebalance.py`); one more bit of query PoW on
        // that oracle restores the ladder's level at no verifier cost, and the
        // pessimistic rule's query count is derived at the raised PoW (18 at
        // 2^22, unchanged).
        schedule.internal_rounds[0].queries_pow_bits += 1;
        schedule =
            schedule.to_virtual_packing(level.security_bits() as u32, &PessimisticConjectureMode);
    }
    Ok(schedule)
}

/// The sec-100 ladder for a `2^message_size_log2` message: base LDE factor
/// [`DEFAULT_LDE_FACTOR`], cap [`DEFAULT_CAP_SIZE`], a round-0 fold of 1
/// (two values per column per base leaf), one OOD sample per intermediate
/// oracle, no OOD or folding PoW.
fn ladder_for_100_bits(input: &WhirInput) -> Result<WhirSchedule, ConfigSelectionError> {
    let (steps, queries, lde_factors, pows): (&[usize], &[usize], &[usize], &[u32]) =
        match input.message_size_log2 {
            20 => (
                &[1, 5, 5, 4, 4],
                &[89, 11, 8, 7, 7],
                &[256, 4096, 8192, 16384],
                &[26, 27, 25, 25, 21],
            ),
            21 => (
                &[1, 5, 5, 5, 4],
                &[89, 15, 8, 7, 7],
                &[64, 2048, 8192, 16384],
                &[26, 25, 27, 25, 21],
            ),
            22 => (
                &[1, 5, 5, 5, 5],
                &[89, 15, 8, 7, 7],
                &[64, 2048, 8192, 16384],
                &[26, 25, 27, 25, 21],
            ),
            // Stops at the 2^3 polynomial (plain-text tail): the former sixth
            // round folded 2^3 -> 2^1 through ANOTHER committed oracle — an LDE
            // of a degree-8 polynomial, below the
            // 2^DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2 floor now enforced by
            // `ProverConfig::validate_for_whir_message_size`.
            23 => (
                &[1, 5, 5, 5, 4],
                &[89, 23, 10, 8, 7],
                &[16, 512, 8192, 16384],
                &[26, 24, 25, 19, 21],
            ),
            24 => (
                &[1, 5, 5, 5, 4, 3],
                &[89, 23, 10, 8, 7, 6],
                &[16, 512, 8192, 16384, 131072],
                &[26, 24, 25, 19, 21, 21],
            ),
            _ => {
                return Err(ConfigSelectionError::MissingSchedule {
                    mode: SoundnessMode::PessimisticConjecture,
                    level: SecurityLevel::Sec100,
                    input: *input,
                })
            }
        };
    Ok(WhirSchedule::from_legacy_arrays(
        DEFAULT_LDE_FACTOR,
        DEFAULT_CAP_SIZE,
        input.physical_packing_log2,
        steps,
        queries,
        lde_factors,
        pows,
    ))
}

/// The unpacked standard config of a `2^trace_len_log2` trace at `level`
/// (two values per column per base leaf).
pub fn config_for_security_level_under_pessimistic_conjecture(
    trace_len_log2: usize,
    level: SecurityLevel,
) -> ProverConfig {
    standard_config(
        trace_len_log2,
        level,
        whir_schedule(level, trace_len_log2, BasePacking::NONE),
    )
}

pub fn config_for_100_bits_under_pessimistic_conjecture(trace_len_log2: usize) -> ProverConfig {
    config_for_security_level_under_pessimistic_conjecture(trace_len_log2, SecurityLevel::Sec100)
}

/// [`config_for_security_level_under_pessimistic_conjecture`] for a PACKED base
/// commitment (`pack_log2 > 0`): the GKR side (trace length, same-size
/// sumcheck schedule, explicit sumcheck output) is the `trace_len_log2`
/// config's, while the WHIR side (base LDE factor, cap, values per leaf and
/// the whole fold/query/PoW schedule) is the ladder of the packed message size
/// `trace_len_log2 + pack_log2` — the WHIR run starts from the
/// `2^(trace_len_log2 + pack_log2)`-variate packed polynomials, so its
/// schedule must be the one computed for that size. `pack_log2 == 0` returns
/// the plain config.
pub fn packed_config_for_security_level_under_pessimistic_conjecture(
    trace_len_log2: usize,
    pack_log2: usize,
    level: SecurityLevel,
) -> ProverConfig {
    let packing = BasePacking::physical(pack_log2);
    standard_config(
        trace_len_log2,
        level,
        whir_schedule(level, packing.message_size_log2(trace_len_log2), packing),
    )
}

/// [`config_for_security_level_under_pessimistic_conjecture`] with the
/// VIRTUAL-PACKING base round (`fold_log2 = 0`, see
/// [`WhirBaseRoundSchedule`]): the same GKR side and the
/// [`WhirSchedule::to_virtual_packing`] twin of the standard WHIR schedule —
/// one value per column per base leaf, no round-0 sumcheck, intermediate
/// oracle 0 at the same domain size (one rate bit worse, folded one step
/// further) and every later oracle unchanged. Its round-1 query count is
/// recomputed under [`PessimisticConjectureMode`] for the worse rate.
pub fn virtual_packing_config_for_security_level_under_pessimistic_conjecture(
    trace_len_log2: usize,
    level: SecurityLevel,
) -> ProverConfig {
    virtual_packed_config_for_security_level_under_pessimistic_conjecture(trace_len_log2, 0, level)
}

/// The virtual-packing twin of
/// [`packed_config_for_security_level_under_pessimistic_conjecture`]: physical
/// packing by `2^pack_log2` AND `fold_log2 = 0` (one value per packed column
/// per base leaf, no round-0 sumcheck). `pack_log2 = 0` is
/// [`virtual_packing_config_for_security_level_under_pessimistic_conjecture`].
pub fn virtual_packed_config_for_security_level_under_pessimistic_conjecture(
    trace_len_log2: usize,
    pack_log2: usize,
    level: SecurityLevel,
) -> ProverConfig {
    let packing = BasePacking::physical_and_virtual(pack_log2);
    standard_config(
        trace_len_log2,
        level,
        whir_schedule(level, packing.message_size_log2(trace_len_log2), packing),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr::whir::proximity_testing_modes::ProximityTestingMode;

    pub(crate) fn assert_every_round_preserves_security_margin(config: &ProverConfig) {
        let schedule = &config.whir_schedule;
        let security_bits = config.security_level.security_bits() as u32;
        let rates = std::iter::once(schedule.base_lde_factor_log2() as u32).chain(
            schedule
                .internal_rounds
                .iter()
                .map(|r| r.lde_factor_log2 as u32),
        );
        for (round, ((queries, pow), rate_bits)) in schedule
            .queries_per_round()
            .into_iter()
            .zip(schedule.queries_pow_bits_per_round())
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
                    schedule.base_round.queries_pow_bits,
                    schedule.base_round.num_queries
                ),
                (26, 89)
            );
            assert_every_round_preserves_security_margin(&config);
            config.validate_for_whir_message_size(trace_log2);
        }
        assert_every_round_preserves_security_margin(&evm_production_packed_prover_config(
            SecurityLevel::Sec100,
        ));
    }

    /// The three base-round strategies on the 2^20 (blake delegation) trace
    /// are self-consistent: the packed and virtual twins keep the standard
    /// ladder's security margin, fold the (virtual / packed) message down
    /// to the plain-text tail and keep every oracle domain within BabyBear's
    /// two-adicity.
    #[test]
    fn blake_strategy_variants_are_self_consistent() {
        let level = SecurityLevel::Sec100;
        let default = config_for_security_level_under_pessimistic_conjecture(20, level);
        let packed = packed_config_for_security_level_under_pessimistic_conjecture(20, 4, level);
        let virtual_ =
            virtual_packing_config_for_security_level_under_pessimistic_conjecture(20, level);
        for config in [&default, &packed, &virtual_] {
            assert_every_round_preserves_security_margin(config);
            config.validate_for_whir_message_size(config.whir_message_size_log2());
            let mut poly_size_log2 =
                config.whir_message_size_log2() - config.whir_schedule.base_folding_log2();
            for round in config.whir_schedule.internal_rounds.iter() {
                assert!(
                    poly_size_log2 + round.lde_factor_log2 <= 27,
                    "oracle domain exceeds 2^27"
                );
                poly_size_log2 -= round.folding_log2;
            }
        }
        // default: 2 values per column per leaf, fold 1 + [5, 5, 4, 4] -> 2^1 tail
        assert_eq!(default.base_oracles_values_per_leaf(), 2);
        assert_eq!(default.whir_schedule.fold_steps(), vec![1, 5, 5, 4, 4]);
        assert_eq!(default.whir_schedule.final_poly_size_log2(20), 1);
        // packed by 16: the 2^24 ladder on a 2^24 message, 2 values per
        // PACKED column per leaf -> 2^1 tail
        assert_eq!(packed.pack_log2(), 4);
        assert_eq!(packed.whir_message_size_log2(), 24);
        assert_eq!(packed.base_oracles_values_per_leaf(), 2);
        assert_eq!(packed.whir_schedule.fold_steps(), vec![1, 5, 5, 5, 4, 3]);
        assert_eq!(packed.whir_schedule.final_poly_size_log2(24), 1);
        // virtual: one value per column per leaf, no round-0 fold, oracle 0
        // keeps its 2^27 domain (LDE 256 -> 128) and folds by 6 -> 2^1 tail
        assert!(virtual_.is_virtual_packing());
        assert_eq!(virtual_.pack_log2(), 0);
        assert_eq!(virtual_.base_oracles_values_per_leaf(), 1);
        assert_eq!(virtual_.whir_schedule.fold_steps(), vec![0, 6, 5, 4, 4]);
        assert_eq!(
            virtual_.whir_schedule.intermediate_lde_factors(),
            vec![128, 4096, 8192, 16384]
        );
        assert_eq!(virtual_.whir_schedule.final_poly_size_log2(20), 1);
        let round0 = &virtual_.whir_schedule.internal_rounds[0];
        // one more bit of query PoW than the ladder's oracle 0 (see `whir_schedule`)
        assert_eq!(
            round0.queries_pow_bits,
            default.whir_schedule.internal_rounds[0].queries_pow_bits + 1
        );
        assert_eq!(
            round0.num_queries,
            PessimisticConjectureMode
                .num_queries_for_rate_and_bits_of_security(100 - round0.queries_pow_bits, 7)
                as usize
        );
        assert_eq!(round0.num_queries, 13);
        assert_eq!(
            &virtual_.whir_schedule.internal_rounds[1..],
            &default.whir_schedule.internal_rounds[1..]
        );
    }

    /// The production schedule of the delegation circuits (bigint, keccak,
    /// blake2_g_function on 2^22 traces; blake2_with_compression on a 2^20
    /// trace packed by 2^2): the virtual twin of the 2^22 ladder, oracle 0 at
    /// 18 queries with 26 bits of query PoW.
    #[test]
    fn delegation_virtual_twin_of_the_2_22_ladder() {
        let level = SecurityLevel::Sec100;
        let plain = config_for_security_level_under_pessimistic_conjecture(22, level);
        let twin =
            virtual_packing_config_for_security_level_under_pessimistic_conjecture(22, level);
        let packed_twin =
            virtual_packed_config_for_security_level_under_pessimistic_conjecture(20, 2, level);
        assert_eq!(
            plain.whir_schedule.queries_per_round(),
            vec![89, 15, 8, 7, 7]
        );
        assert_eq!(
            plain.whir_schedule.intermediate_lde_factors(),
            vec![64, 2048, 8192, 16384]
        );
        for config in [&twin, &packed_twin] {
            assert_every_round_preserves_security_margin(config);
            let schedule = &config.whir_schedule;
            assert_eq!(schedule.fold_steps(), vec![0, 6, 5, 5, 5]);
            assert_eq!(schedule.queries_per_round(), vec![89, 18, 8, 7, 7]);
            assert_eq!(
                schedule.intermediate_lde_factors(),
                vec![32, 2048, 8192, 16384]
            );
            assert_eq!(
                schedule.queries_pow_bits_per_round(),
                vec![26, 26, 27, 25, 21]
            );
            assert_eq!(schedule.final_poly_size_log2(22), 1);
        }
        assert_eq!(packed_twin.pack_log2(), 2);
        assert_eq!(packed_twin.whir_message_size_log2(), 22);
    }

    /// The batching-challenge PoW is the correlated-agreement bound of the
    /// committed columns on the base domain, so the base round's fold
    /// (2 values per column per leaf vs. virtual packing) must not change it;
    /// physical packing changes it only through the packed message size and
    /// the packed column count, which cancel for the blake widths.
    #[test]
    fn batching_pow_bits_do_not_depend_on_the_base_round_fold() {
        use crate::gkr::prover_config::pow_bits::physically_committed_polys;
        use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};

        let level = SecurityLevel::Sec100;
        let security_bits = level.security_bits();
        // blake2_with_extended_control: 225 memory + 538 witness + 6 setup columns
        let (memory, witness, setup) = (225, 538, 6);
        for pack_log2 in 0..=4 {
            let packed =
                packed_config_for_security_level_under_pessimistic_conjecture(20, pack_log2, level);
            let virtual_ = virtual_packed_config_for_security_level_under_pessimistic_conjecture(
                20, pack_log2, level,
            );
            assert_eq!(packed.base_oracles_values_per_leaf(), 2);
            assert_eq!(virtual_.base_oracles_values_per_leaf(), 1);
            assert_eq!(packed.whir_message_size_log2(), 20 + pack_log2);
            assert_eq!(virtual_.whir_message_size_log2(), 20 + pack_log2);
            let committed = physically_committed_polys(memory, witness, setup, pack_log2);
            let bits = |config: &ProverConfig| {
                config
                    .whir_schedule
                    .base_round
                    .batching_pow_bits::<BabyBearField, BabyBearExt4>(
                        security_bits,
                        config.whir_message_size_log2(),
                        committed,
                    )
            };
            assert_eq!(bits(&packed), bits(&virtual_), "pack_log2 = {pack_log2}");
            // 123 - (21 + pack) - ceil_log2(769 / 2^pack) = 92 for every pack <= 4
            assert_eq!(bits(&packed), 8, "pack_log2 = {pack_log2}");
        }
        // an explicitly configured value survives the virtual twin unchanged
        let mut explicit =
            packed_config_for_security_level_under_pessimistic_conjecture(20, 2, level);
        explicit.whir_schedule.base_round.batching_pow_bits = Some(11);
        let twin = explicit
            .whir_schedule
            .to_virtual_packing(security_bits as u32, &PessimisticConjectureMode);
        assert_eq!(twin.base_round.batching_pow_bits, Some(11));
        assert_eq!(
            twin.base_round
                .batching_pow_bits::<BabyBearField, BabyBearExt4>(security_bits, 22, 194),
            11
        );
    }
}
