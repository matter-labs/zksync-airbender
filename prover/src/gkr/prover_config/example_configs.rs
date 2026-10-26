use crate::definitions::*;
use crate::gkr::whir::proximity_testing_modes::PessimisticConjectureMode;

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
        // the L1 feeder flow commits the single merged memory+witness tree
        commitment_mode: CommitmentMode::MergedMemoryAndWitness,
        same_size_sumcheck_schedule: crate::gkr::prover_config::windowed_same_size_schedule(23),
        dimension_reducing_sumcheck_schedule: Default::default(),
        cap_size: DEFAULT_CAP_SIZE,
        sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
        security_level: SecurityLevel::Sec100,
        // Total fold 20: the WHIR run STOPS at the 2^3 polynomial and ships
        // its 8 monomial coefficients in plain text — no LDE/oracle for the
        // degree-8 tail (the extra fold-by-2 round on a 2^27-domain oracle is
        // dropped entirely).
        //
        // rates 2^-4 / 2^-5 / 2^-10 / 2^-15 / 2^-20; per-round PoW pushed
        // to the next query-count boundary (grinds capped at 2^30):
        //   ceil(1.2 * floor(71 / 4))  = 21  (pow 29)
        //   ceil(1.2 * floor(74 / 5))  = 17  (pow 26)
        //   ceil(1.2 * floor(75 / 10)) = 9   (pow 25; no boundary <= 30)
        //   ceil(1.2 * floor(74 / 15)) = 5   (pow 26)
        //   ceil(1.2 * floor(79 / 20)) = 4   (pow 21; no boundary <= 30)
        // every oracle domain = 2^27 exactly (BabyBear's two-adicity cap)
        whir_schedule: WhirSchedule::from_legacy_arrays(
            L1_FEEDER_BASE_LDE_FACTOR,
            DEFAULT_CAP_SIZE,
            0,
            &[1, 5, 5, 5, 4],
            &[21, 17, 9, 5, 4],
            &[32, 1024, 32768, 1048576],
            &[29, 26, 25, 26, 21],
        ),
    }
}

/// The standard unpacked sec-100 config shape: base LDE factor
/// [`DEFAULT_LDE_FACTOR`], cap [`DEFAULT_CAP_SIZE`], explicit packing by 1
/// with a round-0 fold of 1 (two values per column per base leaf), windowed
/// same-size sumchecks, and the given per-round fold / query / LDE / PoW
/// ladder (one OOD sample per intermediate oracle, no OOD or folding PoW).
fn standard_config_for_100_bits(
    trace_len_log_2: usize,
    whir_steps_schedule: &[usize],
    whir_queries_schedule: &[usize],
    whir_steps_lde_factors: &[usize],
    whir_pow_schedule: &[u32],
) -> ProverConfig {
    ProverConfig {
        trace_len_log2: trace_len_log_2,
        commitment_mode: CommitmentMode::SeparateMemoryAndWitness,
        same_size_sumcheck_schedule: crate::gkr::prover_config::windowed_same_size_schedule(
            trace_len_log_2,
        ),
        dimension_reducing_sumcheck_schedule: Default::default(),
        cap_size: DEFAULT_CAP_SIZE,
        sumcheck_explicit_output_size_log_2: DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
        security_level: SecurityLevel::Sec100,
        whir_schedule: WhirSchedule::from_legacy_arrays(
            DEFAULT_LDE_FACTOR,
            DEFAULT_CAP_SIZE,
            0,
            whir_steps_schedule,
            whir_queries_schedule,
            whir_steps_lde_factors,
            whir_pow_schedule,
        ),
    }
}

pub fn config_for_100_bits_under_pessimistic_conjecture(trace_len_log_2: usize) -> ProverConfig {
    match trace_len_log_2 {
        20 => standard_config_for_100_bits(
            trace_len_log_2,
            &[1, 5, 5, 4, 4],
            &[89, 11, 7, 6, 5],
            &[256, 8192, 32768, 524288],
            &[26, 27, 25, 25, 21],
        ),
        21 => standard_config_for_100_bits(
            trace_len_log_2,
            &[1, 5, 5, 5, 4],
            &[89, 15, 8, 6, 5],
            &[64, 2048, 32768, 524288],
            &[26, 25, 27, 25, 21],
        ),
        22 => standard_config_for_100_bits(
            trace_len_log_2,
            &[1, 5, 5, 5, 5],
            &[89, 15, 8, 6, 5],
            &[64, 2048, 32768, 524288],
            &[26, 25, 27, 25, 21],
        ),
        // Stops at the 2^3 polynomial (plain-text tail): the former sixth
        // round folded 2^3 -> 2^1 through ANOTHER committed oracle — an LDE
        // of a degree-8 polynomial, below the
        // 2^DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2 floor now enforced by
        // `ProverConfig::validate_for_whir_message_size`.
        23 => standard_config_for_100_bits(
            trace_len_log_2,
            &[1, 5, 5, 5, 4],
            &[89, 23, 10, 7, 5],
            &[16, 512, 16384, 524288],
            &[26, 24, 25, 19, 21],
        ),
        24 => standard_config_for_100_bits(
            trace_len_log_2,
            &[1, 5, 5, 5, 4, 3],
            &[89, 23, 10, 7, 5, 5],
            &[16, 512, 16384, 524288, 524288],
            &[26, 24, 25, 19, 21, 21],
        ),
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
/// `trace_len_log2 + pack_log2` with its base round packing by `2^pack_log2`
/// — the WHIR run starts from the `2^(trace_len_log2 + pack_log2)`-variate
/// packed polynomials, so its schedule must be the one computed for that
/// size. `pack_log2 == 0` returns the plain config.
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
        let mut whir_schedule = whir_side.whir_schedule;
        whir_schedule.base_round.physical_packing_log2 = pack_log2;
        config.cap_size = whir_side.cap_size;
        config.whir_schedule = whir_schedule;
        config.validate_for_whir_message_size(config.whir_message_size_log2());
    }
    config
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
    let mut config =
        packed_config_for_security_level_under_pessimistic_conjecture(trace_len_log2, pack_log2, level);
    config.whir_schedule = config.whir_schedule.to_virtual_packing(
        config.security_level.security_bits() as u32,
        &PessimisticConjectureMode,
    );
    config.validate_for_whir_message_size(config.whir_message_size_log2());
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
        commitment_mode: CommitmentMode::MergedMemoryAndWitness,
        // the EVM verifier (gkr.sol) consumes monomial [c0..c3] rounds;
        // keep these proofs on the windowed schedule (transcript-identical
        // to naive)
        same_size_sumcheck_schedule: windowed_same_size_schedule(EVM_PRODUCTION_TRACE_LEN_LOG2),
        dimension_reducing_sumcheck_schedule: Default::default(),
        cap_size: 8,
        // The GKR dimension-reduction stops at 2^4 and outputs explicit
        // evaluations (this is the GKR-side knob gkr.sol is generated for —
        // NOT the WHIR plain-text tail, which the WHIR schedule determines).
        sumcheck_explicit_output_size_log_2: 4,
        security_level: level,
        // base LDE factor 32 (base_lde_log2 = 5), round-0 values-per-leaf =
        // 2^2; 6 rounds ending in a 2^4 plain-text tail; the 6th round's
        // huge-LDE oracle (the 2^8 poly on a 2^31 domain) is cheap with the
        // continuous intermediate-oracle mode.
        whir_schedule: WhirSchedule::from_legacy_arrays(
            1 << 5,
            8,
            EVM_PRODUCTION_PACK_LOG2,
            &[2, 4, 4, 4, 4, 4],
            &[17, 12, 8, 6, 5, 4],
            &[1 << 7, 1 << 11, 1 << 15, 1 << 19, 1 << 23],
            &[30, 30, 27, 25, 21, 24],
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr::whir::proximity_testing_modes::ProximityTestingMode;

    fn assert_every_round_preserves_security_margin(config: &ProverConfig) {
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
            vec![128, 8192, 32768, 524288]
        );
        assert_eq!(virtual_.whir_schedule.final_poly_size_log2(20), 1);
        let round0 = &virtual_.whir_schedule.internal_rounds[0];
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
        let mut explicit = packed_config_for_security_level_under_pessimistic_conjecture(20, 2, level);
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
