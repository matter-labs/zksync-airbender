use crate::upstream::WhirSchedule;

pub const L1_WHIR_TILE_BYTES: usize = 1 << 30;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OracleShape {
    pub log_n: u32,
    pub log_lde: u32,
    pub log_domain: u32,
    pub log_v: u32,
    pub log_leaves: u32,
    pub skip_bottom: u32,
    pub cap_log: u32,
    pub tile_cosets_log2: u32,
    pub retained_per_coset: usize,
    pub path_len: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RoundShape {
    pub folds: u32,
    pub queries: usize,
    pub pow_bits: u32,
    pub log_poly_after: u32,
    pub query_domain_log2: u32,
    pub oracle: Option<OracleShape>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L1WhirShape {
    pub log_message: u32,
    pub log_base_lde: u32,
    pub cap_log: u32,
    pub rounds: Vec<RoundShape>,
    pub term_capacity: usize,
    pub total_sumcheck_polys: usize,
    pub log_final: u32,
}

impl L1WhirShape {
    pub fn from_schedule(
        schedule: &WhirSchedule,
        log_message: u32,
        log_base_lde: u32,
        log_base_values_per_leaf: u32,
        tile_bytes: usize,
    ) -> Self {
        let count = schedule.whir_steps_schedule.len();
        assert!(count >= 2, "Proth120 WHIR: at least two rounds required");
        assert!(
            schedule.whir_queries_schedule.len() == count
                && schedule.whir_pow_schedule.len() == count
                && schedule.whir_steps_lde_factors.len() == count - 1,
            "Proth120 WHIR: schedule lengths differ"
        );
        assert!(
            (1..=26).contains(&log_message),
            "Proth120 WHIR: log_message outside 1..=26"
        );
        let total_folds = schedule
            .whir_steps_schedule
            .iter()
            .try_fold(0usize, |acc, folds| acc.checked_add(*folds))
            .expect("Proth120 WHIR: sum of folds overflow");
        assert!(
            total_folds <= log_message as usize,
            "Proth120 WHIR: sum of folds exceeds log_message"
        );
        assert!(
            schedule.cap_size.is_power_of_two(),
            "Proth120 WHIR: cap_size must be a power of two"
        );
        assert!(
            schedule.base_lde_factor.is_power_of_two(),
            "Proth120 WHIR: base LDE factor must be a power of two"
        );
        assert_eq!(
            schedule.base_lde_factor.trailing_zeros(),
            log_base_lde,
            "Proth120 WHIR: base LDE factor differs"
        );
        let cap_log = schedule.cap_size.trailing_zeros();
        assert!(
            cap_log <= log_base_lde,
            "Proth120 WHIR: cap_log exceeds base log_lde"
        );
        assert!(
            log_message + log_base_lde <= 31,
            "Proth120 WHIR: base log_domain exceeds 31"
        );
        assert_eq!(
            schedule.whir_steps_schedule[0], log_base_values_per_leaf as usize,
            "Proth120 WHIR: first folds differ from base values per leaf"
        );
        assert!(
            tile_bytes.is_power_of_two(),
            "Proth120 WHIR: tile_bytes must be a power of two"
        );
        let mut rounds: Vec<RoundShape> = Vec::with_capacity(count);
        let mut log_n = log_message;
        let mut prior_query_domain = 0;
        let mut term_capacity = 0usize;
        let mut total_sumcheck_polys = 0usize;
        for r in 0..count {
            let folds = u32::try_from(schedule.whir_steps_schedule[r])
                .expect("Proth120 WHIR: folds overflow u32");
            assert!(
                (1..=4).contains(&folds),
                "Proth120 WHIR: folds outside 1..=4"
            );
            log_n = log_n
                .checked_sub(folds)
                .expect("Proth120 WHIR: sum of folds exceeds log_message");
            total_sumcheck_polys += folds as usize;
            let queries = schedule.whir_queries_schedule[r];
            assert!(
                queries >= 1 && queries <= u32::MAX as usize,
                "Proth120 WHIR: queries outside 1..=u32::MAX"
            );
            assert!(
                schedule.whir_pow_schedule[r] <= 32,
                "Proth120 WHIR: pow_bits exceeds 32"
            );
            let query_domain_log2 = if r == 0 {
                log_message + log_base_lde - folds
            } else {
                rounds[r - 1].oracle.unwrap().log_domain - folds
            };
            prior_query_domain = prior_query_domain.max(query_domain_log2);
            let oracle = if r + 1 < count {
                let factor = schedule.whir_steps_lde_factors[r];
                assert!(
                    factor.is_power_of_two(),
                    "Proth120 WHIR: oracle LDE factor must be a power of two"
                );
                let log_lde = factor.trailing_zeros();
                let log_domain = log_n + log_lde;
                assert!(log_n >= 8, "Proth120 WHIR: oracle log_n below 8");
                assert!(
                    log_domain <= 31,
                    "Proth120 WHIR: oracle log_domain exceeds 31"
                );
                assert!(
                    cap_log <= log_lde,
                    "Proth120 WHIR: cap_log exceeds oracle log_lde"
                );
                assert!(
                    log_domain >= prior_query_domain,
                    "Proth120 WHIR: oracle domain below earlier query domain"
                );
                let log_v = u32::try_from(schedule.whir_steps_schedule[r + 1])
                    .expect("Proth120 WHIR: log_v overflow u32");
                assert!(
                    (1..=4).contains(&log_v),
                    "Proth120 WHIR: log_v outside 1..=4"
                );
                let log_leaves = log_n
                    .checked_sub(log_v)
                    .expect("Proth120 WHIR: leaf width exceeds oracle length");
                assert!(
                    log_leaves >= 1,
                    "Proth120 WHIR: oracle has no leaf index bits"
                );
                let skip_bottom = log_leaves.min(5);
                assert!(
                    tile_bytes >= 16usize << log_n,
                    "Proth120 WHIR: tile_bytes below one coset"
                );
                let tile_cosets_log2 = (tile_bytes / 16)
                    .trailing_zeros()
                    .saturating_sub(log_n)
                    .min(log_lde);
                term_capacity = term_capacity
                    .checked_add(queries)
                    .expect("Proth120 WHIR: term_capacity overflow");
                Some(OracleShape {
                    log_n,
                    log_lde,
                    log_domain,
                    log_v,
                    log_leaves,
                    skip_bottom,
                    cap_log,
                    tile_cosets_log2,
                    retained_per_coset: 2 * (1usize << (log_leaves - skip_bottom)) - 1,
                    path_len: (log_leaves + log_lde - cap_log) as usize,
                })
            } else {
                None
            };
            rounds.push(RoundShape {
                folds,
                queries,
                pow_bits: schedule.whir_pow_schedule[r],
                log_poly_after: log_n,
                query_domain_log2,
                oracle,
            });
        }
        assert!(
            term_capacity <= 256,
            "Proth120 WHIR: term_capacity exceeds one block"
        );
        Self {
            log_message,
            log_base_lde,
            cap_log,
            rounds,
            term_capacity,
            total_sumcheck_polys,
            log_final: log_n,
        }
    }
}
