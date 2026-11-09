use crate::upstream::{ProofProfile, SoundnessMode, WhirSchedule};

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
    pub fn from_schedule(schedule: &WhirSchedule) -> Self {
        let config = ProofProfile::L1Wrap.prover_config(21, SoundnessMode::PessimisticConjecture);
        assert_eq!(
            schedule, &config.whir_schedule,
            "Proth120 WHIR requires the wrap schedule"
        );
        let log_message = config.whir_message_size_log2() as u32;
        let log_base_lde = config.lde_factor().trailing_zeros();
        let cap_log = config.cap_size.trailing_zeros();
        let fold_steps = schedule.fold_steps();
        let queries = schedule.queries_per_round();
        let pow_bits = schedule.queries_pow_bits_per_round();
        let lde_factors = schedule.intermediate_lde_factors();
        let count = schedule.num_rounds();
        let mut rounds: Vec<RoundShape> = Vec::with_capacity(count);
        let mut log_n = log_message;
        let mut term_capacity = 0;
        let mut total_sumcheck_polys = 0;
        for r in 0..count {
            let folds = fold_steps[r] as u32;
            log_n -= folds;
            total_sumcheck_polys += folds as usize;
            let query_domain_log2 = if r == 0 {
                log_message + log_base_lde - folds
            } else {
                rounds[r - 1].oracle.unwrap().log_domain - folds
            };
            let oracle = if r + 1 < count {
                let log_lde = lde_factors[r].trailing_zeros();
                let log_v = fold_steps[r + 1] as u32;
                let log_leaves = log_n - log_v;
                let skip_bottom = 5;
                term_capacity += queries[r];
                Some(OracleShape {
                    log_n,
                    log_lde,
                    log_domain: log_n + log_lde,
                    log_v,
                    log_leaves,
                    skip_bottom,
                    cap_log,
                    tile_cosets_log2: (L1_WHIR_TILE_BYTES / 16)
                        .trailing_zeros()
                        .saturating_sub(log_n)
                        .min(log_lde),
                    retained_per_coset: 2 * (1 << (log_leaves - skip_bottom)) - 1,
                    path_len: (log_leaves + log_lde - cap_log) as usize,
                })
            } else {
                None
            };
            rounds.push(RoundShape {
                folds,
                queries: queries[r],
                pow_bits: pow_bits[r],
                log_poly_after: log_n,
                query_domain_log2,
                oracle,
            });
        }
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
