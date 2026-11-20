use crate::upstream::ProverConfig;
use gpu_hash::keccak256::MAX_POW_BITS;
use gpu_ntt::proth120::LOG_MAX_DOMAIN;

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
    pub folding_pow_bits: u32,
    /// Difficulty for the next oracle's OOD draw; zero in the final round.
    pub ood_pow_bits: u32,
    pub ood_samples: usize,
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
    pub max_internal_leaf_width: usize,
    pub log_final: u32,
}

impl L1WhirShape {
    pub fn from_config(config: &ProverConfig) -> Self {
        let schedule = &config.whir_schedule;
        let log_message = u32::try_from(config.whir_message_size_log2())
            .expect("Proth120 WHIR: message log exceeds u32");
        assert!(
            (1..=26).contains(&log_message),
            "Proth120 WHIR: message log {log_message} outside 1..=26"
        );
        let log_base_lde = u32::try_from(config.base_lde_factor_log2())
            .expect("Proth120 WHIR: base LDE log exceeds u32");
        let check_domain = |log_n: u32, log_lde: u32, oracle: usize| {
            assert!(
                log_lde <= LOG_MAX_DOMAIN - log_n,
                "Proth120 WHIR: oracle {oracle} domain log ({log_n} + {log_lde}) exceeds {LOG_MAX_DOMAIN}"
            );
        };
        check_domain(log_message, log_base_lde, 0);
        for (r, round) in schedule.internal_rounds.iter().enumerate() {
            assert!(
                round.lde_factor_log2 <= LOG_MAX_DOMAIN as usize,
                "Proth120 WHIR: oracle {} LDE log exceeds {LOG_MAX_DOMAIN}",
                r + 1
            );
        }
        config.validate_for_whir_message_size(log_message as usize);
        let cap_log = config.cap_size.trailing_zeros();
        let fold_steps = schedule.fold_steps();
        let queries = schedule.queries_per_round();
        let pow_bits = schedule.queries_pow_bits_per_round();
        if let Some(bits) = schedule.base_round.batching_pow_bits {
            assert!(
                bits <= MAX_POW_BITS,
                "Proth120 WHIR: batching PoW bits {bits} exceed {MAX_POW_BITS}"
            );
        }
        let count = schedule.num_rounds();
        let mut rounds: Vec<RoundShape> = Vec::with_capacity(count);
        let mut log_n = log_message;
        let mut term_capacity = 0;
        let mut total_sumcheck_polys = 0;
        for r in 0..count {
            let folds = fold_steps[r] as u32;
            assert!(
                folds <= 6,
                "Proth120 WHIR: round {r} folding log {folds} exceeds 6"
            );
            assert!(
                queries[r] <= u32::MAX as usize,
                "Proth120 WHIR: round {r} query count exceeds u32"
            );
            assert!(
                pow_bits[r] <= MAX_POW_BITS,
                "Proth120 WHIR: round {r} query PoW bits {} exceed {MAX_POW_BITS}",
                pow_bits[r]
            );
            log_n -= folds;
            total_sumcheck_polys += folds as usize;
            let query_domain_log2 = if r == 0 {
                log_message + log_base_lde - folds
            } else {
                rounds[r - 1].oracle.unwrap().log_domain - folds
            };
            let oracle = if r + 1 < count {
                let next = &schedule.internal_rounds[r];
                let log_lde = next.lde_factor_log2 as u32;
                let log_v = next.folding_log2 as u32;
                let log_leaves = log_n - log_v;
                check_domain(log_n, log_lde, r + 1);
                assert!(
                    log_lde + log_n >= query_domain_log2,
                    "Proth120 WHIR: oracle {} domain log is below round {r}'s query domain",
                    r + 1
                );
                let skip_bottom = (log_leaves - cap_log.saturating_sub(log_lde)).min(5);
                assert!(
                    log_n <= 12 || skip_bottom == 5,
                    "Proth120 WHIR: oracle {} cap_log {cap_log} is too wide for a log_n {log_n} commitment",
                    r + 1
                );
                assert!(
                    queries[r + 1]
                        .checked_mul(1 << skip_bottom)
                        .is_some_and(|n| n <= i32::MAX as usize),
                    "Proth120 WHIR: round {r} query subtree count exceeds the CUDA grid limit"
                );
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
                        .min(log_lde)
                        .min(15),
                    retained_per_coset: 2 * (1 << (log_leaves - skip_bottom)) - 1,
                    path_len: (log_leaves + log_lde - cap_log) as usize,
                })
            } else {
                None
            };
            let folding_pow_bits = if r == 0 {
                schedule.base_round.folding_pow_bits
            } else {
                schedule.internal_rounds[r - 1].folding_pow_bits
            };
            let (ood_samples, ood_pow_bits) = schedule
                .internal_rounds
                .get(r)
                .map_or((0, 0), |next| (next.num_ood_samples, next.ood_pow_bits));
            assert!(
                folding_pow_bits <= MAX_POW_BITS,
                "Proth120 WHIR: round {r} folding PoW bits {folding_pow_bits} exceed {MAX_POW_BITS}"
            );
            assert!(
                ood_pow_bits <= MAX_POW_BITS,
                "Proth120 WHIR: round {r} OOD PoW bits {ood_pow_bits} exceed {MAX_POW_BITS}"
            );
            rounds.push(RoundShape {
                folds,
                queries: queries[r],
                pow_bits: pow_bits[r],
                folding_pow_bits,
                ood_pow_bits,
                ood_samples,
                log_poly_after: log_n,
                query_domain_log2,
                oracle,
            });
        }
        let max_internal_leaf_width = 1
            << schedule
                .internal_rounds
                .iter()
                .map(|round| round.folding_log2)
                .max()
                .unwrap();
        Self {
            log_message,
            log_base_lde,
            cap_log,
            rounds,
            term_capacity,
            total_sumcheck_polys,
            max_internal_leaf_width,
            log_final: log_n,
        }
    }
}
