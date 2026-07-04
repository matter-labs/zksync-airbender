//! Compile-in-loop metaheuristic search (Task 6 promotion of
//! `gkr_eval_isa/tests/s3_planner/metaheuristic.rs`'s population/beam/
//! simulated-annealing optimizer, which lived entirely inside that file's
//! `#[cfg(test)] mod tests` — deliberately test-only research code, per its
//! module doc: "must stay out of the production compiler path"). Task 6
//! promotes the algorithm itself (population seeding, neighbor moves, SA
//! acceptance) to production, driven by the real [`super::scorer::score`]
//! fitness function instead of the deleted `Replay` simulation.
//!
//! This is a clean reimplementation of the prototype's algorithm (not a
//! line-for-line port): the prototype's neighbor/beam machinery was entangled
//! with `OracleInstance`/`DemandSite` (the pre-DAG-native oracle types deleted
//! in earlier tasks), so it is re-expressed here directly over [`Genome`] +
//! [`LayerCtx`] + [`CandidateScore`], keeping the same moves (unit swap/insert/
//! reverse, single-gene cache-priority perturbation) and the same
//! deterministic `splitmix64`-seeded RNG + cooling-temperature Metropolis
//! acceptance.

use std::time::{Duration, Instant};

use cs::gkr_compiler::dag_ir::LayerSchedule;

use super::genome::Genome;
use super::scorer::{score, CandidateScore, LayerCtx};

/// Search knobs, env-overridable via `GKR_SEARCH_POP` / `GKR_SEARCH_EVALS` /
/// `GKR_SEARCH_SEED` (checked once via [`SearchConfig::from_env`]). Defaults
/// are a modest but real search: enough evals to escape the neutral seed on
/// production-sized layers without dominating a full producer run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SearchConfig {
    pub pop: usize,
    pub evals: usize,
    pub seed: u64,
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self { pop: 8, evals: 2_000, seed: 0 }
    }
}

impl SearchConfig {
    /// Start from [`Default::default`], overriding any field whose env var
    /// parses as a valid `usize`/`u64`. Malformed env values are ignored (fall
    /// back to the default) rather than panicking — this is a perf knob, not a
    /// correctness input.
    pub fn from_env() -> Self {
        let mut cfg = Self::default();
        if let Some(v) = parse_env_usize("GKR_SEARCH_POP") {
            cfg.pop = v.max(1);
        }
        if let Some(v) = parse_env_usize("GKR_SEARCH_EVALS") {
            cfg.evals = v;
        }
        if let Some(v) = parse_env_u64("GKR_SEARCH_SEED") {
            cfg.seed = v;
        }
        cfg
    }
}

fn parse_env_usize(key: &str) -> Option<usize> {
    std::env::var(key).ok().and_then(|s| s.parse::<usize>().ok())
}

fn parse_env_u64(key: &str) -> Option<u64> {
    std::env::var(key).ok().and_then(|s| s.parse::<u64>().ok())
}

/// Result of searching one layer: the winning `LayerSchedule` (already
/// `predicted_traffic`-stamped from the winning compile) plus the perf-envelope
/// counters the producer prints.
pub struct LayerSearchOutcome {
    pub schedule: LayerSchedule,
    pub compiles: usize,
    pub wall: Duration,
}

// ── deterministic RNG (splitmix64) ──────────────────────────────────────────

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Draw a value in `[0, 1)` from the RNG state.
fn unit_draw(state: &mut u64) -> f64 {
    (splitmix64(state) >> 11) as f64 / (1u64 << 53) as f64
}

fn draw_index(state: &mut u64, n: usize) -> usize {
    if n == 0 {
        return 0;
    }
    (splitmix64(state) % n as u64) as usize
}

// ── neighbor moves ───────────────────────────────────────────────────────────

/// One perturbation of `base`: with unit-order moves available whenever there
/// are >=2 units (swap/insert/reverse acting on unit *keys*, since
/// [`super::decode::decode_unit_order`] sorts by key — a key permutation IS an
/// order permutation) and a cache-priority gene nudge whenever there is >=1
/// site.
fn random_neighbor(base: &Genome, rng: &mut u64) -> Genome {
    let n_units = base.root_order_key.len();
    let n_sites = base.cache_priority.len();
    let order_moves = if n_units >= 2 { 3 } else { 0 };
    let site_moves = if n_sites > 0 { 1 } else { 0 };
    let total_moves = order_moves + site_moves;
    if total_moves == 0 {
        return base.clone();
    }
    let mut choice = draw_index(rng, total_moves);
    if n_units >= 2 {
        if choice == 0 {
            return unit_swap_neighbor(base, rng);
        }
        choice -= 1;
        if choice == 0 {
            return unit_insert_neighbor(base, rng);
        }
        choice -= 1;
        if choice == 0 && n_units >= 3 {
            return unit_reverse_neighbor(base, rng);
        }
        choice = choice.saturating_sub(1);
    }
    let _ = choice; // remaining choice (if any) falls through to cache-priority nudge
    let site_idx = draw_index(rng, n_sites);
    let delta = (unit_draw(rng) - 0.5) * 2.0; // small symmetric bias step
    base.perturb_one_gene(n_units + site_idx, delta)
}

/// Swap two distinct units' keys (equivalent to swapping their decoded
/// position, since `decode_unit_order` sorts by key).
fn unit_swap_neighbor(base: &Genome, rng: &mut u64) -> Genome {
    let n = base.root_order_key.len();
    let i = draw_index(rng, n);
    let mut j = draw_index(rng, n);
    if j == i {
        j = (j + 1) % n;
    }
    let mut out = base.clone();
    out.root_order_key.swap(i, j);
    out
}

/// Move one unit's key just past another unit's key (a local insert in decoded
/// order, expressed directly as a key re-assignment).
fn unit_insert_neighbor(base: &Genome, rng: &mut u64) -> Genome {
    let n = base.root_order_key.len();
    if n < 2 {
        return base.clone();
    }
    let anchor_unit = draw_index(rng, n);
    let mut moved_unit = draw_index(rng, n);
    if moved_unit == anchor_unit {
        moved_unit = (moved_unit + 1) % n;
    }
    let mut out = base.clone();
    let anchor_key = base.root_order_key[anchor_unit];
    let nudge = 1e-9 * (1.0 + unit_draw(rng));
    out.root_order_key[moved_unit] = (anchor_key + nudge).clamp(0.0, 1.0);
    out
}

/// Reverse a contiguous run of decoded unit positions (segment reverse),
/// re-expressed as a key permutation over the decoded order.
fn unit_reverse_neighbor(base: &Genome, rng: &mut u64) -> Genome {
    let n = base.root_order_key.len();
    if n < 3 {
        return base.clone();
    }
    let order = super::decode::decode_unit_order(&base.root_order_key);
    let i = draw_index(rng, n);
    let len = 2 + draw_index(rng, n - 2); // length in [2, n]
    let end = (i + len).min(n);
    let mut keys: Vec<f64> = order.iter().map(|&u| base.root_order_key[u]).collect();
    keys[i..end].reverse();
    let mut out = base.clone();
    for (pos, &unit) in order.iter().enumerate() {
        out.root_order_key[unit] = keys[pos];
    }
    out
}

// ── SA acceptance ────────────────────────────────────────────────────────────

/// Read-traffic-scale initial temperature, cooling linearly to 0 as the eval
/// budget is spent (mirrors the prototype's `sa_temperature`,
/// metaheuristic.rs:5156).
const SA_INITIAL_TEMPERATURE: f64 = 4.0;

fn sa_temperature(evals_used: usize, eval_budget: usize) -> f64 {
    if eval_budget == 0 {
        return 0.0;
    }
    let frac = (evals_used as f64 / eval_budget as f64).min(1.0);
    SA_INITIAL_TEMPERATURE * (1.0 - frac)
}

fn metropolis_accepts(delta: f64, temperature: f64, draw: f64) -> bool {
    if delta <= 0.0 {
        return true; // improving or equal always accepted
    }
    if temperature <= 0.0 {
        return false;
    }
    let p = (-delta / temperature).exp();
    draw < p
}

// ── search loop ──────────────────────────────────────────────────────────────

/// Search one layer: seed a population of `cfg.pop` genomes (neutral,
/// reversed-neutral, then seeded-random), then spend the remaining eval budget
/// running independent SA/hill-climb walks from each seed, tracking the global
/// best. Deterministic given `cfg.seed` — no `HashMap`/`HashSet` iteration in
/// the hot path; moves draw from an explicit `u64` RNG state, gene arrays are
/// `Vec`s, and [`CandidateScore`]'s `derive(Ord)` gives an explicit total order
/// (no float `NaN` — `score` always returns finite `usize` fields).
pub fn search_layer(ctx: &LayerCtx, cfg: &SearchConfig) -> LayerSearchOutcome {
    let start = Instant::now();
    let n_units = ctx.n_order_keys();
    let n_sites = ctx.n_sites();

    if n_units == 0 {
        // No atom roots: nothing to schedule. Empty, valid schedule.
        return LayerSearchOutcome {
            schedule: LayerSchedule { order: vec![], sites: vec![], predicted_traffic: 0, floor: ctx.floor },
            compiles: 0,
            wall: start.elapsed(),
        };
    }

    let mut rng = cfg.seed;
    let pop = cfg.pop.max(1);

    // Seed population: neutral, reversed-neutral, then seeded-random genomes.
    let mut population: Vec<Genome> = Vec::with_capacity(pop);
    population.push(Genome::neutral(n_units, n_sites));
    if pop > 1 {
        let mut reversed = Genome::neutral(n_units, n_sites);
        reversed.root_order_key.reverse();
        population.push(reversed);
    }
    while population.len() < pop {
        let mut g = Genome::neutral(n_units, n_sites);
        for k in &mut g.root_order_key {
            *k = unit_draw(&mut rng);
        }
        for c in &mut g.cache_priority {
            *c = (unit_draw(&mut rng) - 0.5) * 2.0;
        }
        population.push(g);
    }

    let mut compiles = 0usize;
    let mut scored: Vec<(Genome, CandidateScore)> = population
        .into_iter()
        .map(|g| {
            let s = score(&g, ctx);
            compiles += 1;
            (g, s)
        })
        .collect();

    let mut best = scored[argmin(&scored)].clone();

    while compiles < cfg.evals {
        for i in 0..scored.len() {
            if compiles >= cfg.evals {
                break;
            }
            let (cur_genome, _cur_score) = scored[i].clone();
            let candidate = random_neighbor(&cur_genome, &mut rng);
            let candidate_score = score(&candidate, ctx);
            compiles += 1;

            let delta = objective_delta(&candidate_score, &scored[i].1);
            let temperature = sa_temperature(compiles, cfg.evals);
            let draw = unit_draw(&mut rng);
            if metropolis_accepts(delta, temperature, draw) {
                scored[i] = (candidate, candidate_score);
            }
            if scored[i].1 < best.1 {
                best = scored[i].clone();
            }
        }
    }
    let final_best_idx = argmin(&scored);
    if scored[final_best_idx].1 < best.1 {
        best = scored[final_best_idx].clone();
    }

    let (best_genome, best_score) = best;
    let mut schedule = super::scorer::decode_schedule(&best_genome, ctx);
    schedule.predicted_traffic = if best_score.infeasible { 0 } else { best_score.dram_traffic };

    LayerSearchOutcome { schedule, compiles, wall: start.elapsed() }
}

fn argmin(scored: &[(Genome, CandidateScore)]) -> usize {
    let mut best = 0;
    for i in 1..scored.len() {
        if scored[i].1 < scored[best].1 {
            best = i;
        }
    }
    best
}

/// Signed objective delta as `f64` (for Metropolis) — `infeasible` candidates
/// are treated as "vastly worse" via explicit `+-infinity`, not by comparing
/// `usize::MAX` sentinels numerically (which would silently saturate/cancel in
/// `f64` arithmetic for large feasible traffic values too).
fn objective_delta(candidate: &CandidateScore, current: &CandidateScore) -> f64 {
    match (candidate.infeasible, current.infeasible) {
        (true, true) => 0.0,
        (true, false) => f64::INFINITY,
        (false, true) => f64::NEG_INFINITY,
        (false, false) => {
            let cand = (candidate.dram_traffic as f64) * 1e6 + candidate.instrs as f64;
            let curr = (current.dram_traffic as f64) * 1e6 + current.instrs as f64;
            cand - curr
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn search_config_defaults_are_sane() {
        let cfg = SearchConfig::default();
        assert!(cfg.pop >= 1);
        assert!(cfg.evals >= cfg.pop);
    }

    #[test]
    fn splitmix64_is_deterministic_and_varies() {
        let mut a = 42u64;
        let mut b = 42u64;
        let xa = splitmix64(&mut a);
        let xb = splitmix64(&mut b);
        assert_eq!(xa, xb);
        let ya = splitmix64(&mut a);
        assert_ne!(xa, ya);
    }

    #[test]
    fn unit_draw_is_in_unit_interval_and_deterministic() {
        let mut a = 7u64;
        let mut b = 7u64;
        let da = unit_draw(&mut a);
        let db = unit_draw(&mut b);
        assert_eq!(da, db);
        assert!((0.0..1.0).contains(&da));
    }

    #[test]
    fn sa_temperature_starts_hot_and_cools_to_zero() {
        assert_eq!(sa_temperature(0, 100), SA_INITIAL_TEMPERATURE);
        assert_eq!(sa_temperature(100, 100), 0.0);
        assert!(sa_temperature(50, 100) < SA_INITIAL_TEMPERATURE);
    }

    #[test]
    fn metropolis_rejects_worse_candidate_at_zero_temperature() {
        assert!(!metropolis_accepts(1.0, 0.0, 0.0));
    }

    #[test]
    fn metropolis_always_accepts_improving_or_equal() {
        assert!(metropolis_accepts(0.0, 1.0, 0.999));
        assert!(metropolis_accepts(-5.0, 1.0, 0.999));
    }

    #[test]
    fn metropolis_accepts_worse_candidate_when_draw_below_boltzmann_probability() {
        // delta=1, temp=1 -> p = e^-1 ~= 0.3679
        assert!(metropolis_accepts(1.0, 1.0, 0.1));
        assert!(!metropolis_accepts(1.0, 1.0, 0.9));
    }

    #[test]
    fn objective_delta_treats_infeasible_as_worse_than_any_feasible() {
        let feasible = CandidateScore { infeasible: false, dram_traffic: 1_000_000, instrs: 1_000_000 };
        let infeasible = CandidateScore { infeasible: true, dram_traffic: 0, instrs: 0 };
        assert_eq!(objective_delta(&infeasible, &feasible), f64::INFINITY);
        assert_eq!(objective_delta(&feasible, &infeasible), f64::NEG_INFINITY);
    }

    #[test]
    fn unit_swap_neighbor_only_touches_order_keys() {
        let base = Genome::neutral(4, 2);
        let mut rng = 3u64;
        let neighbor = unit_swap_neighbor(&base, &mut rng);
        assert_eq!(neighbor.cache_priority, base.cache_priority);
        assert_ne!(neighbor.root_order_key, base.root_order_key);
    }
}
