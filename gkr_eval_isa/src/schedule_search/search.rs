//! Compile-in-loop metaheuristic search (Task 6 promotion of
//! `gkr_eval_isa/tests/s3_planner/metaheuristic.rs`'s population/beam/
//! simulated-annealing optimizer, which lived entirely inside that test-only
//! module). The algorithm's architecture is ported 1:1 — deterministic
//! neighbor-batch greedy descent (unit swap / insert / segment-reverse order
//! moves + per-gene cache-priority nudges), a budget-scaled beam over scored
//! seed states, plateau-limited sideways cache moves, and a Metropolis
//! simulated-annealing escape from stalled states — but the fitness function is
//! the REAL compile ([`super::scorer::score`]) instead of the deleted `Replay`
//! event simulation.
//!
//! Deleted with the simulation (no successor here): the trace-guided
//! cache-neighbor family (`push_trace_guided_cache_neighbors`) consumed the
//! `Replay` engine's `CacheTrace` events; the compile path exposes no such
//! trace, so that move family dies with the simulator. The order/bias move
//! families and the whole selection/beam/SA loop survive unchanged.
//!
//! Determinism: neighbor enumeration is a fixed deterministic order, parallel
//! scoring preserves entry indices, all tie-breaks are `(objective, index)`,
//! and the SA draw is a stateless `splitmix64` hash of the eval counter —
//! repeated runs with the same `SearchConfig` produce identical results.

use std::time::{Duration, Instant};

use cs::gkr_compiler::dag_ir::LayerSchedule;

use super::decode::decode_unit_order;
use super::genome::{assert_normalized_genome, clamp_bias, Genome};
use super::scorer::{objective_key, score, CandidateScore, LayerCtx};

// ── Tuning constants (values carried over from the prototype) ────────────────

/// Local cache-priority mutation step (prototype `LOCAL_BIAS_STEP`).
const LOCAL_BIAS_STEP: f64 = 0.25;
/// Per-batch cap on reserved cache-priority slots (prototype `CACHE_FAMILY_QUOTA`).
const CACHE_FAMILY_QUOTA: usize = 64;
/// Sideways (equal-objective) cache moves allowed before a plateau stalls
/// (prototype `CACHE_PLATEAU_STEPS`).
const CACHE_PLATEAU_STEPS: usize = 4;
/// Maximum beam width (cap); effective width scales with the eval budget — see
/// `beam_width_for_budget` (prototype `OPTIMIZER_BEAM_WIDTH`).
const OPTIMIZER_BEAM_WIDTH: usize = 8;
/// Per-state convergence budget: open at most one beam state per this many
/// evals (prototype `BEAM_STATE_MIN_BUDGET`; empirically a single greedy
/// descent converges within ~1000 evals — under-funded beams dilute and
/// regress).
const BEAM_STATE_MIN_BUDGET: usize = 1_000;
/// Fixed per-iteration neighbor-batch cap, INDEPENDENT of the eval budget
/// (prototype H3): the unit-insert family is O(units^2); without a fixed cap
/// one batch at production scale consumes the whole budget and the search
/// degenerates to a single greedy step.
const NEIGHBOR_BATCH_CAP: usize = 128;
/// Simulated-annealing initial temperature in read-traffic units; cools
/// linearly to 0 as the budget is spent (prototype `SA_INITIAL_TEMPERATURE`).
const SA_INITIAL_TEMPERATURE: f64 = 4.0;

// ── SearchConfig (env-overridable, same contract as the deleted v1 producer) ─

/// Search knobs. Env overrides (checked by [`search_config_from_env`]):
/// `GKR_SCHEDULE_POP` / `GKR_SCHEDULE_EVALS` / `GKR_SCHEDULE_SEED` — the same
/// variable names (and validation) the deleted v1 producer used
/// (`s3_gap_experiment.rs`'s `schedule_search_config_from_env`, removed with
/// the v1 schema in Task 4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SearchConfig {
    pub pop: usize,
    pub evals: usize,
    pub seed: u64,
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self { pop: 8, evals: 1000, seed: 0 }
    }
}

fn parse_usize_env(name: &str, default: usize) -> usize {
    match std::env::var(name) {
        Ok(raw) => raw
            .parse::<usize>()
            .unwrap_or_else(|_| panic!("{name} must be a usize, got {raw:?}")),
        Err(std::env::VarError::NotPresent) => default,
        Err(err) => panic!("failed to read {name}: {err}"),
    }
}

fn parse_u64_env(name: &str, default: u64) -> u64 {
    match std::env::var(name) {
        Ok(raw) => raw
            .parse::<u64>()
            .unwrap_or_else(|_| panic!("{name} must be a u64, got {raw:?}")),
        Err(std::env::VarError::NotPresent) => default,
        Err(err) => panic!("failed to read {name}: {err}"),
    }
}

/// [`SearchConfig`] from the environment, with the v1 producer's validation:
/// malformed values PANIC (a silently-ignored typo in a regen run would burn
/// hours), `pop`/`evals` must be positive and `pop < evals`.
pub fn search_config_from_env() -> SearchConfig {
    let defaults = SearchConfig::default();
    let cfg = SearchConfig {
        pop: parse_usize_env("GKR_SCHEDULE_POP", defaults.pop),
        evals: parse_usize_env("GKR_SCHEDULE_EVALS", defaults.evals),
        seed: parse_u64_env("GKR_SCHEDULE_SEED", defaults.seed),
    };
    assert!(cfg.pop > 0, "GKR_SCHEDULE_POP must be positive");
    assert!(cfg.evals > 0, "GKR_SCHEDULE_EVALS must be positive");
    assert!(cfg.pop < cfg.evals, "GKR_SCHEDULE_POP must be < GKR_SCHEDULE_EVALS");
    cfg
}

// ── Outcome types ─────────────────────────────────────────────────────────────

/// Result of searching one layer: the winning `LayerSchedule` (already
/// `predicted_traffic`-stamped from the winning compile) plus the perf-envelope
/// counters the producer prints.
pub struct LayerSearchOutcome {
    pub schedule: LayerSchedule,
    pub compiles: usize,
    pub wall: Duration,
}

/// Winning genome + score of one optimizer run (prototype `OptimizerResult`,
/// minus the move-family bookkeeping counters that only fed its smoke-test
/// report formatting).
pub struct OptimizerResult {
    pub best_genome: Genome,
    pub best_score: CandidateScore,
    pub evals: usize,
    pub iterations: usize,
    pub beam_states: usize,
}

// ── Deterministic RNG helpers (prototype splitmix64 / unit_draw / SmokeRng) ──

fn splitmix64(seed: u64) -> u64 {
    let mut z = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Deterministic sample in `[0, 1)` from a seed (top 53 bits of a splitmix64
/// hash) — keeps the optimizer's annealing reproducible across runs.
fn unit_draw(seed: u64) -> f64 {
    (splitmix64(seed) >> 11) as f64 / (1u64 << 53) as f64
}

/// Stateful LCG for the random seed-population tail (prototype `SmokeRng`,
/// same constants).
struct SeedRng {
    state: u64,
}

impl SeedRng {
    fn new(seed: u64) -> Self {
        Self { state: seed ^ 0x9e37_79b9_7f4a_7c15 }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }

    fn next_unit(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 * (1.0 / ((1u64 << 53) as f64))
    }

    fn next_signed(&mut self) -> f64 {
        self.next_unit() * 2.0 - 1.0
    }
}

// ── Objective ordering ────────────────────────────────────────────────────────

fn objective_less(a: &CandidateScore, b: &CandidateScore) -> bool {
    objective_key(a) < objective_key(b)
}

/// One scored candidate in a batch; `index` is the enumeration index (the
/// deterministic tie-break).
#[derive(Clone, Debug)]
struct ScoredGenome {
    index: usize,
    genome: Genome,
    score: CandidateScore,
    family: Option<MoveFamily>,
}

fn scored_less(a: &ScoredGenome, b: &ScoredGenome) -> bool {
    objective_key(&a.score)
        .cmp(&objective_key(&b.score))
        .then(a.index.cmp(&b.index))
        .is_lt()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MoveFamily {
    UnitSwap,
    UnitInsert,
    UnitReverse,
    CachePriority,
}

fn is_cache_move_family(family: MoveFamily) -> bool {
    matches!(family, MoveFamily::CachePriority)
}

// ── Neighbor moves (unit-keyed; prototype's grouped move families) ───────────

/// Genome whose unit-key order equals `order` (rank/denom along it) —
/// prototype `genome_with_unit_order`.
fn genome_with_unit_order(base: &Genome, order: &[usize]) -> Genome {
    let mut candidate = base.clone();
    let denom = order.len().max(1) as f64;
    for (rank, &unit) in order.iter().enumerate() {
        candidate.root_order_key[unit] = rank as f64 / denom;
    }
    candidate
}

fn push_unit_swap_neighbors(
    base: &Genome,
    limit: usize,
    out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
) {
    let order = decode_unit_order(&base.root_order_key);
    for pair in order.windows(2) {
        if out.len() >= limit {
            return;
        }
        let mut candidate = base.clone();
        candidate.root_order_key.swap(pair[0], pair[1]);
        out.push((out.len(), candidate, Some(MoveFamily::UnitSwap)));
    }
}

fn push_unit_insert_neighbors(
    base: &Genome,
    limit: usize,
    out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
) {
    let order = decode_unit_order(&base.root_order_key);
    for from in 0..order.len() {
        for to in 0..order.len() {
            if out.len() >= limit {
                return;
            }
            if from == to || from.abs_diff(to) == 1 {
                continue;
            }
            let mut inserted = order.clone();
            let unit = inserted.remove(from);
            inserted.insert(to, unit);
            out.push((out.len(), genome_with_unit_order(base, &inserted), Some(MoveFamily::UnitInsert)));
        }
    }
}

fn push_unit_reverse_neighbors(
    base: &Genome,
    limit: usize,
    out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
) {
    // 2-opt over units: reverse a contiguous run of the unit order (runs of
    // length 2 are skipped — reversing an adjacent pair is exactly a unit swap).
    let order = decode_unit_order(&base.root_order_key);
    let n = order.len();
    for i in 0..n {
        for j in (i + 2)..n {
            if out.len() >= limit {
                return;
            }
            let mut reversed = order.clone();
            reversed[i..=j].reverse();
            out.push((out.len(), genome_with_unit_order(base, &reversed), Some(MoveFamily::UnitReverse)));
        }
    }
}

fn push_cache_priority_neighbors(
    base: &Genome,
    limit: usize,
    out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
) {
    for idx in 0..base.cache_priority.len() {
        for delta in [-LOCAL_BIAS_STEP, LOCAL_BIAS_STEP] {
            if out.len() >= limit {
                return;
            }
            let mut candidate = base.clone();
            candidate.cache_priority[idx] = clamp_bias(candidate.cache_priority[idx] + delta);
            out.push((out.len(), candidate, Some(MoveFamily::CachePriority)));
        }
    }
}

fn has_unit_insert_neighbors(n_units: usize) -> bool {
    n_units >= 3
}

fn has_cache_priority_neighbors(base: &Genome) -> bool {
    !base.cache_priority.is_empty()
}

/// Slots reserved for the cache-priority family within a `remaining`-sized
/// batch (prototype `reserved_cache_slots`, re-typed to unit counts).
fn reserved_cache_slots(n_units: usize, base: &Genome, remaining: usize) -> usize {
    let active = usize::from(has_cache_priority_neighbors(base));
    if active == 0 || remaining == 0 {
        return 0;
    }
    let fractional_cap = (remaining / 4).max(active).min(remaining);
    let mut slots = fractional_cap.min(active * CACHE_FAMILY_QUOTA);
    if has_unit_insert_neighbors(n_units) && remaining > active && slots == remaining {
        slots -= 1;
    }
    slots
}

/// One deterministic neighbor batch around `base`, capped at `limit`
/// (prototype `neighbor_entries`, unit-keyed arm; the trace-guided cache
/// family is deleted with the `Replay` simulator — see module doc).
fn neighbor_entries(
    n_units: usize,
    base: &Genome,
    limit: usize,
) -> Vec<(usize, Genome, Option<MoveFamily>)> {
    let mut out = Vec::with_capacity(limit);
    push_unit_swap_neighbors(base, limit, &mut out);
    let cache_slots = reserved_cache_slots(n_units, base, limit.saturating_sub(out.len()));
    push_unit_insert_neighbors(base, limit - cache_slots, &mut out);
    push_unit_reverse_neighbors(base, limit - cache_slots, &mut out);
    push_cache_priority_neighbors(base, limit, &mut out);
    out
}

// ── Parallel candidate scoring ────────────────────────────────────────────────

fn default_worker_count() -> usize {
    std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1)
}

/// Score a batch of candidates in parallel, preserving entry order (results are
/// re-sorted by `index`, so parallelism never changes selection). A scorer
/// panic (its non-`BudgetBelowFloor` bug guard) is re-raised on the caller's
/// thread with its original payload.
fn score_genomes_parallel(
    ctx: &LayerCtx,
    entries: Vec<(usize, Genome, Option<MoveFamily>)>,
    workers: usize,
) -> Vec<ScoredGenome> {
    if entries.is_empty() {
        return Vec::new();
    }
    let worker_count = workers.max(1).min(entries.len());
    let chunk_size = entries.len().div_ceil(worker_count);
    let mut chunks: Vec<Vec<(usize, Genome, Option<MoveFamily>)>> = Vec::with_capacity(worker_count);
    let mut current = Vec::with_capacity(chunk_size);
    for entry in entries {
        current.push(entry);
        if current.len() == chunk_size {
            chunks.push(current);
            current = Vec::with_capacity(chunk_size);
        }
    }
    if !current.is_empty() {
        chunks.push(current);
    }

    let mut scored = std::thread::scope(|scope| {
        let handles: Vec<_> = chunks
            .into_iter()
            .map(|chunk| {
                scope.spawn(move || {
                    chunk
                        .into_iter()
                        .map(|(index, genome, family)| {
                            let score = score(&genome, ctx);
                            ScoredGenome { index, genome, score, family }
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|handle| match handle.join() {
                Ok(v) => v,
                // Preserve the scorer's genome-dump panic payload.
                Err(payload) => std::panic::resume_unwind(payload),
            })
            .collect::<Vec<_>>()
    });
    scored.sort_by_key(|entry| entry.index);
    scored
}

// ── SA acceptance (prototype metropolis/sa_temperature/best_uphill) ──────────

/// Metropolis acceptance for a strictly-worse candidate. `delta > 0` is the
/// traffic increase. At `temperature <= 0` never accepts (pure hill-climbing).
fn metropolis_accepts(delta: f64, temperature: f64, draw: f64) -> bool {
    debug_assert!(delta > 0.0, "metropolis_accepts is only for strictly-worse candidates");
    if temperature <= 0.0 {
        return false;
    }
    draw < (-delta / temperature).exp()
}

/// Linear cooling from `SA_INITIAL_TEMPERATURE` to 0 over the eval budget.
fn sa_temperature(evals: usize, eval_budget: usize) -> f64 {
    if eval_budget == 0 {
        return 0.0;
    }
    let progress = (evals as f64 / eval_budget as f64).min(1.0);
    SA_INITIAL_TEMPERATURE * (1.0 - progress)
}

/// The gentlest feasible neighbor strictly worse in primary energy (traffic)
/// than `current` — the candidate an uphill SA step would move to. Ties break
/// on instrs then index. `None` if no such neighbor exists.
fn best_uphill_neighbor(scored: &[ScoredGenome], current: &CandidateScore) -> Option<usize> {
    scored
        .iter()
        .enumerate()
        .filter(|(_, entry)| !entry.score.infeasible && entry.score.dram_traffic > current.dram_traffic)
        .min_by(|a, b| {
            (a.1.score.dram_traffic, a.1.score.instrs, a.0)
                .cmp(&(b.1.score.dram_traffic, b.1.score.instrs, b.0))
        })
        .map(|(idx, _)| idx)
}

// ── Optimizer state machine (prototype beam + greedy + plateau + SA stop) ────

#[derive(Clone, Debug)]
struct OptimizerState {
    genome: Genome,
    score: CandidateScore,
    /// Decoded unit order, cached for the beam's order+objective dedup.
    unit_order: Vec<usize>,
    plateau_remaining: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OptimizerStep {
    Improving(usize),
    Sideways(usize),
    Stop,
}

fn select_optimizer_neighbor(
    scored: &[ScoredGenome],
    current: &CandidateScore,
    plateau_remaining: usize,
) -> OptimizerStep {
    let Some((idx, _)) = scored
        .iter()
        .enumerate()
        .filter(|(_, entry)| objective_less(&entry.score, current))
        .min_by(|(_, a), (_, b)| {
            objective_key(&a.score).cmp(&objective_key(&b.score)).then(a.index.cmp(&b.index))
        })
    else {
        if plateau_remaining == 0 {
            return OptimizerStep::Stop;
        }
        return scored
            .iter()
            .enumerate()
            .find(|(_, entry)| {
                entry.family.is_some_and(is_cache_move_family)
                    && objective_key(&entry.score) == objective_key(current)
            })
            .map(|(idx, _)| OptimizerStep::Sideways(idx))
            .unwrap_or(OptimizerStep::Stop);
    };
    OptimizerStep::Improving(idx)
}

/// Budget-proportional beam width (prototype `beam_width_for_budget`).
fn beam_width_for_budget(eval_budget: usize) -> usize {
    (eval_budget / BEAM_STATE_MIN_BUDGET).clamp(1, OPTIMIZER_BEAM_WIDTH)
}

fn optimizer_beam_from_seed_scores(mut scored: Vec<ScoredGenome>, beam_width: usize) -> Vec<OptimizerState> {
    assert!(beam_width > 0, "beam width must be positive");
    scored.sort_by(|a, b| {
        objective_key(&a.score).cmp(&objective_key(&b.score)).then(a.index.cmp(&b.index))
    });
    let mut states: Vec<OptimizerState> = Vec::with_capacity(beam_width.min(scored.len()));
    for entry in scored {
        if states.len() >= beam_width {
            break;
        }
        // Dedup by decoded order + objective, NOT byte-equal genome: random-key
        // seeds that decode to the same order are redundant starts (identical
        // greedy neighborhood).
        let unit_order = decode_unit_order(&entry.genome.root_order_key);
        if states.iter().any(|state| {
            state.unit_order == unit_order && objective_key(&state.score) == objective_key(&entry.score)
        }) {
            continue;
        }
        states.push(OptimizerState {
            genome: entry.genome,
            score: entry.score,
            unit_order,
            plateau_remaining: CACHE_PLATEAU_STEPS,
        });
    }
    states
}

/// Advance one beam state by one neighbor batch. Returns whether the state
/// stays live (prototype `advance_optimizer_state`, minus the move-family
/// report counters).
#[allow(clippy::too_many_arguments)]
fn advance_optimizer_state(
    ctx: &LayerCtx,
    state: &mut OptimizerState,
    eval_budget: usize,
    evals: &mut usize,
    best_genome: &mut Genome,
    best_score: &mut CandidateScore,
) -> bool {
    if *evals >= eval_budget {
        return false;
    }
    let n_units = ctx.n_order_keys();
    // H3: cap each batch to a FIXED branching factor, independent of the
    // remaining budget (see NEIGHBOR_BATCH_CAP).
    let remaining = (eval_budget - *evals).min(NEIGHBOR_BATCH_CAP);
    let neighbors = neighbor_entries(n_units, &state.genome, remaining);
    if neighbors.is_empty() {
        return false;
    }
    *evals += neighbors.len();
    let neighbor_scores = score_genomes_parallel(ctx, neighbors, default_worker_count());

    let mut adopt = |state: &mut OptimizerState, selected: ScoredGenome| {
        state.unit_order = decode_unit_order(&selected.genome.root_order_key);
        state.genome = selected.genome;
        state.score = selected.score;
    };

    match select_optimizer_neighbor(&neighbor_scores, &state.score, state.plateau_remaining) {
        OptimizerStep::Improving(idx) => {
            adopt(state, neighbor_scores[idx].clone());
            state.plateau_remaining = CACHE_PLATEAU_STEPS;
            if objective_less(&state.score, best_score) {
                *best_genome = state.genome.clone();
                *best_score = state.score;
            }
            true
        }
        OptimizerStep::Sideways(idx) => {
            adopt(state, neighbor_scores[idx].clone());
            state.plateau_remaining = state.plateau_remaining.saturating_sub(1);
            true
        }
        OptimizerStep::Stop => {
            // Simulated annealing: rather than abandon a stalled state, accept
            // the gentlest feasible uphill move with Metropolis probability so
            // the search can escape this local optimum. The global best is
            // preserved (this move is strictly worse); the temperature cools to
            // 0 as the budget is spent, annealing back to hill-climbing.
            let temperature = sa_temperature(*evals, eval_budget);
            let Some(idx) = best_uphill_neighbor(&neighbor_scores, &state.score) else {
                return false;
            };
            let delta = (neighbor_scores[idx].score.dram_traffic - state.score.dram_traffic) as f64;
            if !metropolis_accepts(delta, temperature, unit_draw(*evals as u64)) {
                return false;
            }
            adopt(state, neighbor_scores[idx].clone());
            state.plateau_remaining = CACHE_PLATEAU_STEPS;
            true
        }
    }
}

/// Beam-of-greedy-descents optimizer over compile-scored candidates (prototype
/// `optimize_from_population_grouped`; the genome here is ALWAYS unit-keyed —
/// there is no flat per-occurrence arm anymore, `relation_units` partitions
/// every layer's atom roots).
pub fn optimize_from_population(ctx: &LayerCtx, seeds: Vec<Genome>, eval_budget: usize) -> OptimizerResult {
    assert!(eval_budget > 0, "eval_budget must be positive");

    let seeds = if seeds.is_empty() {
        vec![Genome::neutral(ctx.n_order_keys(), ctx.n_sites())]
    } else {
        seeds
    };
    for genome in &seeds {
        assert_normalized_genome(genome);
    }
    let seed_entries: Vec<_> = seeds
        .into_iter()
        .take(eval_budget)
        .enumerate()
        .map(|(index, genome)| (index, genome, None))
        .collect();
    let mut evals = seed_entries.len();
    let seed_scores = score_genomes_parallel(ctx, seed_entries, default_worker_count());

    let mut beam = optimizer_beam_from_seed_scores(seed_scores, beam_width_for_budget(eval_budget));
    let beam_states = beam.len();
    let mut best_genome = beam[0].genome.clone();
    let mut best_score = beam[0].score;
    let mut iterations = 0usize;

    // Round-robin: advance every live state once per round against the shared
    // eval budget and the shared global best. A stalled state is dropped so its
    // dead neighborhood is never re-scored.
    while evals < eval_budget && !beam.is_empty() {
        let mut next_beam = Vec::with_capacity(beam.len());
        let mut advanced_any = false;
        for mut state in beam.drain(..) {
            if evals >= eval_budget {
                next_beam.push(state);
                continue;
            }
            let before = evals;
            let moved = advance_optimizer_state(
                ctx,
                &mut state,
                eval_budget,
                &mut evals,
                &mut best_genome,
                &mut best_score,
            );
            if evals > before {
                iterations += 1;
            }
            if moved {
                advanced_any = true;
                next_beam.push(state);
            }
        }
        beam = next_beam;
        if !advanced_any {
            break;
        }
    }

    OptimizerResult { best_genome, best_score, evals, iterations, beam_states }
}

// ── Seed population (prototype seeded_smoke_population, DagLayer-native) ─────

/// Reuse-density-weighted seed: per-site bias = (layer-wide demand count of the
/// site's value / its cell width), normalized by the max density (prototype
/// `reuse_weighted_smoke_genome`'s density arm; its reload-vs-recompute
/// `CachedRootOutput` refinement needed the deleted `OracleInstance` cone
/// walk and is dropped — density alone carried most of the anchor's value).
fn reuse_weighted_genome(ctx: &LayerCtx) -> Genome {
    let mut genome = Genome::neutral(ctx.n_order_keys(), ctx.n_sites());
    if ctx.sites.is_empty() {
        return genome;
    }
    use std::collections::BTreeMap;
    let mut demand_count: BTreeMap<u32, u32> = BTreeMap::new();
    for site in &ctx.sites {
        *demand_count.entry(site.value.0).or_default() += 1;
    }
    let width = |value: u32| -> f64 {
        let f = crate::fwd::compile::expr_operand_field(
            ctx.layer,
            cs::gkr_compiler::dag_ir::ExprId(value),
            ctx.cross_layer_fields,
        );
        if f == crate::fwd::isa::OperandField::Ext {
            4.0
        } else {
            1.0
        }
    };
    let density = |value: u32| demand_count[&value] as f64 / width(value);
    let max_density = ctx.sites.iter().map(|s| density(s.value.0)).fold(0.0f64, f64::max);
    if max_density > 0.0 {
        for (gene, site) in genome.cache_priority.iter_mut().zip(&ctx.sites) {
            *gene = density(site.value.0) / max_density;
        }
    }
    genome
}

/// Seed population: neutral + reversed-neutral + reuse-weighted anchors, then a
/// deterministic random tail seeded from `run_offset` (prototype
/// `seeded_smoke_population`; `run_offset == 0` reproduces the historical
/// `smoke_genome_population` tail exactly).
pub fn seeded_population(ctx: &LayerCtx, total: usize, run_offset: u64) -> Vec<Genome> {
    let n_units = ctx.n_order_keys();
    let n_sites = ctx.n_sites();
    let mut genomes = Vec::with_capacity(total);
    if total == 0 {
        return genomes;
    }
    genomes.push(Genome::neutral(n_units, n_sites));
    if genomes.len() < total {
        let mut reversed = Genome::neutral(n_units, n_sites);
        let n = reversed.root_order_key.len();
        let denom = n.max(1) as f64;
        for (idx, key) in reversed.root_order_key.iter_mut().enumerate() {
            *key = (n - 1 - idx) as f64 / denom;
        }
        genomes.push(reversed);
    }
    if genomes.len() < total {
        genomes.push(reuse_weighted_genome(ctx));
    }
    while genomes.len() < total {
        let seed = run_offset
            .wrapping_mul(0x9E37_79B9_7F4A_7C15)
            .wrapping_add((genomes.len() - 3) as u64);
        let mut rng = SeedRng::new(seed);
        let mut genome = Genome::neutral(n_units, n_sites);
        for key in &mut genome.root_order_key {
            *key = rng.next_unit();
        }
        for bias in &mut genome.cache_priority {
            *bias = rng.next_signed();
        }
        genomes.push(genome);
    }
    genomes
}

// ── search_layer: the per-layer driver the producer calls ────────────────────

/// Search one layer: seed `cfg.pop` genomes, run the beam/greedy/SA optimizer
/// for `cfg.evals` compile-evals, and return the winning schedule stamped with
/// its own compile's traffic. Panics if even the best candidate is infeasible
/// at `ctx.budget` (an infeasible layer is a real problem, not a schedule —
/// the deleted v1 producer's F6 gate).
pub fn search_layer(ctx: &LayerCtx, cfg: &SearchConfig) -> LayerSearchOutcome {
    let start = Instant::now();

    if ctx.n_order_keys() == 0 {
        // No atom roots: nothing to schedule. Trivial empty (and trivially
        // valid) schedule; `floor: 0` mirrors the v1 producer's empty branch
        // (the validator requires floor <= predicted_traffic, and an
        // unsearched layer records no achieved traffic).
        return LayerSearchOutcome {
            schedule: LayerSchedule { order: vec![], sites: vec![], predicted_traffic: 0, floor: 0 },
            compiles: 0,
            wall: start.elapsed(),
        };
    }

    let seeds = seeded_population(ctx, cfg.pop.min(cfg.evals), cfg.seed);
    let opt = optimize_from_population(ctx, seeds, cfg.evals);
    assert!(
        !opt.best_score.infeasible,
        "search_layer: best candidate infeasible at budget {} ({} units, {} sites)",
        ctx.budget,
        ctx.n_order_keys(),
        ctx.n_sites()
    );

    let mut schedule = super::scorer::decode_schedule(&opt.best_genome, ctx);
    schedule.predicted_traffic = opt.best_score.dram_traffic;
    assert!(
        schedule.floor <= schedule.predicted_traffic,
        "search_layer: floor {} above achieved traffic {}",
        schedule.floor,
        schedule.predicted_traffic
    );

    LayerSearchOutcome { schedule, compiles: opt.evals, wall: start.elapsed() }
}

// ── Tests (ported subset of the prototype's search-mechanics suite) ──────────

#[cfg(test)]
mod tests {
    use super::*;

    fn feasible(traffic: usize, instrs: usize) -> CandidateScore {
        CandidateScore { infeasible: false, dram_traffic: traffic, instrs }
    }

    fn infeasible() -> CandidateScore {
        CandidateScore { infeasible: true, dram_traffic: usize::MAX, instrs: usize::MAX }
    }

    fn sg(index: usize, score: CandidateScore, family: Option<MoveFamily>) -> ScoredGenome {
        ScoredGenome { index, genome: Genome::neutral(2, 0), score, family }
    }

    // ── RNG / SA primitives ────────────────────────────────────────────────

    #[test]
    fn unit_draw_is_in_unit_interval_and_deterministic() {
        for seed in [0u64, 1, 42, u64::MAX] {
            let a = unit_draw(seed);
            let b = unit_draw(seed);
            assert_eq!(a, b);
            assert!((0.0..1.0).contains(&a));
        }
        assert_ne!(unit_draw(1), unit_draw(2));
    }

    #[test]
    fn sa_temperature_starts_hot_and_cools_to_zero() {
        assert_eq!(sa_temperature(0, 100), SA_INITIAL_TEMPERATURE);
        assert_eq!(sa_temperature(100, 100), 0.0);
        assert_eq!(sa_temperature(200, 100), 0.0, "past-budget clamps to 0");
        let mid = sa_temperature(50, 100);
        assert!(mid > 0.0 && mid < SA_INITIAL_TEMPERATURE);
    }

    #[test]
    fn metropolis_rejects_worse_candidate_at_zero_temperature() {
        assert!(!metropolis_accepts(1.0, 0.0, 0.0));
    }

    #[test]
    fn metropolis_accepts_worse_candidate_when_draw_below_boltzmann_probability() {
        // delta=1, temp=1 -> p = e^-1 ~= 0.3679
        assert!(metropolis_accepts(1.0, 1.0, 0.1));
        assert!(!metropolis_accepts(1.0, 1.0, 0.9));
    }

    #[test]
    fn metropolis_acceptance_probability_shrinks_as_temperature_cools() {
        let draw = 0.2;
        let hot = metropolis_accepts(1.0, 4.0, draw);
        let cold = metropolis_accepts(1.0, 0.1, draw);
        assert!(hot);
        assert!(!cold);
    }

    // ── uphill / selection ────────────────────────────────────────────────

    #[test]
    fn best_uphill_neighbor_picks_gentlest_feasible_worse_traffic() {
        let current = feasible(10, 10);
        let scored = vec![
            sg(0, feasible(15, 1), None),
            sg(1, feasible(12, 9), None), // gentlest uphill
            sg(2, feasible(12, 5), None), // same traffic, fewer instrs -> preferred
            sg(3, infeasible(), None),
        ];
        assert_eq!(best_uphill_neighbor(&scored, &current), Some(2));
    }

    #[test]
    fn best_uphill_neighbor_ignores_improving_equal_and_infeasible() {
        let current = feasible(10, 10);
        let scored = vec![
            sg(0, feasible(9, 1), None),  // improving
            sg(1, feasible(10, 99), None), // equal traffic
            sg(2, infeasible(), None),
        ];
        assert_eq!(best_uphill_neighbor(&scored, &current), None);
    }

    #[test]
    fn plateau_selection_accepts_equal_cache_neighbor_when_budget_remains() {
        let current = feasible(10, 10);
        let scored = vec![
            sg(0, feasible(11, 10), Some(MoveFamily::UnitSwap)),
            sg(1, feasible(10, 10), Some(MoveFamily::CachePriority)),
        ];
        assert_eq!(select_optimizer_neighbor(&scored, &current, 2), OptimizerStep::Sideways(1));
        assert_eq!(select_optimizer_neighbor(&scored, &current, 0), OptimizerStep::Stop);
    }

    #[test]
    fn plateau_selection_prefers_strict_improvement_over_sideways_cache_neighbor() {
        let current = feasible(10, 10);
        let scored = vec![
            sg(0, feasible(10, 10), Some(MoveFamily::CachePriority)),
            sg(1, feasible(9, 20), Some(MoveFamily::UnitInsert)),
        ];
        assert_eq!(select_optimizer_neighbor(&scored, &current, 2), OptimizerStep::Improving(1));
    }

    #[test]
    fn sideways_moves_only_come_from_the_cache_family() {
        let current = feasible(10, 10);
        let scored = vec![sg(0, feasible(10, 10), Some(MoveFamily::UnitSwap))];
        assert_eq!(select_optimizer_neighbor(&scored, &current, 4), OptimizerStep::Stop);
    }

    // ── beam ──────────────────────────────────────────────────────────────

    #[test]
    fn beam_width_scales_with_budget_to_avoid_dilution() {
        assert_eq!(beam_width_for_budget(0), 1);
        assert_eq!(beam_width_for_budget(999), 1);
        assert_eq!(beam_width_for_budget(2_000), 2);
        assert_eq!(beam_width_for_budget(1_000_000), OPTIMIZER_BEAM_WIDTH);
    }

    #[test]
    fn optimizer_beam_keeps_multiple_scored_seed_states() {
        // Distinct decoded orders -> distinct states, best objective first.
        let mut a = Genome::neutral(2, 0);
        a.root_order_key = vec![0.0, 0.5];
        let mut b = Genome::neutral(2, 0);
        b.root_order_key = vec![0.5, 0.0];
        let scored = vec![
            ScoredGenome { index: 0, genome: a, score: feasible(12, 0), family: None },
            ScoredGenome { index: 1, genome: b, score: feasible(10, 0), family: None },
        ];
        let beam = optimizer_beam_from_seed_scores(scored, 4);
        assert_eq!(beam.len(), 2);
        assert_eq!(beam[0].score, feasible(10, 0), "best objective first");
    }

    #[test]
    fn optimizer_beam_dedups_states_with_equal_order_and_objective() {
        // Byte-DIFFERENT genomes decoding to the SAME order with the same
        // objective collapse to one state.
        let mut a = Genome::neutral(2, 0);
        a.root_order_key = vec![0.1, 0.9];
        let mut b = Genome::neutral(2, 0);
        b.root_order_key = vec![0.2, 0.8]; // same decoded order (0, 1)
        let scored = vec![
            ScoredGenome { index: 0, genome: a, score: feasible(10, 0), family: None },
            ScoredGenome { index: 1, genome: b, score: feasible(10, 0), family: None },
        ];
        let beam = optimizer_beam_from_seed_scores(scored, 4);
        assert_eq!(beam.len(), 1);
    }

    // ── neighbor families ─────────────────────────────────────────────────

    #[test]
    fn unit_swap_neighbors_swap_adjacent_decoded_positions() {
        let base = Genome::neutral(3, 0);
        let mut out = Vec::new();
        push_unit_swap_neighbors(&base, usize::MAX, &mut out);
        assert_eq!(out.len(), 2, "n-1 adjacent pairs");
        // First neighbor swaps decoded positions 0 and 1.
        let n0 = decode_unit_order(&out[0].1.root_order_key);
        assert_eq!(n0, vec![1, 0, 2]);
        assert!(out.iter().all(|(_, _, f)| *f == Some(MoveFamily::UnitSwap)));
    }

    #[test]
    fn unit_insert_neighbors_skip_identity_and_adjacent_moves() {
        let base = Genome::neutral(4, 0);
        let mut out = Vec::new();
        push_unit_insert_neighbors(&base, usize::MAX, &mut out);
        // from,to pairs with from != to and |from-to| != 1: 4*4 - 4 - 6 = 6.
        assert_eq!(out.len(), 6);
        for (_, genome, _) in &out {
            let order = decode_unit_order(&genome.root_order_key);
            assert_ne!(order, vec![0, 1, 2, 3], "insert must change the decoded order");
        }
    }

    #[test]
    fn unit_reverse_neighbors_reverse_runs_of_length_three_or_more() {
        let base = Genome::neutral(4, 0);
        let mut out = Vec::new();
        push_unit_reverse_neighbors(&base, usize::MAX, &mut out);
        // (i, j) with j >= i+2 over n=4: (0,2),(0,3),(1,3) = 3.
        assert_eq!(out.len(), 3);
        let orders: Vec<Vec<usize>> =
            out.iter().map(|(_, g, _)| decode_unit_order(&g.root_order_key)).collect();
        assert!(orders.contains(&vec![2, 1, 0, 3]));
        assert!(orders.contains(&vec![3, 2, 1, 0]));
        assert!(orders.contains(&vec![0, 3, 2, 1]));
    }

    #[test]
    fn cache_priority_neighbors_step_each_gene_both_ways_clamped() {
        let mut base = Genome::neutral(1, 2);
        base.cache_priority = vec![0.0, 1.0];
        let mut out = Vec::new();
        push_cache_priority_neighbors(&base, usize::MAX, &mut out);
        assert_eq!(out.len(), 4);
        assert_eq!(out[0].1.cache_priority, vec![-LOCAL_BIAS_STEP, 1.0]);
        assert_eq!(out[1].1.cache_priority, vec![LOCAL_BIAS_STEP, 1.0]);
        assert_eq!(out[2].1.cache_priority, vec![0.0, 1.0 - LOCAL_BIAS_STEP]);
        assert_eq!(out[3].1.cache_priority, vec![0.0, 1.0], "+step clamps at the bias bound");
    }

    #[test]
    fn neighbor_batch_reserves_slots_for_cache_bias_families() {
        // Many units so order moves alone could saturate the batch; the
        // reserved cache slots must still admit cache-priority neighbors.
        let base = Genome::neutral(20, 4);
        let batch = neighbor_entries(20, &base, 64);
        assert!(batch.len() <= 64);
        assert!(
            batch.iter().any(|(_, _, f)| *f == Some(MoveFamily::CachePriority)),
            "cache-priority family must get reserved slots in a saturated batch"
        );
    }

    #[test]
    fn neighbor_entries_respects_limit_exactly() {
        let base = Genome::neutral(20, 4);
        for limit in [1usize, 8, 32, 128] {
            assert!(neighbor_entries(20, &base, limit).len() <= limit);
        }
    }

    #[test]
    fn reserved_cache_slots_zero_without_cache_genes() {
        let base = Genome::neutral(4, 0);
        assert_eq!(reserved_cache_slots(4, &base, 100), 0);
        let with_genes = Genome::neutral(4, 3);
        assert!(reserved_cache_slots(4, &with_genes, 100) > 0);
    }

    // ── seeds / config ────────────────────────────────────────────────────

    #[test]
    fn seed_rng_tail_stays_in_normalized_ranges() {
        let mut rng = SeedRng::new(7);
        for _ in 0..1000 {
            let u = rng.next_unit();
            assert!((0.0..1.0).contains(&u));
            let s = rng.next_signed();
            assert!((-1.0..=1.0).contains(&s));
        }
    }

    #[test]
    fn search_config_defaults_match_deleted_v1_producer() {
        let cfg = SearchConfig::default();
        assert_eq!(cfg, SearchConfig { pop: 8, evals: 1000, seed: 0 });
    }
}
