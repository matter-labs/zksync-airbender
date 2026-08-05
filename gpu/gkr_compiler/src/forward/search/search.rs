//! Compile-in-loop generational memetic GA (Phase 2). Replaces the earlier
//! beam local-descent + simulated-annealing driver: each generation carries the
//! best `elitism` genomes unchanged, then breeds the rest by tournament
//! selection + BLX-alpha crossover + per-gene Gaussian mutation, and hill-climbs
//! every offspring with the existing deterministic neighbor moves (unit swap /
//! insert / segment-reverse order moves + per-gene cache-priority nudges). The
//! fitness function is the REAL compile ([`super::scorer::score`]) — every
//! compile (initial population, each offspring, and every local-descent
//! neighbor) counts against `cfg.evals`.
//!
//! The neighbor-move families (`neighbor_entries` + `push_*_neighbors`) survive
//! as the memetic local-descent operator; the deleted `Replay` simulator's
//! trace-guided cache-neighbor family is gone (no compile trace to consume).
//!
//! Determinism: the breeding RNG (`SeedRng`, seeded by `cfg.seed`) is advanced
//! sequentially, neighbor enumeration is a fixed deterministic order, parallel
//! scoring preserves entry indices, and all tie-breaks are `(objective, index)`
//! — repeated runs with the same `SearchConfig` and `LayerCtx` produce identical
//! results.

use std::time::{Duration, Instant};

use crate::schedule::LayerSchedule;

use super::decode::decode_unit_order;
use super::genome::{CACHE_PRIORITY_BOUND, Genome, assert_normalized_genome, clamp_bias};
use super::scorer::{CandidateScore, LayerCtx, genome_from_schedule, objective_key, score};

// ── Tuning constants (values carried over from the prototype) ────────────────

/// Local cache-priority mutation step (prototype `LOCAL_BIAS_STEP`).
const LOCAL_BIAS_STEP: f64 = 0.25;
/// Per-batch cap on reserved cache-priority slots (prototype `CACHE_FAMILY_QUOTA`).
const CACHE_FAMILY_QUOTA: usize = 64;
/// Fixed per-iteration neighbor-batch cap, INDEPENDENT of the eval budget
/// (prototype H3): the unit-insert family is O(units^2); without a fixed cap
/// one batch at production scale consumes the whole budget and the local
/// descent degenerates to a single greedy step.
const NEIGHBOR_BATCH_CAP: usize = 128;

// ── SearchConfig (env-overridable, same contract as the deleted v1 producer) ─

/// Crossover operator family. `Blx` = per-gene BLX-alpha on both gene vectors
/// (production default — [`ga_crossover_blx`]); `Order` = permutation-preserving
/// order crossover (OX) on the unit-order genes + BLX-alpha on the continuous
/// cache-priority genes ([`ga_crossover_order`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CrossoverKind {
    Blx,
    Order,
}

/// Internal search knobs. The public offline API supplies every input explicitly.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SearchConfig {
    pub pop: usize,
    pub evals: usize,
    pub seed: u64,
    pub tournament: usize,   // GKR_SCHEDULE_TOURNAMENT
    pub elitism: usize,      // GKR_SCHEDULE_ELITISM
    pub crossover_rate: f64, // GKR_SCHEDULE_XOVER
    pub mutation_rate: f64,  // GKR_SCHEDULE_MUT_RATE (per-gene probability)
    pub mutation_sigma: f64, // GKR_SCHEDULE_MUT_SIGMA
    pub local_steps: usize,  // GKR_SCHEDULE_LOCAL_STEPS
    /// Number of the generation's best offspring (objective order) that receive
    /// memetic local descent. `0` = pure GA (no hill-climb). Rationing local
    /// descent to the top few offspring — rather than every offspring — is what
    /// prevents the local search from collapsing population diversity in ~2
    /// generations (the premature-convergence failure the Phase-B ablation
    /// surfaced). `GKR_SCHEDULE_LOCAL_ELITE`.
    pub local_elite: usize,
    /// Crossover operator applied to the unit-order genes. `GKR_SCHEDULE_XOVER_KIND`
    /// (`blx` | `order`). Default `Blx` keeps production behavior unchanged.
    pub crossover_kind: CrossoverKind,
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            pop: 64,
            evals: 20_000,
            seed: 0,
            tournament: 3,
            elitism: 2,
            crossover_rate: 0.9,
            mutation_rate: 0.1,
            mutation_sigma: 0.15,
            local_steps: 2,
            // Tuning verdict (Phase-B sweeps, .agents/specs/2026-07-06-gkr-ga-investigation-design.md):
            // pure GA (no memetic local descent) + order-crossover is the winner —
            // local descent, even rationed, over-exploits and collapses diversity;
            // OX inherits parent sub-orderings (BLX-alpha on raw keys destroyed them).
            // Beats the old beam+SA search by up to -8 on the hard layers.
            local_elite: 0,
            crossover_kind: CrossoverKind::Order,
        }
    }
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

// ── Phase-B ablation + telemetry (behavior-inert instrumentation) ─────────────

/// Phase-B ablation controls. `Default` = the full memetic GA, byte-identical to
/// production ([`optimize_from_population`]).
///
/// `random_search` replaces the entire select→crossover→mutate breeding path
/// with a fresh uniformly-random genome (bypassing selection, crossover and
/// mutation — their flags are then ignored); `local_descent` is still applied to
/// that genome iff its flag is set. So `random_search=true, local_descent=false`
/// is pure random search and `random_search=true, local_descent=true` is
/// local-descent-only from random restarts — the two non-GA baselines Phase B
/// measures the GA against. With `random_search=false`, `crossover`/`mutation`
/// individually disable that operator (the RNG draw for a disabled operator is
/// short-circuited, so an ablation run is a *different* stream — only the default
/// all-true config reproduces production's stream, which is the determinism gate).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GaAblation {
    pub crossover: bool,
    pub mutation: bool,
    pub local_descent: bool,
    pub random_search: bool,
}

impl Default for GaAblation {
    fn default() -> Self {
        Self {
            crossover: true,
            mutation: true,
            local_descent: true,
            random_search: false,
        }
    }
}

/// Per-generation + per-operator telemetry (behavior-inert). Every extra scoring
/// call the instrumented driver makes to fill these fields is RNG-free and is
/// NOT counted against `cfg.evals`, so the search trajectory — and therefore the
/// returned [`OptimizerResult`] — is identical whether or not telemetry is
/// collected (the determinism gate proves this on add_sub L0).
#[derive(Default, Clone, Debug, serde::Serialize)]
pub struct GaTelemetry {
    /// Free-form experiment tag, filled by the harness (the optimizer leaves it empty).
    pub label: String,
    pub floor: usize,
    /// Final best feasible `dram_traffic` (`usize::MAX` if no feasible candidate).
    pub final_best: usize,
    /// Which stage last produced the strict improvement that yielded the final
    /// `best`: `"seed"` | `"crossover"` | `"mutation"` | `"local_descent"`.
    pub winner_origin: String,
    pub total_evals: usize,
    pub generations: Vec<GenStat>,
}

/// One generation's aggregate statistics. `generation == 0` is the scored initial
/// population (no breeding); subsequent entries are the breeding generations.
#[derive(Default, Clone, Debug, serde::Serialize)]
pub struct GenStat {
    pub generation: usize,
    pub evals_so_far: usize,
    /// Best feasible `dram_traffic` in the population (`usize::MAX` if none feasible).
    pub best: usize,
    /// Mean feasible `dram_traffic` (`0.0` if none feasible).
    pub mean: f64,
    /// Mean per-gene stddev of `root_order_key` across the population.
    pub diversity_order: f64,
    /// Mean per-gene stddev of `cache_priority` across the population.
    pub diversity_prio: f64,
    /// Offspring bred this generation.
    pub offspring: usize,
    /// # crossover children whose post-crossover-pre-mutation fitness beat the
    /// better parent.
    pub crossover_improved: usize,
    /// # children whose post-mutation fitness beat their post-crossover fitness.
    pub mutation_improved: usize,
    /// # children local descent strictly improved.
    pub local_descent_improved: usize,
    /// Mean `(pre_ld - post_ld)` traffic drop from local descent (feasible only).
    pub mean_ld_gain: f64,
    /// Whether the global best improved during this generation.
    pub new_best: bool,
}

/// [`optimize_instrumented`] output: the production [`OptimizerResult`] plus
/// optional telemetry (`Some` iff `collect`).
pub struct GaRun {
    pub result: OptimizerResult,
    pub telemetry: Option<GaTelemetry>,
}

// ── Deterministic RNG helpers (prototype splitmix64 / unit_draw / SmokeRng) ──

// Only reached from the retained RNG tests below (`--lib` non-test builds
// never call it), so it warns dead-code outside `cfg(test)`; kept deliberately.
#[allow(dead_code)]
fn splitmix64(seed: u64) -> u64 {
    let mut z = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Deterministic sample in `[0, 1)` from a seed (top 53 bits of a splitmix64
/// hash) — keeps the optimizer's annealing reproducible across runs.
// Only reached from the retained RNG tests below; kept deliberately.
#[allow(dead_code)]
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
        Self {
            state: seed ^ 0x9e37_79b9_7f4a_7c15,
        }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn next_unit(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 * (1.0 / ((1u64 << 53) as f64))
    }

    fn next_signed(&mut self) -> f64 {
        self.next_unit() * 2.0 - 1.0
    }

    /// Standard-normal sample via Box-Muller (two uniforms). Deterministic given
    /// the RNG stream. `u1` floored off 0 to avoid `ln(0)`.
    fn next_gaussian(&mut self) -> f64 {
        let u1 = self.next_unit().max(1e-12);
        let u2 = self.next_unit();
        (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos()
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
    // Tagged by neighbor moves, retained for future consumers (e.g. move-family
    // reporting); not yet read anywhere.
    #[allow(dead_code)]
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
            out.push((
                out.len(),
                genome_with_unit_order(base, &inserted),
                Some(MoveFamily::UnitInsert),
            ));
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
            out.push((
                out.len(),
                genome_with_unit_order(base, &reversed),
                Some(MoveFamily::UnitReverse),
            ));
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
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
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
    let mut chunks: Vec<Vec<(usize, Genome, Option<MoveFamily>)>> =
        Vec::with_capacity(worker_count);
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
                            ScoredGenome {
                                index,
                                genome,
                                score,
                                family,
                            }
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

// ── GA operators (tournament + BLX-alpha crossover + Gaussian mutation) ──────

/// BLX-alpha blend of two random keys, clamped to a gene's domain `[lo, hi]`.
const BLX_ALPHA: f64 = 0.3;

fn blx_alpha(a: f64, b: f64, lo: f64, hi: f64, rng: &mut SeedRng) -> f64 {
    let (min, max) = (a.min(b), a.max(b));
    let d = max - min;
    let low = min - BLX_ALPHA * d;
    let high = max + BLX_ALPHA * d;
    (low + rng.next_unit() * (high - low)).clamp(lo, hi)
}

/// Dispatch to the configured crossover operator. The BLX arm is the historical
/// production path (byte-identical RNG stream); the Order arm swaps in
/// permutation-preserving OX for the unit-order genes (cache-priority stays BLX).
fn ga_crossover(p1: &Genome, p2: &Genome, kind: CrossoverKind, rng: &mut SeedRng) -> Genome {
    match kind {
        CrossoverKind::Blx => ga_crossover_blx(p1, p2, rng),
        CrossoverKind::Order => ga_crossover_order(p1, p2, rng),
    }
}

/// Per-gene BLX-alpha crossover over both gene vectors. Random keys stay in
/// `[0,1]` (any value decodes to a valid unit permutation — atomicity preserved);
/// priorities stay in `[-BOUND, BOUND]`.
fn ga_crossover_blx(p1: &Genome, p2: &Genome, rng: &mut SeedRng) -> Genome {
    let root_order_key = p1
        .root_order_key
        .iter()
        .zip(&p2.root_order_key)
        .map(|(&a, &b)| blx_alpha(a, b, 0.0, 1.0, rng))
        .collect();
    let cache_priority = p1
        .cache_priority
        .iter()
        .zip(&p2.cache_priority)
        .map(|(&a, &b)| blx_alpha(a, b, -CACHE_PRIORITY_BOUND, CACHE_PRIORITY_BOUND, rng))
        .collect();
    Genome {
        root_order_key,
        cache_priority,
    }
}

/// Order crossover (OX) on the unit-order permutation + BLX-alpha on the
/// continuous cache-priority genes. BLX blends both parents' raw random keys
/// per-gene, which destroys both orderings; OX decodes each parent to its unit
/// permutation, copies a contiguous segment from `p1`, then fills the rest in
/// `p2`'s relative order — inheriting real ordering structure from both parents.
/// The child permutation is re-encoded as distinct keys in `(0,1)` so
/// [`decode_unit_order`] reproduces it exactly.
fn ga_crossover_order(p1: &Genome, p2: &Genome, rng: &mut SeedRng) -> Genome {
    let n = p1.root_order_key.len();
    let o1 = decode_unit_order(&p1.root_order_key);
    let o2 = decode_unit_order(&p2.root_order_key);
    let child_order = if n <= 1 {
        o1
    } else {
        let a = (rng.next_u64() as usize) % n;
        let b = (rng.next_u64() as usize) % n;
        let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
        let mut in_child = vec![false; n];
        let mut child = vec![usize::MAX; n];
        for k in lo..=hi {
            child[k] = o1[k];
            in_child[o1[k]] = true;
        }
        let mut fill = 0usize;
        for &u in &o2 {
            if in_child[u] {
                continue;
            }
            while fill < n && child[fill] != usize::MAX {
                fill += 1;
            }
            child[fill] = u;
            in_child[u] = true;
        }
        child
    };
    // Re-encode child permutation as distinct keys in (0,1) so decode reproduces it exactly.
    let mut root_order_key = vec![0.0f64; n];
    for (pos, &unit) in child_order.iter().enumerate() {
        root_order_key[unit] = (pos as f64 + 0.5) / n as f64;
    }
    let cache_priority = p1
        .cache_priority
        .iter()
        .zip(&p2.cache_priority)
        .map(|(&a, &b)| blx_alpha(a, b, -CACHE_PRIORITY_BOUND, CACHE_PRIORITY_BOUND, rng))
        .collect();
    Genome {
        root_order_key,
        cache_priority,
    }
}

/// Per-gene Gaussian mutation at probability `rate`, step `sigma`, clamped to
/// each gene's domain. Continuous — removes the old fixed-step dyadic collisions.
fn ga_mutate(g: &mut Genome, rate: f64, sigma: f64, rng: &mut SeedRng) {
    for key in &mut g.root_order_key {
        if rng.next_unit() < rate {
            *key = (*key + rng.next_gaussian() * sigma).clamp(0.0, 1.0);
        }
    }
    for gene in &mut g.cache_priority {
        if rng.next_unit() < rate {
            *gene = clamp_bias(*gene + rng.next_gaussian() * sigma);
        }
    }
}

/// Tournament of size `k`: sample `k` population members, return the population
/// INDEX of the best by objective, ties broken by (lower) population index
/// (matches the file's tie discipline, codex-P5). `pop` is
/// `(Genome, CandidateScore)`. Splitting the index out (vs [`ga_tournament`])
/// lets the instrumented driver read the selected parents' fitness for operator
/// attribution without perturbing the RNG draw order.
fn ga_tournament_idx(pop: &[(Genome, CandidateScore)], k: usize, rng: &mut SeedRng) -> usize {
    let mut best: Option<usize> = None;
    for _ in 0..k.max(1) {
        let i = (rng.next_u64() as usize) % pop.len();
        best = Some(match best {
            None => i,
            Some(b) => {
                // strictly better objective wins; on a tie, lower index wins.
                if objective_key(&pop[i].1)
                    .cmp(&objective_key(&pop[b].1))
                    .then(i.cmp(&b))
                    .is_lt()
                {
                    i
                } else {
                    b
                }
            }
        });
    }
    best.expect("k>=1 so best is set")
}

/// Tournament winner genome (thin wrapper over [`ga_tournament_idx`], same RNG
/// draws). Only reached from the operator unit test; the driver uses the `_idx`
/// form directly to capture parent indices.
#[cfg(test)]
fn ga_tournament<'a>(
    pop: &'a [(Genome, CandidateScore)],
    k: usize,
    rng: &mut SeedRng,
) -> &'a Genome {
    &pop[ga_tournament_idx(pop, k, rng)].0
}

/// Memetic hill-climb: up to `steps` rounds of the existing neighbor moves;
/// adopt the best strictly-improving neighbor each round, stop at a local
/// optimum. Every scored neighbor counts against `evals`/`budget`. `pub` so the
/// integration suite can exercise the "never worsens" property on a real ctx.
pub fn ga_local_descent(
    ctx: &LayerCtx,
    mut genome: Genome,
    mut score: CandidateScore,
    steps: usize,
    evals: &mut usize,
    budget: usize,
) -> (Genome, CandidateScore) {
    for _ in 0..steps {
        if *evals >= budget {
            break;
        }
        let remaining = (budget - *evals).min(NEIGHBOR_BATCH_CAP);
        let neighbors = neighbor_entries(ctx.n_order_keys(), &genome, remaining);
        if neighbors.is_empty() {
            break;
        }
        *evals += neighbors.len();
        let scored = score_genomes_parallel(ctx, neighbors, default_worker_count());
        let best = scored
            .iter()
            .filter(|e| objective_less(&e.score, &score))
            .min_by(|a, b| {
                objective_key(&a.score)
                    .cmp(&objective_key(&b.score))
                    .then(a.index.cmp(&b.index))
            });
        match best {
            Some(b) => {
                genome = b.genome.clone();
                score = b.score;
            }
            None => break, // local optimum
        }
    }
    (genome, score)
}

// ── Generational memetic GA driver ──────────────────────────────────────────

/// Generational memetic GA. Seeds an initial population, then each generation:
/// carry the `elitism` best unchanged, breed the rest by tournament selection +
/// BLX-alpha crossover + Gaussian mutation, **score the whole offspring cohort in
/// one parallel batch** (all cores), then apply memetic local descent to only the
/// best `local_elite` offspring. All compiles (population + offspring + local
/// descent) count against `cfg.evals`. Deterministic given `cfg.seed` (breeding
/// RNG is sequential; scoring is parallel but RNG-free and index-stable).
pub fn optimize_from_population(
    ctx: &LayerCtx,
    seeds: Vec<Genome>,
    cfg: &SearchConfig,
) -> OptimizerResult {
    // Single shared code path: production is `optimize_instrumented` with the
    // default (full-GA) ablation and telemetry off — behaviour-inert defaults, so
    // the result is identical with telemetry on or off (the determinism gate
    // `optimize_instrumented_default_matches_production` in `tests/ga_investigation.rs`).
    optimize_instrumented(ctx, seeds, cfg, GaAblation::default(), false).result
}

/// Mean per-gene standard deviation of a population's gene vectors (all `rows`
/// share one length by construction — every genome is sized against `ctx`). The
/// population diversity metric: `0.0` for an empty population or zero-length
/// genes (nothing to vary).
fn mean_gene_stddev(rows: &[&[f64]]) -> f64 {
    if rows.is_empty() {
        return 0.0;
    }
    let n_genes = rows[0].len();
    if n_genes == 0 {
        return 0.0;
    }
    let pop_n = rows.len() as f64;
    let mut total = 0.0;
    for g in 0..n_genes {
        let mean = rows.iter().map(|v| v[g]).sum::<f64>() / pop_n;
        let var = rows
            .iter()
            .map(|v| (v[g] - mean) * (v[g] - mean))
            .sum::<f64>()
            / pop_n;
        total += var.sqrt();
    }
    total / n_genes as f64
}

/// `(best_feasible_traffic, mean_feasible_traffic, diversity_order, diversity_prio)`
/// over `pop`. `best`/`mean` ignore infeasible members; `best = usize::MAX` and
/// `mean = 0.0` when none are feasible.
fn population_stats(pop: &[(Genome, CandidateScore)]) -> (usize, f64, f64, f64) {
    let feasible: Vec<usize> = pop
        .iter()
        .filter(|p| !p.1.infeasible)
        .map(|p| p.1.dram_traffic)
        .collect();
    let best = feasible.iter().copied().min().unwrap_or(usize::MAX);
    let mean = if feasible.is_empty() {
        0.0
    } else {
        feasible.iter().sum::<usize>() as f64 / feasible.len() as f64
    };
    let order_rows: Vec<&[f64]> = pop.iter().map(|p| p.0.root_order_key.as_slice()).collect();
    let prio_rows: Vec<&[f64]> = pop.iter().map(|p| p.0.cache_priority.as_slice()).collect();
    (
        best,
        mean,
        mean_gene_stddev(&order_rows),
        mean_gene_stddev(&prio_rows),
    )
}

/// Instrumented memetic-GA driver — the single implementation behind
/// [`optimize_from_population`]. `ablation` selects which operators run and
/// `collect` toggles [`GaTelemetry`]. Both are behavior-inert at their defaults
/// (`GaAblation::default()`, `collect = false`) — they add no RNG draws and no
/// `evals` charges, so the [`OptimizerResult`] is identical to the historical
/// loop. Telemetry's per-operator attribution uses EXTRA scoring calls that are
/// RNG-free (the scorer is pure) and are deliberately NOT added to `evals`.
pub fn optimize_instrumented(
    ctx: &LayerCtx,
    seeds: Vec<Genome>,
    cfg: &SearchConfig,
    ablation: GaAblation,
    collect: bool,
) -> GaRun {
    let budget = cfg.evals;
    assert!(budget > 0, "eval budget must be positive");
    assert!(
        cfg.elitism < cfg.pop,
        "elitism ({}) must be < pop ({})",
        cfg.elitism,
        cfg.pop
    );
    let n_units = ctx.n_order_keys();
    let n_sites = ctx.n_sites();
    let seeds = if seeds.is_empty() {
        vec![Genome::neutral(n_units, n_sites)]
    } else {
        seeds
    };
    for g in &seeds {
        assert_normalized_genome(g);
    }

    let workers = default_worker_count();
    let mut rng = SeedRng::new(cfg.seed);
    // Initial population score.
    let init: Vec<_> = seeds
        .into_iter()
        .take(budget)
        .enumerate()
        .map(|(i, g)| (i, g, None))
        .collect();
    let mut evals = init.len();
    let scored = score_genomes_parallel(ctx, init, workers);
    let mut pop: Vec<(Genome, CandidateScore)> =
        scored.into_iter().map(|s| (s.genome, s.score)).collect();
    assert!(!pop.is_empty(), "seed population must be non-empty");

    let best_of = |pop: &[(Genome, CandidateScore)]| -> (Genome, CandidateScore) {
        pop.iter()
            .min_by(|a, b| objective_key(&a.1).cmp(&objective_key(&b.1)))
            .expect("non-empty")
            .clone()
    };
    let mut best = best_of(&pop);
    let mut winner_origin = "seed";
    let mut generations = 0usize;

    let mut telemetry = if collect {
        let (b, m, dord, dpri) = population_stats(&pop);
        Some(GaTelemetry {
            floor: ctx.floor,
            generations: vec![GenStat {
                generation: 0,
                evals_so_far: evals,
                best: b,
                mean: m,
                diversity_order: dord,
                diversity_prio: dpri,
                new_best: true,
                ..Default::default()
            }],
            ..Default::default()
        })
    } else {
        None
    };

    while evals < budget {
        // Sort for elitism (best first).
        pop.sort_by(|a, b| objective_key(&a.1).cmp(&objective_key(&b.1)));
        let mut next: Vec<(Genome, CandidateScore)> = pop
            .iter()
            .take(cfg.elitism.min(pop.len()))
            .cloned()
            .collect();
        let gen_best_before = objective_key(&best.1);

        // ── 1) Breed the whole offspring cohort (RNG-sequential, cheap). ──
        // Cap by the remaining eval budget so the batch score never overshoots.
        let cohort_cap = cfg.pop.saturating_sub(next.len()).min(budget - evals);
        let mut cohort: Vec<Genome> = Vec::with_capacity(cohort_cap);
        // Per-child attribution meta (telemetry): (better-parent score, did_crossover, mutated).
        let mut meta: Vec<(Option<CandidateScore>, bool, bool)> = Vec::with_capacity(cohort_cap);
        // Post-crossover-pre-mutation children (telemetry only) for the operator split.
        let mut pre_children: Vec<Genome> = Vec::new();
        for _ in 0..cohort_cap {
            let (mut child, s_parent, did_crossover) = if ablation.random_search {
                // Fresh uniformly-random genome: keys in [0,1], priorities in
                // [-BOUND, BOUND]. Bypasses selection/crossover/mutation.
                let mut g = Genome::neutral(n_units, n_sites);
                for k in &mut g.root_order_key {
                    *k = rng.next_unit();
                }
                for b in &mut g.cache_priority {
                    *b = clamp_bias(rng.next_signed() * CACHE_PRIORITY_BOUND);
                }
                (g, None, false)
            } else {
                let i1 = ga_tournament_idx(&pop, cfg.tournament, &mut rng);
                let i2 = ga_tournament_idx(&pop, cfg.tournament, &mut rng);
                let p1 = pop[i1].0.clone();
                let p2 = pop[i2].0.clone();
                // Default (`ablation.crossover == true`) still draws exactly one
                // `next_unit()` here. A disabled crossover short-circuits the draw
                // (ablation stream diverges — intended).
                let did_crossover = ablation.crossover && rng.next_unit() < cfg.crossover_rate;
                let child = if did_crossover {
                    ga_crossover(&p1, &p2, cfg.crossover_kind, &mut rng)
                } else {
                    p1.clone()
                };
                let s_parent = if did_crossover {
                    if objective_less(&pop[i1].1, &pop[i2].1) {
                        pop[i1].1
                    } else {
                        pop[i2].1
                    }
                } else {
                    pop[i1].1
                };
                (child, Some(s_parent), did_crossover)
            };
            if collect && !ablation.random_search {
                pre_children.push(child.clone());
            }
            let mutation_ran = ablation.mutation && !ablation.random_search;
            if mutation_ran {
                ga_mutate(&mut child, cfg.mutation_rate, cfg.mutation_sigma, &mut rng);
            }
            assert_normalized_genome(&child); // clamps guarantee this; loud if a NaN slips through
            meta.push((s_parent, did_crossover, mutation_ran));
            cohort.push(child);
        }
        let bred = cohort.len();
        if bred == 0 {
            break; // budget exhausted; no filler
        }

        // ── 2) Score the WHOLE cohort in one parallel batch (all cores). ──
        let entries: Vec<_> = cohort
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, g)| (i, g, None))
            .collect();
        let scored = score_genomes_parallel(ctx, entries, workers); // index-stable
        evals += bred;
        let mut cohort_scored: Vec<(Genome, CandidateScore)> =
            scored.into_iter().map(|s| (s.genome, s.score)).collect();
        let post_mut_scores: Vec<CandidateScore> = cohort_scored.iter().map(|(_, s)| *s).collect();

        // Telemetry-only: pre-mutation batch score (RNG-free, uncounted) for the split.
        let pre_scores: Vec<CandidateScore> = if collect && !pre_children.is_empty() {
            let e: Vec<_> = pre_children
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, g)| (i, g, None))
                .collect();
            score_genomes_parallel(ctx, e, workers)
                .into_iter()
                .map(|s| s.score)
                .collect()
        } else {
            Vec::new()
        };

        // ── 3) Rationed memetic local descent: only the best `local_elite`
        // offspring are polished (best-first, deterministic order), until the
        // budget is spent. Rationing is what stops local search from collapsing
        // diversity every generation (the Phase-B premature-convergence finding).
        let mut ld_gained = vec![false; bred];
        if ablation.local_descent && cfg.local_elite > 0 {
            let mut order: Vec<usize> = (0..bred).collect();
            order.sort_by(|&a, &b| {
                objective_key(&cohort_scored[a].1)
                    .cmp(&objective_key(&cohort_scored[b].1))
                    .then(a.cmp(&b))
            });
            for &i in order.iter().take(cfg.local_elite) {
                if evals >= budget {
                    break;
                }
                let (g0, s0) = cohort_scored[i].clone();
                let (g, s) = ga_local_descent(ctx, g0, s0, cfg.local_steps, &mut evals, budget);
                if objective_less(&s, &cohort_scored[i].1) {
                    ld_gained[i] = true;
                }
                cohort_scored[i] = (g, s);
            }
        }

        // ── Operator attribution + best/provenance update (no RNG). ──
        let mut xover_improved = 0usize;
        let mut mut_improved = 0usize;
        let mut ld_improved = 0usize;
        let mut ld_gain_sum = 0.0f64;
        let mut ld_gain_n = 0usize;
        for i in 0..bred {
            let (s_parent, did_crossover, mutated) = meta[i];
            let pre = pre_scores.get(i).copied();
            if collect {
                if did_crossover {
                    if let (Some(pm), Some(sp)) = (pre, s_parent) {
                        if objective_less(&pm, &sp) {
                            xover_improved += 1;
                        }
                    }
                }
                if mutated {
                    if let Some(pm) = pre {
                        if objective_less(&post_mut_scores[i], &pm) {
                            mut_improved += 1;
                        }
                    }
                }
                if ld_gained[i] {
                    ld_improved += 1;
                    let now = cohort_scored[i].1;
                    if !now.infeasible && !post_mut_scores[i].infeasible {
                        ld_gain_sum +=
                            post_mut_scores[i].dram_traffic as f64 - now.dram_traffic as f64;
                        ld_gain_n += 1;
                    }
                }
            }
            let sc = cohort_scored[i].1;
            if objective_less(&sc, &best.1) {
                best = (cohort_scored[i].0.clone(), sc);
                if collect {
                    let mut origin = "seed";
                    if did_crossover {
                        if let (Some(pm), Some(sp)) = (pre, s_parent) {
                            if objective_less(&pm, &sp) {
                                origin = "crossover";
                            }
                        }
                    }
                    if mutated {
                        if let Some(pm) = pre {
                            if objective_less(&post_mut_scores[i], &pm) {
                                origin = "mutation";
                            }
                        }
                    }
                    if ld_gained[i] {
                        origin = "local_descent";
                    }
                    winner_origin = origin;
                }
            }
        }

        // ── Form the next generation (elites + scored cohort), pad if cut short. ──
        next.extend(cohort_scored);
        while next.len() < cfg.pop && next.len() < pop.len() {
            next.push(pop[next.len()].clone());
        }
        pop = next;
        generations += 1;

        if let Some(t) = telemetry.as_mut() {
            let (b, m, dord, dpri) = population_stats(&pop);
            t.generations.push(GenStat {
                generation: generations,
                evals_so_far: evals,
                best: b,
                mean: m,
                diversity_order: dord,
                diversity_prio: dpri,
                offspring: bred,
                crossover_improved: xover_improved,
                mutation_improved: mut_improved,
                local_descent_improved: ld_improved,
                mean_ld_gain: if ld_gain_n > 0 {
                    ld_gain_sum / ld_gain_n as f64
                } else {
                    0.0
                },
                new_best: objective_key(&best.1) < gen_best_before,
            });
        }
    }

    let result = OptimizerResult {
        best_genome: best.0.clone(),
        best_score: best.1,
        evals,
        iterations: generations,
        beam_states: cfg.pop,
    };
    if let Some(t) = telemetry.as_mut() {
        t.final_best = if best.1.infeasible {
            usize::MAX
        } else {
            best.1.dram_traffic
        };
        t.winner_origin = winner_origin.to_string();
        t.total_evals = evals;
    }
    GaRun { result, telemetry }
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
        let f = crate::forward::compile::expr_operand_field(
            ctx.layer,
            gkr_eval_ir::ExprId(value),
            ctx.cross_layer_fields,
        );
        if f == crate::forward::isa::OperandField::Ext {
            4.0
        } else {
            1.0
        }
    };
    let density = |value: u32| demand_count[&value] as f64 / width(value);
    let max_density = ctx
        .sites
        .iter()
        .map(|s| density(s.value.0))
        .fold(0.0f64, f64::max);
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

/// Search one layer: seed `cfg.pop` genomes, run the memetic GA for `cfg.evals`
/// compile-evals, and return the winning schedule stamped with its own compile's
/// traffic. Panics if even the best candidate is infeasible at `ctx.budget` (an
/// infeasible layer is a real problem, not a schedule — the deleted v1
/// producer's F6 gate).
///
/// `incumbent`, when `Some(ls)`, is a previously-persisted schedule for this
/// layer. It drives a two-strategy ENSEMBLE that dominates either strategy alone:
///   1. **from-scratch** — best exploration; finds better basins on some layers
///      (bigint/keccak L0 reach lower traffic from scratch than by refining the
///      incumbent, which as a strong seed collapses diversity around its basin);
///   2. **incumbent-seeded** — best refinement; on other layers the GA improves
///      *upon* the incumbent better than it explores blind (e.g. blake2-ext L0
///      −13 seeded vs 0 from scratch).
/// The best of the two is taken, then the incumbent itself is a post-hoc floor
/// (kept if it beats both searches) — so the result is never worse than the
/// persisted schedule (non-regression) and captures whichever strategy wins.
pub fn search_layer(
    ctx: &LayerCtx,
    cfg: &SearchConfig,
    incumbent: Option<&LayerSchedule>,
) -> LayerSearchOutcome {
    let start = Instant::now();

    if ctx.n_order_keys() == 0 {
        // No atom roots: nothing to schedule. Trivial empty (and trivially
        // valid) schedule; `floor: 0` mirrors the v1 producer's empty branch
        // (the validator requires floor <= predicted_traffic, and an
        // unsearched layer records no achieved traffic).
        return LayerSearchOutcome {
            schedule: LayerSchedule {
                units: vec![],
                sites: vec![],
                predicted_traffic: 0,
                floor: 0,
            },
            compiles: 0,
            wall: start.elapsed(),
        };
    }

    // Strategy 1: from-scratch (best exploration).
    let seeds_fs = seeded_population(ctx, cfg.pop.min(cfg.evals), cfg.seed);
    let opt_fs = optimize_from_population(ctx, seeds_fs, cfg);
    let mut best_genome = opt_fs.best_genome;
    let mut best_score = opt_fs.best_score;
    let mut compiles = opt_fs.evals;

    // Strategy 2: incumbent-seeded (best refinement of a good starting point).
    if let Some(ls) = incumbent {
        let mut seeds_seed = seeded_population(ctx, cfg.pop.min(cfg.evals), cfg.seed);
        seeds_seed.insert(0, genome_from_schedule(ls, ctx));
        let opt_seed = optimize_from_population(ctx, seeds_seed, cfg);
        compiles += opt_seed.evals;
        if objective_less(&opt_seed.best_score, &best_score) {
            best_genome = opt_seed.best_genome;
            best_score = opt_seed.best_score;
        }
    }

    assert!(
        !best_score.infeasible,
        "search_layer: best candidate infeasible at budget {} ({} units, {} sites)",
        ctx.budget,
        ctx.n_order_keys(),
        ctx.n_sites()
    );

    let mut schedule = super::scorer::decode_schedule(&best_genome, ctx);
    schedule.predicted_traffic = best_score.dram_traffic;

    // Post-hoc non-regression floor: keep the incumbent structure if it is at least as
    // good as both searches (never regress below the persisted schedule). Recompute the
    // incumbent's traffic UNDER THE CURRENT OBJECTIVE rather than trusting its stored
    // `predicted_traffic`: a value persisted under a different cost model (e.g. before a
    // traffic-accounting change) would otherwise wrongly discard an equal-cost incumbent
    // and let the GA drift to a different-but-equal structure, churning the corpus. Relabel
    // the kept incumbent's `predicted_traffic` to the recomputed value.
    if let Some(inc) = incumbent {
        let inc_score = score(&genome_from_schedule(inc, ctx), ctx);
        if !inc_score.infeasible && inc_score.dram_traffic <= schedule.predicted_traffic {
            let mut kept = inc.clone();
            kept.predicted_traffic = inc_score.dram_traffic;
            schedule = kept;
        }
    }
    assert!(
        schedule.floor <= schedule.predicted_traffic,
        "search_layer: floor {} above achieved traffic {}",
        schedule.floor,
        schedule.predicted_traffic
    );

    LayerSearchOutcome {
        schedule,
        compiles,
        wall: start.elapsed(),
    }
}
