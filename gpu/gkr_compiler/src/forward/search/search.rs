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
    /// memetic local descent. `0` = pure GA (no hill-climb).
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
    let budget = cfg.evals;
    assert!(budget > 0, "eval budget must be positive");
    assert!(
        cfg.elitism < cfg.pop,
        "elitism ({}) must be < pop ({})",
        cfg.elitism,
        cfg.pop
    );

    let seeds = if seeds.is_empty() {
        vec![Genome::neutral(ctx.n_order_keys(), ctx.n_sites())]
    } else {
        seeds
    };
    for genome in &seeds {
        assert_normalized_genome(genome);
    }

    let workers = default_worker_count();
    let mut rng = SeedRng::new(cfg.seed);
    let initial: Vec<_> = seeds
        .into_iter()
        .take(budget)
        .enumerate()
        .map(|(index, genome)| (index, genome, None))
        .collect();
    let mut evals = initial.len();
    let mut population: Vec<(Genome, CandidateScore)> =
        score_genomes_parallel(ctx, initial, workers)
            .into_iter()
            .map(|entry| (entry.genome, entry.score))
            .collect();
    assert!(!population.is_empty(), "seed population must be non-empty");

    let mut best = population
        .iter()
        .min_by(|a, b| objective_key(&a.1).cmp(&objective_key(&b.1)))
        .expect("non-empty")
        .clone();

    while evals < budget {
        population.sort_by(|a, b| objective_key(&a.1).cmp(&objective_key(&b.1)));
        let mut next: Vec<(Genome, CandidateScore)> = population
            .iter()
            .take(cfg.elitism.min(population.len()))
            .cloned()
            .collect();

        let cohort_cap = cfg
            .pop
            .saturating_sub(next.len())
            .min(budget.saturating_sub(evals));
        let mut cohort = Vec::with_capacity(cohort_cap);
        for _ in 0..cohort_cap {
            let first = ga_tournament_idx(&population, cfg.tournament, &mut rng);
            let second = ga_tournament_idx(&population, cfg.tournament, &mut rng);
            let mut child = if rng.next_unit() < cfg.crossover_rate {
                ga_crossover(
                    &population[first].0,
                    &population[second].0,
                    cfg.crossover_kind,
                    &mut rng,
                )
            } else {
                population[first].0.clone()
            };
            ga_mutate(&mut child, cfg.mutation_rate, cfg.mutation_sigma, &mut rng);
            assert_normalized_genome(&child);
            cohort.push(child);
        }
        if cohort.is_empty() {
            break;
        }

        let entries: Vec<_> = cohort
            .into_iter()
            .enumerate()
            .map(|(index, genome)| (index, genome, None))
            .collect();
        let mut scored: Vec<(Genome, CandidateScore)> =
            score_genomes_parallel(ctx, entries, workers)
                .into_iter()
                .map(|entry| (entry.genome, entry.score))
                .collect();
        evals += scored.len();

        if cfg.local_elite > 0 {
            let mut order: Vec<usize> = (0..scored.len()).collect();
            order.sort_by(|&a, &b| {
                objective_key(&scored[a].1)
                    .cmp(&objective_key(&scored[b].1))
                    .then(a.cmp(&b))
            });
            for index in order.into_iter().take(cfg.local_elite) {
                if evals >= budget {
                    break;
                }
                let (genome, score) = scored[index].clone();
                scored[index] =
                    ga_local_descent(ctx, genome, score, cfg.local_steps, &mut evals, budget);
            }
        }

        for candidate in &scored {
            if objective_less(&candidate.1, &best.1) {
                best = candidate.clone();
            }
        }
        next.extend(scored);
        while next.len() < cfg.pop && next.len() < population.len() {
            next.push(population[next.len()].clone());
        }
        population = next;
    }

    OptimizerResult {
        best_genome: best.0,
        best_score: best.1,
        evals,
    }
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
