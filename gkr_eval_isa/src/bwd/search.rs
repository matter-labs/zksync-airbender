//! Task 8: the backward schedule-search ADAPTER.
//!
//! The forward search (`schedule_search/{search,scorer,genome,decode}.rs`) is
//! deeply fwd-shaped — its `LayerCtx`/`score`/`decode_schedule` are wired to the
//! forward compiler and are NOT injectable at a constructor — so this module does
//! NOT reuse the fwd GA driver. It DOES reuse the fwd gene TYPES
//! ([`Genome`](crate::schedule_search::genome::Genome) — order keys + cache
//! priorities) and the pure permutation decode
//! ([`decode_unit_order`](crate::schedule_search::decode::decode_unit_order)),
//! and owns a small, self-contained, deterministic GA loop sized for the
//! mini-GATE-D smoke (`pop 4 / evals ~40`). Production-budget search is a
//! census-time option, not a Task-8 requirement.
//!
//! REV2 encoding (Codex option b):
//! * **order genes** permute the CANONICAL relation units
//!   ([`bwd_relation_units`](cs::gkr_compiler::dag_ir::bwd_relation_units), which
//!   [`distill`] partitions into `DistilledLayer::unit_order`). The adapter
//!   re-distills with the decoded `unit_permutation`, rebuilding the top-level
//!   alpha `Add` in that order. Each root keeps its FIXED beta exponent (its
//!   canonical batching position), so any permutation is VALUE-identical by
//!   commutativity and only schedule-relevant (it drives the re-interning order,
//!   hence the distilled `ExprId` numbering that lowering keys off).
//! * **cache-priority genes** map positionally to the candidate's
//!   [`distilled_site_domain`] sites (sorted `BTreeSet` order) → a
//!   [`SiteDecisions`] the bwd compiler consumes.
//!
//! Fitness ([`score_candidate`]) is the REAL compile: ordered
//! `(infeasible, global + fold_traffic, program_lanes)` from
//! [`BwdCompiledLayer::stats_ext`] — the Task-5 `fold_traffic` tally makes the Ext
//! search see its dominant FoldSource reads (invisible to `CompileStats`).
//!
//! Determinism: the breeding RNG is an explicit-seed LCG (mirrors the fwd
//! `SeedRng`); no wall-clock seeding — repeated runs with the same
//! `BwdSearchConfig` produce identical results.

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, FieldKind, ReadPlace, SiteKey};

use crate::bwd::compile::{compile_distilled, BwdTrafficStats};
use crate::bwd::distill::{distill, distilled_site_domain};
use crate::fwd::compile::SiteDecisions;
use crate::fwd::error::CompileError;
use crate::schedule_search::decode::decode_unit_order;
use crate::schedule_search::genome::{assert_normalized_genome, clamp_bias, Genome};

// ── Config / outcome ────────────────────────────────────────────────────────────

/// Minimal, bwd-local search knobs. The fwd [`SearchConfig`](crate::schedule_search::search::SearchConfig)
/// carries GA fields calibrated for its own driver (tournament/elitism/crossover
/// rates/local-descent rationing); reusing it would drag fwd-shaped fields this
/// adapter's compact loop does not honor, so this is a deliberately small local
/// type. `seed` is the explicit deterministic seed (wall-clock seeding is banned).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct BwdSearchConfig {
    /// Population size.
    pub pop: usize,
    /// Total compile-eval budget (initial population + every bred offspring).
    pub evals: usize,
    /// Explicit breeding-RNG seed.
    pub seed: u64,
    /// Per-gene Gaussian mutation step.
    pub mutation_sigma: f64,
}

impl Default for BwdSearchConfig {
    fn default() -> Self {
        Self { pop: 4, evals: 40, seed: 0, mutation_sigma: 0.2 }
    }
}

/// Result of searching one backward layer × regime: the winning
/// [`SiteDecisions`] (keyed to the winning candidate's distilled site domain),
/// its `unit_permutation` (feed back into [`distill`] to reproduce the schedule),
/// and the winning compile's search-facing traffic stats.
pub struct BwdSearchOutcome {
    pub decisions: SiteDecisions,
    pub unit_permutation: Vec<usize>,
    pub stats: BwdTrafficStats,
}

// ── Candidate scoring (the real compile) ─────────────────────────────────────────

/// A scored candidate. `infeasible` candidates (placement floor above `budget`)
/// sort last with `traffic = usize::MAX`, so any feasible candidate wins.
#[derive(Clone, Copy)]
struct BwdScore {
    infeasible: bool,
    /// `global + fold_traffic` — the search objective.
    traffic: usize,
    /// `program_lanes` — the instruction-count tiebreak.
    instrs: usize,
    stats: BwdTrafficStats,
}

/// Lexicographic objective: prefer feasible, then lower traffic, then fewer
/// instructions. Lower is better.
fn objective_key(s: &BwdScore) -> (u8, usize, usize) {
    (s.infeasible as u8, s.traffic, s.instrs)
}

/// Decode a genome to `(unit_permutation, SiteDecisions)` and REAL-compile it.
///
/// The permutation is decoded from the order-key genes; distillation with that
/// permutation yields the candidate's own site domain, which the cache-priority
/// genes map onto positionally (sorted-`SiteKey` order — `zip` tolerates a
/// count mismatch, which cannot happen here since the domain size is
/// permutation-invariant, but keeps the adapter panic-free either way).
fn score_candidate(
    genome: &Genome,
    layer: &DagLayer,
    regime: BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
) -> (Vec<usize>, SiteDecisions, BwdScore) {
    let perm = decode_unit_order(&genome.root_order_key);
    let d = distill(layer, regime, cross, Some(&perm));
    let sites: Vec<SiteKey> = distilled_site_domain(&d).into_iter().collect();
    let decisions =
        SiteDecisions::new(sites.into_iter().zip(genome.cache_priority.iter().copied()));

    let score = match compile_distilled(&d, budget, Some(&decisions)) {
        Ok(c) => BwdScore {
            infeasible: false,
            traffic: c.stats_ext.global + c.stats_ext.fold_traffic,
            instrs: c.stats.program_lanes,
            stats: c.stats_ext,
        },
        Err(CompileError::BudgetBelowFloor { .. }) => BwdScore {
            infeasible: true,
            traffic: usize::MAX,
            instrs: usize::MAX,
            stats: BwdTrafficStats::default(),
        },
        Err(e) => panic!("bwd search: unexpected compile error: {e:?}"),
    };
    (perm, decisions, score)
}

// ── Deterministic RNG (mirrors the fwd `SeedRng` LCG) ─────────────────────────────

struct SeedRng {
    state: u64,
}

impl SeedRng {
    fn new(seed: u64) -> Self {
        Self { state: seed ^ 0x9e37_79b9_7f4a_7c15 }
    }
    fn next_u64(&mut self) -> u64 {
        self.state =
            self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn next_unit(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 * (1.0 / ((1u64 << 53) as f64))
    }
    fn next_signed(&mut self) -> f64 {
        self.next_unit() * 2.0 - 1.0
    }
    /// Standard-normal via Box-Muller (`u1` floored off 0 to avoid `ln(0)`).
    fn next_gaussian(&mut self) -> f64 {
        let u1 = self.next_unit().max(1e-12);
        let u2 = self.next_unit();
        (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos()
    }
}

// ── GA operators (compact local versions) ─────────────────────────────────────────

const BLX_ALPHA: f64 = 0.3;
const MUTATION_RATE: f64 = 0.3;

/// Size-2 tournament: pick two population members, return the better's index.
fn tournament(pop: &[(Genome, BwdScore)], rng: &mut SeedRng) -> usize {
    let a = (rng.next_u64() as usize) % pop.len();
    let b = (rng.next_u64() as usize) % pop.len();
    if objective_key(&pop[a].1) <= objective_key(&pop[b].1) {
        a
    } else {
        b
    }
}

/// Order crossover (OX) over the unit permutation — inherits contiguous
/// sub-orderings from both parents, then re-encodes as distinct keys in `(0,1)`
/// so [`decode_unit_order`] reproduces the child exactly.
fn order_crossover(p1: &[f64], p2: &[f64], rng: &mut SeedRng) -> Vec<f64> {
    let n = p1.len();
    if n <= 1 {
        return p1.to_vec();
    }
    let o1 = decode_unit_order(p1);
    let o2 = decode_unit_order(p2);
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
    let mut keys = vec![0.0f64; n];
    for (pos, &u) in child.iter().enumerate() {
        keys[u] = (pos as f64 + 0.5) / n as f64;
    }
    keys
}

/// BLX-alpha blend of two cache-priority genes, clamped to the symmetric bias range.
fn blx(a: f64, b: f64, rng: &mut SeedRng) -> f64 {
    let (min, max) = (a.min(b), a.max(b));
    let d = max - min;
    let low = min - BLX_ALPHA * d;
    let high = max + BLX_ALPHA * d;
    clamp_bias(low + rng.next_unit() * (high - low))
}

/// Per-gene Gaussian mutation, clamped to each gene's domain.
fn mutate(g: &mut Genome, sigma: f64, rng: &mut SeedRng) {
    for key in &mut g.root_order_key {
        if rng.next_unit() < MUTATION_RATE {
            *key = (*key + rng.next_gaussian() * sigma).clamp(0.0, 1.0);
        }
    }
    for gene in &mut g.cache_priority {
        if rng.next_unit() < MUTATION_RATE {
            *gene = clamp_bias(*gene + rng.next_gaussian() * sigma);
        }
    }
}

// ── Seed population ────────────────────────────────────────────────────────────

/// Neutral (identity order, zero priorities) + reversed-neutral + a deterministic
/// random tail — enough diversity for the smoke-scale GA.
fn seed_population(n_units: usize, n_sites: usize, pop: usize, rng: &mut SeedRng) -> Vec<Genome> {
    let mut genomes = Vec::with_capacity(pop);
    if pop == 0 {
        return genomes;
    }
    genomes.push(Genome::neutral(n_units, n_sites));
    if genomes.len() < pop {
        let mut reversed = Genome::neutral(n_units, n_sites);
        let n = reversed.root_order_key.len();
        let denom = n.max(1) as f64;
        for (idx, key) in reversed.root_order_key.iter_mut().enumerate() {
            *key = (n - 1 - idx) as f64 / denom;
        }
        genomes.push(reversed);
    }
    while genomes.len() < pop {
        let mut g = Genome::neutral(n_units, n_sites);
        for key in &mut g.root_order_key {
            *key = rng.next_unit();
        }
        for gene in &mut g.cache_priority {
            *gene = clamp_bias(rng.next_signed());
        }
        genomes.push(g);
    }
    genomes
}

// ── The per-layer driver ─────────────────────────────────────────────────────────

/// Search one backward layer × regime for a low-traffic `(unit_permutation,
/// SiteDecisions)` at `budget`, via a compact deterministic GA over the fwd gene
/// types. Every genome scored is a real [`compile_distilled`]; the returned
/// outcome is the best candidate found (never worse than the neutral seed, which
/// is always evaluated first).
///
/// A layer with zero relation units (nothing to order) still runs — the order
/// genes are empty, so the GA only tunes cache priorities (or is a no-op if the
/// distilled site domain is also empty).
pub fn search_bwd_layer(
    layer: &DagLayer,
    regime: BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
    cfg: &BwdSearchConfig,
) -> BwdSearchOutcome {
    assert!(cfg.pop > 0, "BwdSearchConfig.pop must be positive");
    assert!(cfg.evals > 0, "BwdSearchConfig.evals must be positive");

    // Gene-vector sizing off the canonical (unpermuted) distillation. The unit
    // count is the canonical relation-unit count; the site count is
    // permutation-invariant (same cones, only re-numbered), so sizing here is
    // stable across every candidate's own re-distilled domain.
    let d0 = distill(layer, regime, cross, None);
    let n_units = d0.unit_order.len();
    let n_sites = distilled_site_domain(&d0).len();

    let mut rng = SeedRng::new(cfg.seed);
    let seeds = seed_population(n_units, n_sites, cfg.pop.min(cfg.evals), &mut rng);

    let mut evals = 0usize;
    let mut pop: Vec<(Genome, BwdScore)> = seeds
        .into_iter()
        .map(|g| {
            let (_, _, s) = score_candidate(&g, layer, regime, cross, budget);
            evals += 1;
            (g, s)
        })
        .collect();
    assert!(!pop.is_empty(), "seed population must be non-empty");

    // Generational (μ+λ) loop: breed a cohort, score it, keep the best `pop`.
    while evals < cfg.evals {
        let cohort_cap = cfg.pop.min(cfg.evals - evals);
        if cohort_cap == 0 {
            break;
        }
        let mut offspring: Vec<(Genome, BwdScore)> = Vec::with_capacity(cohort_cap);
        for _ in 0..cohort_cap {
            let i1 = tournament(&pop, &mut rng);
            let i2 = tournament(&pop, &mut rng);
            let order_key = order_crossover(&pop[i1].0.root_order_key, &pop[i2].0.root_order_key, &mut rng);
            let cache_priority: Vec<f64> = pop[i1]
                .0
                .cache_priority
                .iter()
                .zip(&pop[i2].0.cache_priority)
                .map(|(&a, &b)| blx(a, b, &mut rng))
                .collect();
            let mut child = Genome { root_order_key: order_key, cache_priority };
            mutate(&mut child, cfg.mutation_sigma, &mut rng);
            assert_normalized_genome(&child); // clamps guarantee this; loud if a NaN slips through
            let (_, _, s) = score_candidate(&child, layer, regime, cross, budget);
            evals += 1;
            offspring.push((child, s));
        }
        pop.extend(offspring);
        pop.sort_by_key(|(_, s)| objective_key(s));
        pop.truncate(cfg.pop);
    }

    // Rebuild the winning candidate's decisions + permutation (deterministic).
    let best = pop
        .into_iter()
        .min_by_key(|(_, s)| objective_key(s))
        .expect("non-empty population");
    let (unit_permutation, decisions, score) =
        score_candidate(&best.0, layer, regime, cross, budget);
    assert!(
        !score.infeasible,
        "search_bwd_layer: best candidate infeasible at budget {budget} \
         ({n_units} units, {n_sites} sites)"
    );

    BwdSearchOutcome { decisions, unit_permutation, stats: score.stats }
}
