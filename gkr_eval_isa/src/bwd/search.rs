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
//! * **cache-priority genes** map to a canonical-provenance site ordering that
//!   is invariant under re-distillation. Each candidate translates those stable
//!   keys to its own distilled
//!   [`SiteKey`](cs::gkr_compiler::dag_ir::SiteKey)s before producing the
//!   [`SiteDecisions`] the bwd compiler consumes.
//! * **initial genomes** include a deterministic structure-aware pair: a greedy
//!   maximum-reuse-adjacency unit order and its reverse, with cache priorities
//!   initialized from uncached DRAM benefit per width×lifetime lane. The exact
//!   compile remains the scorer; these are warm starts, not trusted decisions.
//! * **order mutation** can use that same weighted reuse graph to relocate one
//!   endpoint of a currently non-adjacent reuse edge beside the other. It is a
//!   coherent permutation edit; cache genes retain their independent mutation.
//!
//! Fitness ([`score_candidate`]) is the REAL compile: ordered
//! `(infeasible, global + fold_traffic, program_lanes)` from
//! [`BwdCompiledLayer::stats_ext`] — the Task-5 `fold_traffic` tally makes the Ext
//! search see its dominant FoldSource reads (invisible to `CompileStats`).
//!
//! Determinism: the breeding RNG is an explicit-seed LCG (mirrors the fwd
//! `SeedRng`); no wall-clock seeding — repeated runs with the same
//! `BwdSearchConfig` produce identical results. Candidate SCORING (the real
//! [`compile_distilled`] call inside [`score_candidate`]) runs in parallel via
//! rayon `par_iter`, but this does not change the outcome: every RNG draw
//! (`tournament`/`order_crossover`/`blx`/`mutate`) stays in a sequential
//! breeding phase that runs to completion BEFORE any parallel scoring starts,
//! `score_candidate` is a pure function of its inputs (no shared mutable
//! state), and `collect()` preserves input order — so `pop`/`offspring`
//! ordering, and therefore every subsequent `tournament` selection, is
//! byte-identical to the fully-sequential version regardless of thread count.

use std::collections::HashMap;

use rayon::prelude::*;

use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, FieldKind, ReadPlace};

use crate::bwd::compile::{compile_distilled, BwdTrafficStats};
use crate::bwd::distill::{distill, stable_distilled_site_domain, StableBwdSiteKey};
use crate::fwd::compile::SiteDecisions;
use crate::fwd::error::CompileError;
use crate::schedule_search::decode::decode_unit_order;
use crate::schedule_search::genome::{assert_normalized_genome, clamp_bias, Genome};

use super::structure::ReuseStructure;

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
    /// Initial-population strategy. Selection, crossover, and mutation are
    /// otherwise identical between modes, making `Legacy` an equal-evaluation
    /// A/B control when paired with the same `order_mutation`.
    pub seed_strategy: BwdSeedStrategy,
    /// Mutation operator for the unit permutation.
    pub order_mutation: BwdOrderMutation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BwdSeedStrategy {
    /// Stable reuse graph + interval-density cache priorities.
    StructureAware,
    /// Previous neutral + reversed-neutral + random-tail population.
    Legacy,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BwdOrderMutation {
    /// Relocate an endpoint of a weighted, currently non-adjacent reuse edge
    /// directly beside its peer, preserving every other relative ordering.
    ReuseEdgeRelocate,
    /// Previous independent Gaussian mutation of each random key.
    PerKey,
}

impl Default for BwdSearchConfig {
    fn default() -> Self {
        Self {
            pop: 4,
            evals: 40,
            seed: 0,
            mutation_sigma: 0.2,
            seed_strategy: BwdSeedStrategy::StructureAware,
            order_mutation: BwdOrderMutation::ReuseEdgeRelocate,
        }
    }
}

/// Result of searching one backward layer × regime: the winning
/// [`SiteDecisions`] (keyed to the winning candidate's distilled site domain;
/// `None` = compile with NO decisions — the uncached per-demand-recompute
/// baseline, returned whenever no GA candidate strictly beats it, which makes
/// non-regression true BY CONSTRUCTION), its `unit_permutation` (feed back into
/// [`distill`] to reproduce the schedule; canonical identity for the baseline),
/// and the winning compile's search-facing traffic stats.
pub struct BwdSearchOutcome {
    pub decisions: Option<SiteDecisions>,
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
/// permutation yields the candidate's own site domain. Stable canonical
/// provenance supplies a permutation-invariant gene order, whose entries are
/// translated to the candidate's concrete distilled `SiteKey`s for compilation.
fn score_candidate(
    genome: &Genome,
    stable_site_keys: &[StableBwdSiteKey],
    layer: &DagLayer,
    regime: BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
) -> (Vec<usize>, SiteDecisions, BwdScore) {
    let perm = decode_unit_order(&genome.root_order_key);
    let d = distill(layer, regime, cross, Some(&perm));
    let stable_sites = stable_distilled_site_domain(&d);
    assert_eq!(
        stable_sites.len(),
        stable_site_keys.len(),
        "candidate and canonical stable site domains must have equal size"
    );
    assert_eq!(
        stable_site_keys.len(),
        genome.cache_priority.len(),
        "canonical stable site domain must match the cache-priority genome"
    );
    let decisions = SiteDecisions::new(
        stable_site_keys
            .iter()
            .zip(genome.cache_priority.iter().copied())
            .map(|(stable_key, priority)| {
                let site = *stable_sites.get(stable_key).unwrap_or_else(|| {
                    panic!("candidate is missing canonical stable site {stable_key:?}")
                });
                (site, priority)
            }),
    );

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

/// Relocate one endpoint of a weighted, currently non-adjacent reuse edge next
/// to the other endpoint. The weighted choice prioritizes relations whose
/// uncached shared cone has the largest estimated DRAM consequence.
fn relocate_reuse_edge(
    keys: &mut Vec<f64>,
    structure: &ReuseStructure,
    rng: &mut SeedRng,
) -> bool {
    let mut order = decode_unit_order(keys);
    let mut position = vec![0usize; order.len()];
    for (index, &unit) in order.iter().enumerate() {
        position[unit] = index;
    }

    let total_weight = structure
        .weighted_edges
        .iter()
        .filter(|edge| position[edge.left].abs_diff(position[edge.right]) > 1)
        .fold(0u128, |total, edge| total + edge.weight as u128);
    if total_weight == 0 {
        return false;
    }

    let mut ticket = rng.next_u64() as u128 % total_weight;
    let edge = structure
        .weighted_edges
        .iter()
        .filter(|edge| position[edge.left].abs_diff(position[edge.right]) > 1)
        .find(|edge| {
            if ticket < edge.weight as u128 {
                true
            } else {
                ticket -= edge.weight as u128;
                false
            }
        })
        .expect("positive total weight must select a reuse edge");

    let (moving, anchor) = if rng.next_u64() & 1 == 0 {
        (edge.left, edge.right)
    } else {
        (edge.right, edge.left)
    };
    let insert_after = rng.next_u64() & 1 != 0;
    order.remove(position[moving]);
    let anchor_position = order
        .iter()
        .position(|unit| *unit == anchor)
        .expect("reuse-edge anchor must remain in the permutation");
    let insertion = anchor_position + usize::from(insert_after);
    order.insert(insertion, moving);
    *keys = encode_order(&order);
    true
}

/// Order mutation selected by the experiment config, followed by unchanged
/// per-site Gaussian cache-priority mutation.
fn mutate(
    g: &mut Genome,
    sigma: f64,
    order_mutation: BwdOrderMutation,
    structure: Option<&ReuseStructure>,
    rng: &mut SeedRng,
) {
    match order_mutation {
        BwdOrderMutation::ReuseEdgeRelocate => {
            relocate_reuse_edge(
                &mut g.root_order_key,
                structure.expect("reuse-edge mutation requires a reuse model"),
                rng,
            );
        }
        BwdOrderMutation::PerKey => {
            for key in &mut g.root_order_key {
                if rng.next_unit() < MUTATION_RATE {
                    *key = (*key + rng.next_gaussian() * sigma).clamp(0.0, 1.0);
                }
            }
        }
    }
    for key in &mut g.root_order_key {
        debug_assert!((0.0..=1.0).contains(key));
    }
    for gene in &mut g.cache_priority {
        if rng.next_unit() < MUTATION_RATE {
            *gene = clamp_bias(*gene + rng.next_gaussian() * sigma);
        }
    }
}

// ── Seed population ────────────────────────────────────────────────────────────

fn encode_order(order: &[usize]) -> Vec<f64> {
    let mut keys = vec![0.0; order.len()];
    let denom = order.len().max(1) as f64;
    for (position, &unit) in order.iter().enumerate() {
        keys[unit] = (position as f64 + 0.5) / denom;
    }
    keys
}

fn structured_seed(structure: &ReuseStructure, reverse: bool) -> Genome {
    let mut order = structure.order.clone();
    if reverse {
        order.reverse();
    }
    let genome = Genome {
        root_order_key: encode_order(&order),
        cache_priority: structure.cache_priorities.clone(),
    };
    assert_normalized_genome(&genome);
    genome
}

/// Keep the neutral baseline, then add a graph-guided order and its reverse
/// before the deterministic random tail. `Legacy` reproduces the previous
/// neutral + reversed-neutral + random-tail initializer for equal-budget A/Bs.
fn seed_population(
    n_units: usize,
    n_sites: usize,
    pop: usize,
    strategy: BwdSeedStrategy,
    structure: Option<&ReuseStructure>,
    rng: &mut SeedRng,
) -> Vec<Genome> {
    let mut genomes = Vec::with_capacity(pop);
    if pop == 0 {
        return genomes;
    }
    genomes.push(Genome::neutral(n_units, n_sites));
    if strategy == BwdSeedStrategy::StructureAware && genomes.len() < pop {
        genomes.push(structured_seed(
            structure.expect("structure-aware seeding requires a reuse model"),
            false,
        ));
    }
    if genomes.len() < pop {
        if strategy == BwdSeedStrategy::StructureAware {
            genomes.push(structured_seed(
                structure.expect("structure-aware seeding requires a reuse model"),
                true,
            ));
        } else {
            let mut reversed = Genome::neutral(n_units, n_sites);
            let n = reversed.root_order_key.len();
            let denom = n.max(1) as f64;
            for (idx, key) in reversed.root_order_key.iter_mut().enumerate() {
                *key = (n - 1 - idx) as f64 / denom;
            }
            genomes.push(reversed);
        }
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
/// types. Every genome scored is a real [`compile_distilled`].
///
/// NON-REGRESSION BY CONSTRUCTION: the `decisions: None` baseline compile at the
/// same budget (canonical unit order, uncached per-demand recompute — the exact
/// compile the fixture gates pin) is always evaluated as the post-hoc floor. If
/// the GA's best candidate is infeasible OR its `(infeasible, traffic, instrs)`
/// key is worse than the baseline's, the baseline outcome is returned
/// (`decisions: None`, identity `unit_permutation`, baseline stats) — so the
/// result is NEVER worse than an unsearched compile, and decision-candidates
/// whose caching raises the placement floor above `budget` (observed: blake2 L0
/// Ext floor 20 > b16) can no longer panic the search.
///
/// Panics only if even the `None` baseline is infeasible at `budget` — a real
/// layer/budget problem (the `PINNED_B16_INFEASIBLE` class), not a schedule one;
/// the message names layer shape, regime, budget, and floor.
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
    // count is the canonical relation-unit count; the stable site count and
    // ordering come from canonical provenance, so sizing here applies to every
    // candidate's own re-distilled domain without changing gene semantics.
    let d0 = distill(layer, regime, cross, None);
    let n_units = d0.unit_order.len();
    let stable_domain = stable_distilled_site_domain(&d0);
    let stable_site_keys: Vec<StableBwdSiteKey> = stable_domain.keys().copied().collect();
    let n_sites = stable_site_keys.len();
    let structure = (cfg.seed_strategy == BwdSeedStrategy::StructureAware
        || cfg.order_mutation == BwdOrderMutation::ReuseEdgeRelocate)
        .then(|| ReuseStructure::build(layer, &d0, &stable_domain));

    // The `None`-decisions baseline: the non-regression floor AND the fallback
    // when every decision-candidate is infeasible. If even this is infeasible,
    // the layer genuinely does not fit the budget — fail loudly with context.
    let baseline = match compile_distilled(&d0, budget, None) {
        Ok(c) => BwdScore {
            infeasible: false,
            traffic: c.stats_ext.global + c.stats_ext.fold_traffic,
            instrs: c.stats.program_lanes,
            stats: c.stats_ext,
        },
        Err(CompileError::BudgetBelowFloor { floor, .. }) => panic!(
            "search_bwd_layer: even the no-decisions baseline is infeasible \
             ({regime:?}, budget {budget}, floor {floor}, {n_units} units, {n_sites} sites)"
        ),
        Err(e) => panic!("search_bwd_layer: baseline compile error: {e:?}"),
    };

    let mut rng = SeedRng::new(cfg.seed);
    let seeds = seed_population(
        n_units,
        n_sites,
        cfg.pop.min(cfg.evals),
        cfg.seed_strategy,
        structure.as_ref(),
        &mut rng,
    );

    let mut evals = 0usize;
    // `seeds` is already fully generated (sequential RNG, `seed_population`
    // above) — no RNG draws happen past this point for the seed cohort, so
    // scoring it via `par_iter` is race-free and `collect()`'s order-preserving
    // semantics keep `pop`'s index order identical to the sequential `map`.
    evals += seeds.len();
    let mut pop: Vec<(Genome, BwdScore)> = seeds
        .into_par_iter()
        .map(|g| {
            let (_, _, s) =
                score_candidate(&g, &stable_site_keys, layer, regime, cross, budget);
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
        // Phase 1: breed the whole cohort sequentially — RNG draw order is IDENTICAL
        // to the pre-parallelization loop (tournament/crossover/blx/mutate unchanged).
        let children: Vec<Genome> = (0..cohort_cap)
            .map(|_| {
                let i1 = tournament(&pop, &mut rng);
                let i2 = tournament(&pop, &mut rng);
                let order_key =
                    order_crossover(&pop[i1].0.root_order_key, &pop[i2].0.root_order_key, &mut rng);
                let cache_priority: Vec<f64> = pop[i1]
                    .0
                    .cache_priority
                    .iter()
                    .zip(&pop[i2].0.cache_priority)
                    .map(|(&a, &b)| blx(a, b, &mut rng))
                    .collect();
                let mut child = Genome { root_order_key: order_key, cache_priority };
                mutate(
                    &mut child,
                    cfg.mutation_sigma,
                    cfg.order_mutation,
                    structure.as_ref(),
                    &mut rng,
                );
                assert_normalized_genome(&child); // clamps guarantee this; loud if a NaN slips through
                child
            })
            .collect();
        evals += children.len();
        // Phase 2: score the cohort in parallel (score_candidate is pure; collect
        // preserves index order, so `offspring` ordering matches the sequential loop).
        let offspring: Vec<(Genome, BwdScore)> = children
            .into_par_iter()
            .map(|child| {
                let (_, _, s) =
                    score_candidate(&child, &stable_site_keys, layer, regime, cross, budget);
                (child, s)
            })
            .collect();
        pop.extend(offspring);
        pop.sort_by_key(|(_, s)| objective_key(s));
        pop.truncate(cfg.pop);
    }

    // Rebuild the winning candidate's decisions + permutation (deterministic).
    let best = pop
        .into_iter()
        .min_by_key(|(_, s)| objective_key(s))
        .expect("non-empty population");
    let (unit_permutation, decisions, score) = score_candidate(
        &best.0,
        &stable_site_keys,
        layer,
        regime,
        cross,
        budget,
    );

    // Post-hoc baseline floor: fall back to the `None`-decisions compile if the
    // GA's best is infeasible or not strictly better — non-regression BY
    // CONSTRUCTION (baseline wins ties: identical traffic with decisions buys
    // nothing over the simpler uncached compile).
    if score.infeasible || objective_key(&score) >= objective_key(&baseline) {
        return BwdSearchOutcome {
            decisions: None,
            unit_permutation: (0..n_units).collect(),
            stats: baseline.stats,
        };
    }

    BwdSearchOutcome { decisions: Some(decisions), unit_permutation, stats: score.stats }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;
    use crate::bwd::structure::ReuseEdge;

    fn structure(edges: Vec<ReuseEdge>) -> ReuseStructure {
        ReuseStructure {
            order: vec![0, 1, 2, 3],
            cache_priorities: Vec::new(),
            weighted_edges: edges,
            value_units: Vec::new(),
        }
    }

    #[test]
    fn reuse_edge_relocation_makes_selected_pair_adjacent() {
        let structure = structure(vec![ReuseEdge {
            left: 0,
            right: 3,
            weight: 100,
        }]);
        let mut keys = encode_order(&[0, 1, 2, 3]);
        assert!(relocate_reuse_edge(
            &mut keys,
            &structure,
            &mut SeedRng::new(7),
        ));
        let order = decode_unit_order(&keys);
        let p0 = order.iter().position(|unit| *unit == 0).unwrap();
        let p3 = order.iter().position(|unit| *unit == 3).unwrap();
        assert_eq!(p0.abs_diff(p3), 1);
        assert_eq!(
            order.iter().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([0, 1, 2, 3]),
        );
    }

    #[test]
    fn reuse_edge_relocation_is_noop_when_all_edges_are_adjacent() {
        let structure = structure(vec![ReuseEdge {
            left: 0,
            right: 1,
            weight: 100,
        }]);
        let original = encode_order(&[0, 1, 2, 3]);
        let mut keys = original.clone();
        assert!(!relocate_reuse_edge(
            &mut keys,
            &structure,
            &mut SeedRng::new(7),
        ));
        assert_eq!(keys, original);
    }

}
