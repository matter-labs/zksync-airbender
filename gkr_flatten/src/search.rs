//! Score, zero-search baselines, and CELF priced greedy (spec M2 §6).
//!
//! [`Score`] is the walker's objective: `(traffic, instrs)` compared
//! lexicographically — traffic (DRAM touches) dominates, instruction count
//! only breaks ties. The two-field order is binding: `derive(Ord)` on a
//! struct is lexicographic over fields in declaration order, so `traffic`
//! must be declared first. The objective is never blended into a single
//! scalar — that would let a large `instrs` improvement mask a real traffic
//! regression, which is exactly backwards for a DRAM-bound cost model.
//!
//! [`neutral_genome`] / [`naive_fill_genome`] wrap [`crate::genome::Genome`]'s
//! two endpoint constructors (`ceiling`/`all_admit`) as the zero-search
//! baselines every real search (this greedy, and Task 7's GA) must beat.
//!
//! [`greedy`] is lazy (CELF) greedy over the site domain: round 0 prices
//! every admissible locus's marginal gain with one walk each, then a
//! max-heap of stale gains lets later rounds skip re-evaluating loci whose
//! last-known gain is already worse than the current top's fresh gain
//! (submodularity's lazy-forward-selection argument — O1: "greedy is
//! oracle-grade when the model is the emitter", i.e. when the score is a
//! real walk over the real oracle rather than a proxy, lazy greedy's picks
//! are as good as eagerly re-scoring every candidate every round, just far
//! cheaper). Gains are compared lexicographically via the same
//! `(traffic_saved, instrs_saved)` ordering as `Score`; ties break on the
//! lowest locus index (`Reverse(locus)` in the max-heap key) so two runs
//! over the same table produce the identical sequence of admissions.

use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::BinaryHeap;

use cs::gkr_compiler::dag_ir::ExprId;

use crate::dag::LayerView;
use crate::genome::{decode, Genome, SplitMix64};
use crate::oracle::{SiteTable, UseCounts};
use crate::order::{OrderCtx, OrderPolicy};
use crate::walk::flatten_with;

/// The walker's objective: DRAM traffic first, instruction count as a
/// tiebreak. `derive(Ord)` is lexicographic over fields in declaration
/// order — `traffic` must stay first, this is spec-binding, not incidental.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Score {
    pub traffic: u64,
    pub instrs: u64,
}

/// Evaluation context threaded through the `*_ctx` search variants (spec M3).
/// `counts` is the per-value use countdown that engages the dead-aware
/// residency (Task 3); `policy` (Task 6, default [`OrderPolicy::Su`]) and
/// `order` select and drive the walker's fold-order channel (Task 5/6) — a
/// `RefCell` because `score_ctx` rebuilds its genome-dependent `fills` map
/// in place per genome (serial GA ⇒ never contended). `Default` (`Su`
/// policy, both counts and order `None`) recovers the M2 counts-free walk
/// byte-for-byte, which is what makes the old `score`/`greedy`/`ga` names
/// thin wrappers over their `*_ctx` bodies.
#[derive(Default)]
pub struct EvalCtx<'a> {
    /// Per-value use totals for the dead-aware walk; `None` = M2 behavior
    /// (no countdown, no early death, byte-identical to `flatten_budgeted`).
    pub counts: Option<&'a UseCounts>,
    /// The fold-order policy (spec M3/Task 6). Default `Su` — the M1/M2
    /// order, byte-identical to every pre-M3 search.
    pub policy: OrderPolicy,
    /// The read-only order channel a non-`Su` `policy` requires (asserted by
    /// [`crate::walk::flatten_with`]); `None` under `Su`.
    pub order: Option<RefCell<OrderCtx<'a>>>,
}

/// One walk over `g` decoded against `table`, reduced to its `Score`. Under a
/// non-`Su` `ctx.policy` with a nonzero `fill_weight`, first rebuilds
/// `ctx.order`'s genome-dependent `fills` map for `g` (serial GA never
/// contends the `RefCell`); then routes through
/// [`crate::walk::flatten_with`] with `ctx.policy`/`ctx.order`. With the
/// `EvalCtx::default` the M2 wrapper passes (`Su`, no counts, no order) this
/// is exactly the pre-M3 `flatten_budgeted` walk; with `counts: Some` it
/// engages the dead-aware residency.
pub fn score_ctx(
    view: &LayerView<'_>,
    table: &SiteTable,
    g: &Genome,
    budget: Option<u32>,
    ctx: &EvalCtx<'_>,
) -> Score {
    let fill_weight = match ctx.policy {
        OrderPolicy::Derived(p) | OrderPolicy::DerivedBiased(p) => p.fill_weight,
        OrderPolicy::Su | OrderPolicy::Searched => 0,
    };
    if fill_weight != 0 {
        if let Some(order) = &ctx.order {
            order.borrow_mut().set_fills(g, view);
        }
    }
    let oracle = decode(g, table);
    let borrowed = ctx.order.as_ref().map(|o| o.borrow());
    let out = flatten_with(view, &oracle, budget, ctx.policy, ctx.counts, borrowed.as_deref());
    Score { traffic: out.stats.traffic, instrs: out.stats.instrs }
}

/// M2 wrapper: `score_ctx` with the counts-free default context.
pub fn score(view: &LayerView<'_>, table: &SiteTable, g: &Genome, budget: Option<u32>) -> Score {
    score_ctx(view, table, g, budget, &EvalCtx::default())
}

/// Zero-search baseline: refuses every site (`Genome::ceiling`) — decodes to
/// `NeutralOracle`-equivalent behavior (all-recompute ceiling).
pub fn neutral_genome(table: &SiteTable, n_roots: usize) -> Genome {
    Genome::ceiling(table, n_roots)
}

/// Zero-search baseline: admits every admissible site at a flat priority
/// (`Genome::all_admit`) — naive "cache everything" fill, no ranking.
pub fn naive_fill_genome(table: &SiteTable, n_roots: usize) -> Genome {
    Genome::all_admit(table, n_roots)
}

/// Lazy (CELF) greedy over the admissible site domain: round 0 prices every
/// candidate's marginal gain with one walk each; each subsequent round pops
/// the max-heap's top stale gain, re-evaluates it fresh, and commits it only
/// if the fresh gain still beats the (still-stale) runner-up — otherwise
/// reinserts it with its fresh gain and continues. Stops the moment the best
/// available gain (stale or fresh) is not a strict lexicographic
/// improvement over the current score.
///
/// Encodes the result as a `Genome`: the `rank`-th site enabled (0-indexed,
/// in commit order) gets gene `(enabled.len() - rank) as u16` — earlier
/// (higher marginal-gain) picks get the highest genes, so they're the last
/// evicted if a downstream consumer ever thresholds this genome. Disabled
/// loci keep gene `0`, `threshold` is `0`, `root_keys` is the identity
/// order (greedy never touches root visitation, only cache admission).
///
/// `ctx` threads the M3 eval context (`counts`) into every internal
/// `score_ctx` price; [`greedy`] is the counts-free `EvalCtx::default`
/// wrapper.
pub fn greedy_ctx(
    view: &LayerView<'_>,
    table: &SiteTable,
    n_roots: usize,
    budget: Option<u32>,
    ctx: &EvalCtx<'_>,
) -> Genome {
    let genome_of = |enabled: &[u32]| -> Genome {
        debug_assert!(
            enabled.len() <= u16::MAX as usize,
            "greedy enabled-set exceeds u16 gene range"
        );
        let mut keep = vec![0u16; table.len()];
        for (rank, &locus) in enabled.iter().enumerate() {
            keep[locus as usize] = (enabled.len() - rank) as u16;
        }
        Genome {
            root_keys: (0..n_roots as u32).collect(),
            keep,
            threshold: 0,
            order_bias: vec![0; table.len()],
        }
    };
    let mut enabled: Vec<u32> = Vec::new();
    let mut current = score_ctx(view, table, &genome_of(&enabled), budget, ctx);

    // (gain vs current, locus). Gains are lexicographic improvements encoded
    // as (traffic_saved, instrs_saved) — larger is better in the heap.
    let mut heap: BinaryHeap<((i64, i64), Reverse<u32>)> = BinaryHeap::new();
    let gain_of = |current: Score, candidate: Score| -> (i64, i64) {
        (
            current.traffic as i64 - candidate.traffic as i64,
            current.instrs as i64 - candidate.instrs as i64,
        )
    };
    let admissible: Vec<u32> =
        (0..table.len() as u32).filter(|&l| table.sites[l as usize].admissible).collect();
    for &l in &admissible {
        let mut trial = enabled.clone();
        trial.push(l);
        let s = score_ctx(view, table, &genome_of(&trial), budget, ctx);
        heap.push((gain_of(current, s), Reverse(l)));
    }
    while let Some((stale_gain, Reverse(l))) = heap.pop() {
        if stale_gain <= (0, 0) {
            break; // even the stale (optimistic) bound is no improvement
        }
        let mut trial = enabled.clone();
        trial.push(l);
        let s = score_ctx(view, table, &genome_of(&trial), budget, ctx);
        let fresh = gain_of(current, s);
        let next_best = heap.peek().map(|&(g, _)| g).unwrap_or((i64::MIN, i64::MIN));
        if fresh >= next_best {
            if fresh <= (0, 0) {
                break;
            }
            enabled.push(l);
            current = s;
        } else {
            heap.push((fresh, Reverse(l)));
        }
    }
    genome_of(&enabled)
}

/// M2 wrapper: [`greedy_ctx`] with the counts-free default context.
pub fn greedy(view: &LayerView<'_>, table: &SiteTable, n_roots: usize, budget: Option<u32>) -> Genome {
    greedy_ctx(view, table, n_roots, budget, &EvalCtx::default())
}

/// Tunables for [`ga`] (spec §6). `Default` is the M2-exit strength:
/// `pop: 64`, `max_evals: 2000`, `elites: 8`, `descent_flips: 16`, `seed: 0`,
/// `mutate_bias: false`.
#[derive(Clone, Copy, Debug)]
pub struct GaParams {
    /// Population size (seeds + `Genome::random` fill up to this).
    pub pop: usize,
    /// Total eval budget: EVERY `score` call (initial population, offspring,
    /// and local-descent trials) counts against this; the run stops the
    /// moment it is spent.
    pub max_evals: u64,
    /// Best `elites` genomes carried into the next generation UNCHANGED (and
    /// unre-scored — `score` is a pure function of genome + view + budget).
    pub elites: usize,
    /// Rationed local-descent budget: up to this many single-locus random
    /// flips on the single best each generation, improvements kept.
    pub descent_flips: u32,
    /// PRNG seed — the sole source of nondeterminism, so two `ga` runs with
    /// equal inputs (incl. seed) produce the identical best genome + score.
    pub seed: u64,
    /// Task 6: when `true`, [`mutate`] also perturbs `order_bias` genes
    /// (typically paired with `DerivedBiased`/`Searched` policies). Default
    /// `false` — the M2 gene space (`keep`/`root_keys`) is untouched by this
    /// flag, and its RNG draws stay byte-identical to M2 when it is `false`
    /// (the bias-mutation loop is skipped entirely, not merely a no-op draw).
    pub mutate_bias: bool,
}

impl Default for GaParams {
    fn default() -> Self {
        GaParams { pop: 64, max_evals: 2000, elites: 8, descent_flips: 16, seed: 0, mutate_bias: false }
    }
}

/// Generational, serial, deterministic memetic GA over a layer's genome space
/// (spec §6). The population starts as `seeds` (truncated to `params.pop`)
/// plus `Genome::random` fill; each generation sorts by [`Score`] (stable —
/// ties keep prior order), carries `params.elites` best genomes forward
/// unchanged, applies rationed local descent to the single best, and breeds
/// the remainder by tournament-of-2 + uniform crossover + per-locus mutation
/// (≈ `4/len`). EVERY `score` call — initial population, offspring, and every
/// descent trial — counts against `params.max_evals`; the loop ends the
/// moment the budget is spent. Returns the BEST-EVER `(genome, score)` seen
/// across all score calls (the first genome, in evaluation order, achieving
/// the minimum score — stable across runs), never merely the final
/// generation's best.
///
/// Determinism rests on a single `SplitMix64` stream seeded from
/// `params.seed`: initial random fill, tournament draws, crossover coins, and
/// mutation/descent gene draws all consume it in a fixed order, and `score`
/// itself is pure — so identical inputs reproduce the identical run.
///
/// Elitism is the regression net the M2 gates lean on: because all seeds are
/// scored in the initial population and best-ever tracks the global minimum,
/// the returned score can never be worse than the best seed (in particular
/// never worse than the greedy seed a caller passes in).
///
/// `ctx` threads the M3 eval context (`counts`) through every internal
/// `score_ctx` price; [`ga`] is the counts-free `EvalCtx::default` wrapper.
pub fn ga_ctx(
    view: &LayerView<'_>,
    table: &SiteTable,
    n_roots: usize,
    budget: Option<u32>,
    params: &GaParams,
    seeds: Vec<Genome>,
    ctx: &EvalCtx<'_>,
) -> (Genome, Score) {
    let mut rng = SplitMix64(params.seed);
    let mut spent: u64 = 0;
    let mut best: Option<(Genome, Score)> = None;

    // Mutable-locus domain for crossover/mutation/descent: keep genes first
    // (`0..keep_len`), then root-order keys (`keep_len..`). `threshold` is a
    // crossover-only gene (inherited from either parent, never per-locus
    // mutated).
    let keep_len = table.len();
    let n_loci = keep_len + n_roots;

    // Initial population: seeds (truncated to `pop`), then random fill.
    let mut population: Vec<Genome> = seeds;
    population.truncate(params.pop);
    while population.len() < params.pop {
        population.push(Genome::random(table, n_roots, &mut rng));
    }

    // Score the initial population; each counts against the budget.
    let mut scored: Vec<(Genome, Score)> = Vec::with_capacity(population.len());
    for g in population {
        if spent >= params.max_evals {
            return best.expect("gkr_flatten: ga max_evals too small to score any genome");
        }
        let s = eval_counted(view, table, budget, &g, ctx, &mut spent, &mut best);
        scored.push((g, s));
    }

    let elites = params.elites.min(scored.len());

    loop {
        if scored.is_empty() || spent >= params.max_evals {
            return best.expect("gkr_flatten: ga scored no genome");
        }
        let spent_before = spent;

        // Deterministic ranking: stable sort (ties keep prior order).
        scored.sort_by_key(|(_, s)| *s);

        // Rationed local descent on the single best; keep improvements. The
        // descended genome replaces `scored[0]`, so it carries forward as an
        // elite.
        let (mut dg, mut ds) = scored[0].clone();
        for _ in 0..params.descent_flips {
            if spent >= params.max_evals {
                break;
            }
            let mut trial = dg.clone();
            flip_one_locus(&mut trial, n_loci, keep_len, &mut rng);
            let ts = eval_counted(view, table, budget, &trial, ctx, &mut spent, &mut best);
            if ts < ds {
                dg = trial;
                ds = ts;
            }
        }
        scored[0] = (dg, ds);

        // Breed the next generation: carry elites unchanged, fill the rest by
        // tournament-of-2 + uniform crossover + per-locus mutation.
        let mut next: Vec<(Genome, Score)> = Vec::with_capacity(scored.len());
        next.extend(scored[..elites].iter().cloned());
        while next.len() < scored.len() {
            if spent >= params.max_evals {
                return best.expect("gkr_flatten: ga scored no genome");
            }
            let pa = &scored[tournament(&scored, &mut rng)].0;
            let pb = &scored[tournament(&scored, &mut rng)].0;
            let mut child = crossover(pa, pb, &mut rng);
            mutate(&mut child, n_loci, params.mutate_bias, &mut rng);
            let s = eval_counted(view, table, budget, &child, ctx, &mut spent, &mut best);
            next.push((child, s));
        }
        scored = next;

        // Guard against a degenerate config that would spin forever (e.g.
        // `descent_flips == 0` and `elites >= pop`, so a whole generation
        // makes zero score calls).
        if spent == spent_before {
            return best.expect("gkr_flatten: ga scored no genome");
        }
    }
}

/// M2 wrapper: [`ga_ctx`] with the counts-free default context.
pub fn ga(
    view: &LayerView<'_>,
    table: &SiteTable,
    n_roots: usize,
    budget: Option<u32>,
    params: &GaParams,
    seeds: Vec<Genome>,
) -> (Genome, Score) {
    ga_ctx(view, table, n_roots, budget, params, seeds, &EvalCtx::default())
}

/// One `score_ctx` call that increments the spend counter and folds the result
/// into the best-ever tracker. Best-ever is updated only on a STRICT
/// improvement, so ties keep the first (evaluation-order) genome — the tie
/// rule that makes the returned genome reproducible across runs. `ctx` is the
/// M3 eval context threaded from `ga_ctx` (counts-free under `ga`).
fn eval_counted(
    view: &LayerView<'_>,
    table: &SiteTable,
    budget: Option<u32>,
    g: &Genome,
    ctx: &EvalCtx<'_>,
    spent: &mut u64,
    best: &mut Option<(Genome, Score)>,
) -> Score {
    let s = score_ctx(view, table, g, budget, ctx);
    *spent += 1;
    if best.as_ref().map_or(true, |(_, bs)| s < *bs) {
        *best = Some((g.clone(), s));
    }
    s
}

/// One single-locus random flip over the `(keep, root_keys)` gene space:
/// picks a uniform locus and replaces that gene with a fresh random draw.
/// Loci `0..keep_len` address `keep` (u16 genes); `keep_len..` address
/// `root_keys` (u32 genes). Always consumes two RNG draws, so the stream
/// stays branch-independent.
fn flip_one_locus(g: &mut Genome, n_loci: usize, keep_len: usize, rng: &mut SplitMix64) {
    if n_loci == 0 {
        return;
    }
    let locus = rng.below(n_loci as u64) as usize;
    let gene = rng.next_u64();
    if locus < keep_len {
        g.keep[locus] = gene as u16;
    } else {
        g.root_keys[locus - keep_len] = gene as u32;
    }
}

/// Tournament-of-2: two uniform draws over the population, the lower-[`Score`]
/// (better) contestant wins. Ties go to the first draw — deterministic.
fn tournament(scored: &[(Genome, Score)], rng: &mut SplitMix64) -> usize {
    let a = rng.below(scored.len() as u64) as usize;
    let b = rng.below(scored.len() as u64) as usize;
    if scored[a].1 <= scored[b].1 {
        a
    } else {
        b
    }
}

/// Uniform crossover: each `keep`/`order_bias` locus pair takes its genes
/// from parent `a` or `b` by ONE shared independent coin per locus (Task 6:
/// `order_bias` "copies per-locus like keep" — riding `keep`'s own coin costs
/// zero extra RNG draws, so the RNG stream `keep`/`root_keys`/`threshold`
/// consume is byte-identical to M2's crossover regardless of whether the
/// bias vector is all-zero or not); each `root_keys` locus takes its own
/// independent coin; `threshold` likewise comes from either parent. Parents
/// were built against the same table/root count, so their gene vectors align
/// by index.
fn crossover(a: &Genome, b: &Genome, rng: &mut SplitMix64) -> Genome {
    let (keep, order_bias) = a
        .keep
        .iter()
        .zip(&b.keep)
        .zip(a.order_bias.iter().zip(&b.order_bias))
        .map(|((&kx, &ky), (&bx, &by))| {
            if rng.next_u64() & 1 == 0 {
                (kx, bx)
            } else {
                (ky, by)
            }
        })
        .unzip();
    let root_keys = a
        .root_keys
        .iter()
        .zip(&b.root_keys)
        .map(|(&x, &y)| if rng.next_u64() & 1 == 0 { x } else { y })
        .collect();
    let threshold = if rng.next_u64() & 1 == 0 { a.threshold } else { b.threshold };
    Genome { root_keys, keep, threshold, order_bias }
}

/// Per-locus mutation at probability ≈ `4/n_loci`: each `keep` and
/// `root_keys` locus is independently replaced by a fresh random gene when a
/// uniform draw in `0..n_loci` lands below 4 (so ≈ 4 loci mutate per genome).
/// `order_bias` mutates the same way, but ONLY when `mutate_bias` is set
/// (Task 6), and its loop runs strictly AFTER `keep`/`root_keys` so that when
/// `mutate_bias` is `false` the loop is skipped entirely — zero extra RNG
/// draws, keeping the `keep`/`root_keys` stream byte-identical to M2's
/// `mutate` (the regression net every fixed-seed M2 GA test leans on).
fn mutate(g: &mut Genome, n_loci: usize, mutate_bias: bool, rng: &mut SplitMix64) {
    if n_loci == 0 {
        return;
    }
    for k in g.keep.iter_mut() {
        if rng.below(n_loci as u64) < 4 {
            *k = rng.next_u64() as u16;
        }
    }
    for rk in g.root_keys.iter_mut() {
        if rng.below(n_loci as u64) < 4 {
            *rk = rng.next_u64() as u32;
        }
    }
    if mutate_bias {
        for b in g.order_bias.iter_mut() {
            if rng.below(n_loci as u64) < 4 {
                *b = rng.next_u64() as i16;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn score_is_lexicographic() {
        assert!(Score { traffic: 5, instrs: 900 } < Score { traffic: 6, instrs: 1 });
        assert!(Score { traffic: 5, instrs: 1 } < Score { traffic: 5, instrs: 2 });
    }

    #[test]
    fn greedy_finds_the_shared_compound() {
        // shared_diamond: caching the shared compound is the single best (and
        // only useful) decision — greedy must reach the floor.
        let layer = crate::dag::testdag::shared_diamond();
        let cross = std::collections::HashMap::new();
        let v = LayerView::new(&layer, &cross, None);
        let roots: Vec<ExprId> = layer.roots.iter().map(|r| r.expr).collect();
        let report = crate::analysis::size_layer(&v, &roots);
        let table = SiteTable::enumerate(&v);
        let g = greedy(&v, &table, layer.roots.len(), Some(16));
        assert_eq!(score(&v, &table, &g, Some(16)).traffic, report.floor);
    }

    #[test]
    fn greedy_never_loses_to_zero_search_baselines() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let roots: Vec<ExprId> = dag.layers[0].roots.iter().map(|r| r.expr).collect();
        let report = crate::analysis::size_layer(&v, &roots);
        let table = SiteTable::enumerate(&v);
        let n = dag.layers[0].roots.len();
        for budget in [Some(report.peak + 2), Some(16)] {
            let s_greedy = score(&v, &table, &greedy(&v, &table, n, budget), budget);
            let s_neutral = score(&v, &table, &neutral_genome(&table, n), budget);
            let s_naive = score(&v, &table, &naive_fill_genome(&table, n), budget);
            assert!(s_greedy <= s_neutral, "greedy {s_greedy:?} vs neutral {s_neutral:?} @ {budget:?}");
            assert!(s_greedy <= s_naive, "greedy {s_greedy:?} vs naive {s_naive:?} @ {budget:?}");
            assert!(s_greedy.traffic >= report.floor, "bracket");
        }
    }

    #[test]
    fn greedy_is_deterministic() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let table = SiteTable::enumerate(&v);
        let n = dag.layers[0].roots.len();
        let a = greedy(&v, &table, n, Some(12));
        let b = greedy(&v, &table, n, Some(12));
        assert_eq!(a, b);
    }

    #[test]
    fn ga_is_deterministic_and_never_loses_to_its_seeds() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let roots: Vec<ExprId> = dag.layers[0].roots.iter().map(|r| r.expr).collect();
        let report = crate::analysis::size_layer(&v, &roots);
        let table = SiteTable::enumerate(&v);
        let n = dag.layers[0].roots.len();
        let budget = Some(report.peak + 2);
        let params = GaParams { pop: 8, max_evals: 120, elites: 2, descent_flips: 4, seed: 3, ..GaParams::default() };
        let seeds = vec![
            neutral_genome(&table, n),
            naive_fill_genome(&table, n),
            greedy(&v, &table, n, budget),
        ];
        let seed_best = seeds.iter().map(|g| score(&v, &table, g, budget)).min().unwrap();
        let (g1, s1) = ga(&v, &table, n, budget, &params, seeds.clone());
        let (g2, s2) = ga(&v, &table, n, budget, &params, seeds);
        assert_eq!(g1, g2);
        assert_eq!(s1, s2);
        assert!(s1 <= seed_best, "elitism: GA never worse than its best seed");
        assert!(s1.traffic >= report.floor, "bracket");
    }

    #[test]
    fn ga_with_bias_is_deterministic_and_elitist() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let roots: Vec<ExprId> = dag.layers[0].roots.iter().map(|r| r.expr).collect();
        let report = crate::analysis::size_layer(&v, &roots);
        let table = SiteTable::enumerate(&v);
        let n = dag.layers[0].roots.len();
        let budget = Some(report.peak + 2);
        let n_exprs = dag.layers[0].exprs.len();
        let counts = table.use_counts(n_exprs);
        let order = crate::order::OrderCtx::new(&table, n_exprs);
        let ctx = EvalCtx {
            counts: Some(&counts),
            policy: crate::order::OrderPolicy::Searched,
            order: Some(std::cell::RefCell::new(order)),
        };
        let params =
            GaParams { pop: 8, max_evals: 120, elites: 2, descent_flips: 4, seed: 5, mutate_bias: true };
        let seeds = vec![
            neutral_genome(&table, n),
            naive_fill_genome(&table, n),
            greedy(&v, &table, n, budget),
        ];
        // Apples-to-apples: score the seeds through the SAME (Searched, counted)
        // ctx `ga_ctx` scores its initial population with, not the M2 `score`.
        let seed_best =
            seeds.iter().map(|g| score_ctx(&v, &table, g, budget, &ctx)).min().unwrap();
        let (g1, s1) = ga_ctx(&v, &table, n, budget, &params, seeds.clone(), &ctx);
        let (g2, s2) = ga_ctx(&v, &table, n, budget, &params, seeds, &ctx);
        assert_eq!(g1, g2, "GA with bias must be deterministic");
        assert_eq!(s1, s2);
        assert!(s1 <= seed_best, "elitism: GA never worse than its best seed");
        assert!(s1.traffic >= report.floor, "bracket");
    }

    #[test]
    fn mutation_leaves_bias_untouched_when_disabled() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let roots: Vec<ExprId> = dag.layers[0].roots.iter().map(|r| r.expr).collect();
        let report = crate::analysis::size_layer(&v, &roots);
        let table = SiteTable::enumerate(&v);
        let n = dag.layers[0].roots.len();
        let budget = Some(report.peak + 2);
        let seeds = vec![
            neutral_genome(&table, n),
            naive_fill_genome(&table, n),
            greedy(&v, &table, n, budget),
        ];
        assert!(
            seeds.iter().all(|g| g.order_bias.iter().all(|&b| b == 0)),
            "precondition: zero-bias seeds"
        );
        // pop == seeds.len(): no `Genome::random` fill, so nothing but
        // crossover-copied (still all-zero) bias ever enters the population.
        let params = GaParams {
            pop: seeds.len(),
            max_evals: 60,
            elites: 1,
            descent_flips: 4,
            seed: 9,
            mutate_bias: false,
        };
        let (best, _) = ga(&v, &table, n, budget, &params, seeds);
        assert!(
            best.order_bias.iter().all(|&b| b == 0),
            "mutate_bias: false must leave bias untouched"
        );
    }
}
