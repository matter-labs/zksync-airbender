//! M3 Phase-0 gate: a dead-aware re-baseline of the M2 budget-sweep harness
//! (spec .agents/specs/2026-07-16-gkr-flattener-m2-search-design.md §7, run
//! under M3's counted walker). It mirrors `tests/m2_search.rs`'s
//! `run_cell`/`assert_parity`/`SweepRow` structure exactly, with one change:
//! every score/greedy/GA call threads the per-value use countdown
//! (`counts = table.use_counts(n_exprs)`, one per instance) through the
//! `search::*_ctx` variants, so the dead-aware residency (`Residency::mark_dead`)
//! engages. Each calibration row is tagged `phase0` so the M2 and M3 audit
//! tables diff line-by-line.
//!
//! Run (fast smoke, non-ignored — CI-safe):
//!   `cargo test -p gkr_flatten --test m3_order smoke`
//! Run (full sweep, release-only):
//!   `RUSTFLAGS="-Awarnings" cargo test -p gkr_flatten --release --test m3_order -- --ignored --nocapture`

use std::cell::RefCell;

use cs::gkr_compiler::dag_ir::eval::eval_layer_root;
use cs::gkr_compiler::dag_ir::{ExprId, RootId};
use gkr_flatten::analysis::size_layer;
use gkr_flatten::dag::LayerView;
use gkr_flatten::fixtures::{bwd_instance, fwd_instance, Instance};
use gkr_flatten::genome::{decode, Genome};
use gkr_flatten::ir::interpret;
use gkr_flatten::order::{DerivedParams, OrderCtx, OrderPolicy};
use gkr_flatten::oracle::{SiteTable, UseCounts};
use gkr_flatten::resolvers::HashResolvers;
use gkr_flatten::search::{
    ga_ctx, greedy_ctx, naive_fill_genome, neutral_genome, score_ctx, EvalCtx, GaParams, Score,
};
use gkr_flatten::walk::{flatten_counted, flatten_with, WalkOutput, WalkStats};

const HEAVY_QUARTET: [&str; 4] = [
    "bigint_with_extended_control_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

struct SweepRow {
    budget: Option<u32>,
    ceiling: u64,
    floor: u64,
    neutral: Score,
    naive: Score,
    greedy: Score,
    ga_best: Score,
}

/// Runs baselines + greedy + GA on one instance at one budget, ALL through the
/// counted (`*_ctx` + `counts`) search variants; asserts the per-budget hard
/// gates; returns the calibration row and the best genome. Deltas from M2's
/// `run_cell`: `counts = table.use_counts(n_exprs)` per instance and every
/// score/greedy/GA call routes through the `_ctx` variant with that context.
fn run_cell(inst: &Instance, budget: Option<u32>, params: &GaParams) -> (SweepRow, Genome) {
    let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
    let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
    let report = size_layer(&view, &roots);
    // Gate 3: peak assert precondition.
    if let Some(b) = budget {
        assert!(b >= report.peak, "{}: budget {b} < neutral peak {}", inst.label, report.peak);
    }
    let table = SiteTable::enumerate(&view);
    // M3 delta: the per-value use countdown for the dead-aware walk.
    let counts = table.use_counts(inst.layer.exprs.len());
    let ctx = EvalCtx { counts: Some(&counts), ..EvalCtx::default() };
    let n = inst.layer.roots.len();

    let s_neutral = score_ctx(&view, &table, &neutral_genome(&table, n), budget, &ctx);
    let s_naive = score_ctx(&view, &table, &naive_fill_genome(&table, n), budget, &ctx);
    let g_greedy = greedy_ctx(&view, &table, n, budget, &ctx);
    let s_greedy = score_ctx(&view, &table, &g_greedy, budget, &ctx);
    let seeds = vec![neutral_genome(&table, n), naive_fill_genome(&table, n), g_greedy.clone()];
    let (g_best, s_ga) = ga_ctx(&view, &table, n, budget, params, seeds, &ctx);

    // Gate 2: determinism (same seed -> same best).
    let seeds2 = vec![neutral_genome(&table, n), naive_fill_genome(&table, n), g_greedy.clone()];
    let (g_best2, s_ga2) = ga_ctx(&view, &table, n, budget, params, seeds2, &ctx);
    assert_eq!(g_best, g_best2, "{}: GA nondeterministic", inst.label);
    assert_eq!(s_ga, s_ga2);

    // Gate 1: bracket, on every headline score.
    let ceiling = s_neutral.traffic;
    for s in [s_neutral, s_naive, s_greedy, s_ga] {
        assert!(s.traffic >= report.floor && s.traffic <= ceiling,
            "{}: bracket violation {s:?} not in [{}, {ceiling}]", inst.label, report.floor);
    }
    // Gate 5 (sanity half): GA ties-or-beats greedy (elitist seeding).
    assert!(s_ga <= s_greedy, "{}: GA lost to its own greedy seed", inst.label);
    // Gate 5 (endpoint): unbounded budget reaches the floor.
    if budget.is_none() {
        assert_eq!(s_ga.traffic, report.floor, "{}: unbounded best must equal floor", inst.label);
    }
    (SweepRow { budget, ceiling, floor: report.floor,
                neutral: s_neutral, naive: s_naive, greedy: s_greedy, ga_best: s_ga },
     if s_ga <= s_greedy { g_best } else { g_greedy })
}

/// Gate 4: the best genome's program still interprets bit-exact vs
/// `eval_layer_root` (rows 0, 1, 17; shared HashResolvers seed 7). M3 delta:
/// the program is re-flattened through the SAME counted walk (`counts` passed
/// to `flatten_counted`) that scored it, so parity validates the dead-aware
/// program actually selected — not a counts-free stand-in.
fn assert_parity(inst: &Instance, table: &SiteTable, best: &Genome, budget: Option<u32>, counts: &UseCounts) {
    let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
    let out = flatten_counted(&view, &decode(best, table), budget, Some(counts));
    let r = HashResolvers { seed: 7 }.bundle();
    for row in [0usize, 1, 17] {
        let got = interpret(&out.program, &inst.layer, row, &r);
        for (i, _) in inst.layer.roots.iter().enumerate() {
            let want = eval_layer_root(&inst.layer, RootId(i as u32), row, &r);
            assert_eq!(got[&RootId(i as u32)], want,
                "{} root {i} row {row}: searched-genome parity broke", inst.label);
        }
    }
}

/// Fast, non-ignored smoke: add_sub fwd L0, one tight budget, tiny GA — counted.
#[test]
fn smoke_add_sub_counted_tight_budget() {
    let inst = fwd_instance("add_sub_lui_auipc_mop_layout_gkr.json");
    let view = LayerView::new(&inst.layer, &inst.cross, None);
    let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
    let report = size_layer(&view, &roots);
    let params = GaParams { pop: 8, max_evals: 120, elites: 2, descent_flips: 4, seed: 0, ..GaParams::default() };
    let (row, best) = run_cell(&inst, Some(report.peak + 2), &params);
    assert!(row.ga_best <= row.neutral);
    let table = SiteTable::enumerate(&view);
    let counts = table.use_counts(inst.layer.exprs.len());
    assert_parity(&inst, &table, &best, Some(report.peak + 2), &counts);
}

/// The M3 Phase-0 re-baseline sweep: the full M2 grid (8 instances × 6 budgets
/// × best-of-seeds {0,1,2}) re-run under the counted walker, with every M2 hard
/// gate re-asserted per cell. Release-only. GA strength per spec §6: pop 64 /
/// evals 2000 / seeds {0, 1, 2} — the win gate takes best-of-seeds.
#[test]
#[ignore = "release-only full sweep (phase-0 re-baseline)"]
fn phase0_rebaseline() {
    let mut calibration: Vec<(String, Vec<SweepRow>)> = Vec::new();

    for name in HEAVY_QUARTET {
        for inst in [fwd_instance(name), bwd_instance(name)] {
            let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
            let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
            let report = size_layer(&view, &roots);
            let table = SiteTable::enumerate(&view);
            let counts = table.use_counts(inst.layer.exprs.len());
            assert!((report.floor as u128) < report.ceiling, "no reuse to search");
            let tight = [Some(report.peak), Some(report.peak + 2)];
            let budgets = [Some(report.peak), Some(report.peak + 2),
                           Some(12), Some(16), Some(24), None];
            let mut rows = Vec::new();
            for budget in budgets {
                let budget = budget.map(|b| b.max(report.peak)); // 12/16/24 clamped to feasibility
                // Best-of-seeds {0,1,2}; run_cell's internal double-run
                // covers per-seed determinism.
                let (row, best) = [0u64, 1, 2]
                    .into_iter()
                    .map(|seed| run_cell(&inst, budget, &GaParams { seed, ..GaParams::default() }))
                    .min_by_key(|(row, _)| row.ga_best)
                    .unwrap();
                // Gate 5 (win): strict beat over both no-intelligence
                // baselines at each tight budget.
                if tight.contains(&budget) {
                    assert!(row.ga_best < row.neutral,
                        "{} @ {budget:?}: search failed to beat neutral", inst.label);
                    assert!(row.ga_best < row.naive,
                        "{} @ {budget:?}: search failed to beat naive-fill", inst.label);
                    // Gate 4 on tight budgets only (parity of searched IR).
                    assert_parity(&inst, &table, &best, budget, &counts);
                }
                rows.push(row);
            }
            calibration.push((inst.label.clone(), rows));
        }
    }

    // Calibration readout (non-gating): FB2 band ~8-20%, E4c curve shape. Each
    // row is `phase0`-tagged; everything after the tag is byte-format-identical
    // to M2's readout so the two audit tables diff line-by-line.
    println!("\n== phase0 calibration ==");
    for (label, rows) in &calibration {
        for r in rows {
            let win = 100.0 * (r.neutral.traffic - r.ga_best.traffic) as f64
                / r.neutral.traffic.max(1) as f64;
            println!(
                "phase0 {label} @ {:?}: ceiling {} floor {} | neutral {} naive {} greedy {} ga {} | win {win:.1}%",
                r.budget, r.ceiling, r.floor, r.neutral.traffic, r.naive.traffic,
                r.greedy.traffic, r.ga_best.traffic
            );
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// M3 four-arm order machinery (Task 7, spec §6–§7).
//
// Added ALONGSIDE the Phase-0 harness above (which stays byte-identical): the
// four order arms `{Su, Derived(best), DerivedBiased(best), Searched}`, the
// derived-variant pre-sweep, the release-only `m3_sweep`, and a dilution
// spot-check. The invariants (bracket, peak≤budget, parity, elitism, floor,
// `clamps==0` under Su) are HARD gates; every arm-vs-arm comparison is a
// non-gating `println` readout tagged `m3`.
// ═══════════════════════════════════════════════════════════════════════════

/// One of the four full-GA order arms (spec §6). `Su` is the M1/M2 control
/// (no order channel); `Derived`/`DerivedBiased` apply the pre-sweep's winning
/// [`DerivedParams`]; `Searched` drops the derived key and orders purely by the
/// per-child bias gene. `DerivedBiased`/`Searched` search the bias vector
/// (`mutate_bias`); all three non-`Su` arms require the order channel.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Arm {
    Su,
    Derived,
    DerivedBiased,
    Searched,
}

impl Arm {
    const ALL: [Arm; 4] = [Arm::Su, Arm::Derived, Arm::DerivedBiased, Arm::Searched];

    /// Stable column index for the `m3` readout row (`su derived biased searched`).
    fn index(self) -> usize {
        match self {
            Arm::Su => 0,
            Arm::Derived => 1,
            Arm::DerivedBiased => 2,
            Arm::Searched => 3,
        }
    }

    /// The walker [`OrderPolicy`] this arm runs under, parameterized by the
    /// pre-sweep's winning `params` (ignored by `Su`/`Searched`).
    fn policy(self, params: DerivedParams) -> OrderPolicy {
        match self {
            Arm::Su => OrderPolicy::Su,
            Arm::Derived => OrderPolicy::Derived(params),
            Arm::DerivedBiased => OrderPolicy::DerivedBiased(params),
            Arm::Searched => OrderPolicy::Searched,
        }
    }

    /// Whether the GA perturbs `order_bias` for this arm (only the two
    /// bias-consuming arms).
    fn mutate_bias(self) -> bool {
        matches!(self, Arm::DerivedBiased | Arm::Searched)
    }

    /// Whether the arm needs an [`OrderCtx`] (every arm but `Su`).
    fn needs_order(self) -> bool {
        !matches!(self, Arm::Su)
    }
}

/// Builds the per-arm [`EvalCtx`]: counts always on (the dead-aware residency,
/// like the Phase-0 path), the arm's policy, and a FRESH [`OrderCtx`] for the
/// order arms (`None` under `Su`). A fresh `OrderCtx` per call is sound because
/// its genome-dependent `fills` map is rebuilt per genome inside the walk.
fn build_ctx<'a>(
    arm: Arm,
    params: DerivedParams,
    table: &'a SiteTable,
    counts: &'a UseCounts,
    n_exprs: usize,
) -> EvalCtx<'a> {
    let order = arm.needs_order().then(|| RefCell::new(OrderCtx::new(table, n_exprs)));
    EvalCtx { counts: Some(counts), policy: arm.policy(params), order }
}

/// One full walk of genome `g` under `ctx`, returning the whole [`WalkOutput`]
/// (program AND stats). Mirrors `search::score_ctx`'s `set_fills` gate exactly
/// — rebuild the fills map iff the policy carries a nonzero `fill_weight` —
/// then routes through [`flatten_with`], so the traffic/instrs it reports match
/// what the GA scored, while also exposing `peak`/`clamps`/`key_active` and the
/// program the parity gate replays.
fn walk_arm(
    view: &LayerView<'_>,
    table: &SiteTable,
    g: &Genome,
    budget: Option<u32>,
    ctx: &EvalCtx<'_>,
) -> WalkOutput {
    // Mirror `search::score_ctx`'s fill gate verbatim: only a nonzero
    // `fill_weight` (Derived/DerivedBiased) needs the genome-dependent fills
    // map; Su/Searched leave it untouched (Searched drops the fill term).
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
    flatten_with(view, &oracle, budget, ctx.policy, ctx.counts, borrowed.as_deref())
}

/// Runs one arm's GA (best-of `seeds_list`, seeds vector = neutral + naive-fill
/// + greedy, all zero-bias) and returns its best `(genome, score)` plus the
/// full stats of a re-walk of that genome. Asserts the two per-arm invariants
/// that hold for ANY cell: GA ties-or-beats its best seed (elitism), and the
/// re-walk reproduces the GA's recorded traffic/instrs.
#[allow(clippy::too_many_arguments)]
fn run_arm(
    view: &LayerView<'_>,
    table: &SiteTable,
    counts: &UseCounts,
    n_exprs: usize,
    n_roots: usize,
    arm: Arm,
    params: DerivedParams,
    budget: Option<u32>,
    base: &GaParams,
    seeds_list: &[u64],
    greedy_seed: &Genome,
) -> (Genome, Score, WalkStats) {
    let seed_genomes = vec![
        neutral_genome(table, n_roots),
        naive_fill_genome(table, n_roots),
        greedy_seed.clone(),
    ];
    // Best-of-seeds: the first seed (evaluation order) wins ties (strict `<`),
    // so the pick is reproducible.
    let mut best: Option<(Genome, Score)> = None;
    for &seed in seeds_list {
        let ctx = build_ctx(arm, params, table, counts, n_exprs);
        let gp = GaParams { seed, mutate_bias: arm.mutate_bias(), ..*base };
        let (g, s) = ga_ctx(view, table, n_roots, budget, &gp, seed_genomes.clone(), &ctx);
        if best.as_ref().map_or(true, |(_, bs)| s < *bs) {
            best = Some((g, s));
        }
    }
    let (g_best, s_best) = best.expect("run_arm: empty seeds_list");

    // Invariant: the GA ties-or-beats its best seed (elitism), scored under the
    // SAME arm ctx the GA used — apples-to-apples, not the Su `score`.
    let seed_ctx = build_ctx(arm, params, table, counts, n_exprs);
    let seed_best = seed_genomes
        .iter()
        .map(|g| score_ctx(view, table, g, budget, &seed_ctx))
        .min()
        .unwrap();
    assert!(
        s_best <= seed_best,
        "arm {arm:?} @ {budget:?}: GA {s_best:?} lost to its best seed {seed_best:?}"
    );

    // Re-walk the best genome under a fresh arm ctx for its full stats
    // (peak/clamps/key_active). `set_fills` is a pure function of genome+view,
    // so a fresh OrderCtx reproduces the GA's recorded traffic/instrs exactly.
    let stat_ctx = build_ctx(arm, params, table, counts, n_exprs);
    let stats = walk_arm(view, table, &g_best, budget, &stat_ctx).stats;
    assert_eq!(
        (stats.traffic, stats.instrs),
        (s_best.traffic, s_best.instrs),
        "arm {arm:?} @ {budget:?}: re-walk score drift"
    );
    (g_best, s_best, stats)
}

/// Gate 3 (per arm): the arm's best genome, re-flattened under the ARM's policy
/// (not a Su stand-in), still interprets bit-exact vs `eval_layer_root` (rows
/// 0/1/17, shared HashResolvers seed 7).
#[allow(clippy::too_many_arguments)]
fn assert_parity_arm(
    inst: &Instance,
    table: &SiteTable,
    counts: &UseCounts,
    n_exprs: usize,
    best: &Genome,
    budget: Option<u32>,
    arm: Arm,
    params: DerivedParams,
) {
    let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
    let ctx = build_ctx(arm, params, table, counts, n_exprs);
    let out = walk_arm(&view, table, best, budget, &ctx);
    let r = HashResolvers { seed: 7 }.bundle();
    for row in [0usize, 1, 17] {
        let got = interpret(&out.program, &inst.layer, row, &r);
        for (i, _) in inst.layer.roots.iter().enumerate() {
            let want = eval_layer_root(&inst.layer, RootId(i as u32), row, &r);
            assert_eq!(
                got[&RootId(i as u32)], want,
                "{} arm {arm:?} root {i} row {row}: searched-genome parity broke", inst.label
            );
        }
    }
}

/// Fast, non-ignored smoke: add_sub fwd tight × all four arms, tiny GA — each
/// arm passes its per-cell hard gates (bracket, `peak ≤ budget`, `clamps == 0`
/// under `Su`, parity).
#[test]
fn smoke_m3_four_arm() {
    let inst = fwd_instance("add_sub_lui_auipc_mop_layout_gkr.json");
    let view = LayerView::new(&inst.layer, &inst.cross, None);
    let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
    let report = size_layer(&view, &roots);
    let table = SiteTable::enumerate(&view);
    let counts = table.use_counts(inst.layer.exprs.len());
    let n_exprs = inst.layer.exprs.len();
    let n = inst.layer.roots.len();
    let budget = Some(report.peak + 2);
    let params = DerivedParams { fill_weight: 1, peak_first: false };
    let tiny = GaParams { pop: 8, max_evals: 120, elites: 2, descent_flips: 4, seed: 0, mutate_bias: false };

    let su_ctx = EvalCtx { counts: Some(&counts), ..EvalCtx::default() };
    let ceiling = score_ctx(&view, &table, &neutral_genome(&table, n), budget, &su_ctx).traffic;
    let g_greedy = greedy_ctx(&view, &table, n, budget, &su_ctx);

    for arm in Arm::ALL {
        let (g, s, st) =
            run_arm(&view, &table, &counts, n_exprs, n, arm, params, budget, &tiny, &[0], &g_greedy);
        assert!(
            s.traffic >= report.floor && s.traffic <= ceiling,
            "{} arm {arm:?}: bracket {s:?} not in [{}, {ceiling}]",
            inst.label,
            report.floor
        );
        if let Some(b) = budget {
            assert!(st.peak <= b, "{} arm {arm:?}: peak {} > budget {b}", inst.label, st.peak);
        }
        if arm == Arm::Su {
            assert_eq!(st.clamps, 0, "{} Su arm must never clamp", inst.label);
        }
        assert_parity_arm(&inst, &table, &counts, n_exprs, &g, budget, arm, params);
    }
}

/// Determinism per arm (dedicated non-ignored test): add_sub fwd tight × all
/// four arms, tiny GA — a double-run is byte-identical in genome AND score.
#[test]
fn m3_four_arm_determinism() {
    let inst = fwd_instance("add_sub_lui_auipc_mop_layout_gkr.json");
    let view = LayerView::new(&inst.layer, &inst.cross, None);
    let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
    let report = size_layer(&view, &roots);
    let table = SiteTable::enumerate(&view);
    let counts = table.use_counts(inst.layer.exprs.len());
    let n_exprs = inst.layer.exprs.len();
    let n = inst.layer.roots.len();
    let budget = Some(report.peak + 2);
    let params = DerivedParams { fill_weight: 1, peak_first: false };
    let tiny = GaParams { pop: 8, max_evals: 120, elites: 2, descent_flips: 4, seed: 0, mutate_bias: false };
    let su_ctx = EvalCtx { counts: Some(&counts), ..EvalCtx::default() };
    let g_greedy = greedy_ctx(&view, &table, n, budget, &su_ctx);

    for arm in Arm::ALL {
        let (g1, s1, _) =
            run_arm(&view, &table, &counts, n_exprs, n, arm, params, budget, &tiny, &[0], &g_greedy);
        let (g2, s2, _) =
            run_arm(&view, &table, &counts, n_exprs, n, arm, params, budget, &tiny, &[0], &g_greedy);
        assert_eq!(g1, g2, "{} arm {arm:?}: nondeterministic genome", inst.label);
        assert_eq!(s1, s2, "{} arm {arm:?}: nondeterministic score", inst.label);
    }
}

/// The six derived variants in a fixed enum order (`fill_weight ∈ {1,0,−1}` ×
/// `peak_first ∈ {false,true}`). The pre-sweep scores every one and the index
/// here is the final tie-break, so this order is spec-binding.
const VARIANTS: [DerivedParams; 6] = [
    DerivedParams { fill_weight: 1, peak_first: false },
    DerivedParams { fill_weight: 1, peak_first: true },
    DerivedParams { fill_weight: 0, peak_first: false },
    DerivedParams { fill_weight: 0, peak_first: true },
    DerivedParams { fill_weight: -1, peak_first: false },
    DerivedParams { fill_weight: -1, peak_first: true },
];

/// The pass-wide `best` variant: majority vote across a pass's per-instance
/// pre-sweep winners. Ties break by lowest `|fill_weight|`, then key-first
/// (`peak_first == false`), then the [`VARIANTS`] enum order — fully
/// deterministic.
fn majority_derived(winners: &[DerivedParams]) -> DerivedParams {
    VARIANTS
        .iter()
        .copied()
        .enumerate()
        .min_by_key(|&(i, v)| {
            let votes = winners.iter().filter(|&&w| w == v).count();
            (std::cmp::Reverse(votes), v.fill_weight.unsigned_abs(), v.peak_first as u8, i)
        })
        .expect("VARIANTS is non-empty")
        .1
}

/// Derived-variant pre-sweep for ONE instance (spec §6): score the six variants
/// with EXISTING genomes only — `greedy_ctx`'s genome and a short Su GA
/// (`pop 16 / evals 300 / seed 0`), produced under `Su` at each of the two
/// tight budgets — under `Derived(variant)`, and pick the variant with the best
/// SUMMED lexicographic score (ties: fewer summed clamps, then [`VARIANTS`]
/// order). Logs every variant's numbers (audit source, tagged `m3 pre-sweep`).
fn pre_sweep(inst: &Instance, pass: &str) -> DerivedParams {
    let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
    let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
    let report = size_layer(&view, &roots);
    let table = SiteTable::enumerate(&view);
    let counts = table.use_counts(inst.layer.exprs.len());
    let n_exprs = inst.layer.exprs.len();
    let n = inst.layer.roots.len();
    let tight = [Some(report.peak), Some(report.peak + 2)];

    // Existing genomes, per tight budget: greedy + short Su GA winner. Produced
    // under Su (the order they were optimized for — the pre-sweep's stated bias).
    let su_ctx = EvalCtx { counts: Some(&counts), ..EvalCtx::default() };
    let short_ga = GaParams { pop: 16, max_evals: 300, seed: 0, ..GaParams::default() };
    let mut genomes: Vec<(Option<u32>, Vec<Genome>)> = Vec::with_capacity(tight.len());
    for &b in &tight {
        let g_greedy = greedy_ctx(&view, &table, n, b, &su_ctx);
        let seeds = vec![neutral_genome(&table, n), naive_fill_genome(&table, n), g_greedy.clone()];
        let (g_ga, _) = ga_ctx(&view, &table, n, b, &short_ga, seeds, &su_ctx);
        genomes.push((b, vec![g_greedy, g_ga]));
    }

    // Score every variant: sum over (budget × genome) of its Derived walk.
    let mut rows: Vec<(Score, u64)> = Vec::with_capacity(VARIANTS.len());
    for (i, &var) in VARIANTS.iter().enumerate() {
        let ctx = EvalCtx {
            counts: Some(&counts),
            policy: OrderPolicy::Derived(var),
            order: Some(RefCell::new(OrderCtx::new(&table, n_exprs))),
        };
        let (mut traffic, mut instrs, mut clamps) = (0u64, 0u64, 0u64);
        for (b, gs) in &genomes {
            for g in gs {
                let st = walk_arm(&view, &table, g, *b, &ctx).stats;
                traffic += st.traffic;
                instrs += st.instrs;
                clamps += st.clamps;
            }
        }
        rows.push((Score { traffic, instrs }, clamps));
        println!(
            "m3 pre-sweep {pass} {} var{i} fw {} pf {} | sum_traffic {} sum_instrs {} sum_clamps {}",
            inst.label, var.fill_weight, var.peak_first, traffic, instrs, clamps
        );
    }

    let best_idx = (0..VARIANTS.len())
        .min_by_key(|&i| (rows[i].0, rows[i].1, i))
        .expect("VARIANTS is non-empty");
    let best = VARIANTS[best_idx];
    println!(
        "m3 pre-sweep {pass} {} -> best fw {} pf {}",
        inst.label, best.fill_weight, best.peak_first
    );
    best
}

/// The pass-wide winner: pre-sweep every instance in the pass, then majority.
fn pass_best(insts: &[Instance], pass: &str) -> DerivedParams {
    let winners: Vec<DerivedParams> = insts.iter().map(|inst| pre_sweep(inst, pass)).collect();
    let best = majority_derived(&winners);
    println!("m3 pre-sweep {pass} pass-best fw {} pf {}", best.fill_weight, best.peak_first);
    best
}

/// The M3 exit sweep (spec §6–§7). Release-only. Per pass, the pre-sweep picks
/// the pass's `Derived*` params; then per instance × budget `{peak, peak+2, 24,
/// None}` × arm `{Su, Derived(best), DerivedBiased(best), Searched}` a full GA
/// (best-of seeds {0,1,2}) runs under the HARD per-cell gates (bracket,
/// `peak ≤ budget`, `clamps == 0` under Su, parity at tight budgets, floor at
/// None, GA elitism). Every arm-vs-arm comparison is a NON-GATING `m3` readout.
#[test]
#[ignore = "release-only four-arm order sweep"]
fn m3_sweep() {
    let fwd_insts: Vec<Instance> = HEAVY_QUARTET.iter().map(|n| fwd_instance(n)).collect();
    let bwd_insts: Vec<Instance> = HEAVY_QUARTET.iter().map(|n| bwd_instance(n)).collect();

    println!("\n== m3 pre-sweep ==");
    let fwd_best = pass_best(&fwd_insts, "fwd");
    let bwd_best = pass_best(&bwd_insts, "bwd");

    println!("\n== m3 four-arm sweep ==");
    for (insts, best) in [(&fwd_insts, fwd_best), (&bwd_insts, bwd_best)] {
        for inst in insts {
            let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
            let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
            let report = size_layer(&view, &roots);
            let table = SiteTable::enumerate(&view);
            let counts = table.use_counts(inst.layer.exprs.len());
            let n_exprs = inst.layer.exprs.len();
            let n = inst.layer.roots.len();
            assert!((report.floor as u128) < report.ceiling, "no reuse to search");

            // Ceiling is the all-recompute neutral traffic (budget-independent —
            // neutral caches nothing, so order never changes it).
            let su_ctx = EvalCtx { counts: Some(&counts), ..EvalCtx::default() };
            let ceiling =
                score_ctx(&view, &table, &neutral_genome(&table, n), Some(report.peak), &su_ctx).traffic;

            let tight = [Some(report.peak), Some(report.peak + 2)];
            // {peak, peak+2, 24, None}; 24 clamped to feasibility (mirror M2).
            let budgets = [Some(report.peak), Some(report.peak + 2), Some(24), None];
            for budget in budgets {
                let budget = budget.map(|b| b.max(report.peak));
                // Greedy seed once per (instance, budget), under Su (zero-bias),
                // shared across arms.
                let g_greedy = greedy_ctx(&view, &table, n, budget, &su_ctx);

                let mut traffic = [0u64; 4];
                let mut derived_st = WalkStats::default();
                for arm in Arm::ALL {
                    let (g, s, st) = run_arm(
                        &view, &table, &counts, n_exprs, n, arm, best, budget, &GaParams::default(),
                        &[0, 1, 2], &g_greedy,
                    );
                    // Hard gates (invariants), per arm.
                    assert!(
                        s.traffic >= report.floor && s.traffic <= ceiling,
                        "m3 {} @ {budget:?} arm {arm:?}: bracket {s:?} not in [{}, {ceiling}]",
                        inst.label, report.floor
                    );
                    if let Some(b) = budget {
                        assert!(
                            st.peak <= b,
                            "m3 {} @ {budget:?} arm {arm:?}: peak {} > budget {b}",
                            inst.label, st.peak
                        );
                    }
                    if arm == Arm::Su {
                        assert_eq!(st.clamps, 0, "m3 {} @ {budget:?}: Su arm must never clamp", inst.label);
                    }
                    if budget.is_none() {
                        assert_eq!(
                            s.traffic, report.floor,
                            "m3 {} arm {arm:?}: unbounded best must reach floor", inst.label
                        );
                    }
                    if tight.contains(&budget) {
                        assert_parity_arm(inst, &table, &counts, n_exprs, &g, budget, arm, best);
                    }
                    traffic[arm.index()] = s.traffic;
                    if arm == Arm::Derived {
                        derived_st = st;
                    }
                }
                // Non-gating readout (clamps/key_active from the Derived arm — the
                // canonical derived order the pre-sweep selected).
                println!(
                    "m3 {} @ {budget:?}: ceiling {ceiling} floor {} | su {} derived {} biased {} searched {} | clamps {} key_active {}",
                    inst.label, report.floor,
                    traffic[0], traffic[1], traffic[2], traffic[3],
                    derived_st.clamps, derived_st.key_active
                );
            }
        }
    }
}

/// Dilution spot-check (spec §7): one starved bwd cell (bigint bwd Ext L0 @
/// peak), the `Searched` arm at 4× evals, single seed. `println` only — the
/// derived rule reacts to live cache state that static bias genes cannot
/// express, so `Searched`'s larger space at fixed budget can lose from search
/// dilution alone; this cell calibrates that effect. No gates beyond `run_arm`'s
/// intrinsic invariants (elitism, re-walk consistency).
#[test]
#[ignore = "release-only dilution spot-check"]
fn m3_dilution_spot_check() {
    let inst = bwd_instance("bigint_with_extended_control_layout_gkr.json");
    let view = LayerView::new(&inst.layer, &inst.cross, inst.overrides.as_ref());
    let roots: Vec<ExprId> = inst.layer.roots.iter().map(|r| r.expr).collect();
    let report = size_layer(&view, &roots);
    let table = SiteTable::enumerate(&view);
    let counts = table.use_counts(inst.layer.exprs.len());
    let n_exprs = inst.layer.exprs.len();
    let n = inst.layer.roots.len();
    let budget = Some(report.peak);
    // Searched drops the fill term, so the params only carry a peak-first
    // tie-break here; key-first matches the pass default.
    let params = DerivedParams { fill_weight: 0, peak_first: false };
    let su_ctx = EvalCtx { counts: Some(&counts), ..EvalCtx::default() };
    let g_greedy = greedy_ctx(&view, &table, n, budget, &su_ctx);

    // 4× the default eval budget, single seed.
    let quad = GaParams { max_evals: 4 * GaParams::default().max_evals, ..GaParams::default() };
    let (_, s, st) =
        run_arm(&view, &table, &counts, n_exprs, n, Arm::Searched, params, budget, &quad, &[0], &g_greedy);
    println!(
        "m3 dilution {} @ {budget:?}: searched traffic {} instrs {} peak {} clamps {} key_active {} | floor {} ceiling {}",
        inst.label, s.traffic, s.instrs, st.peak, st.clamps, st.key_active, report.floor, report.ceiling
    );
}
