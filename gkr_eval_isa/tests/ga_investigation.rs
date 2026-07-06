//! GA-investigation harness (diagnostic, NOT a production feature).
//!
//! Answers "does the memetic GA improve genome quality via its operators, or does
//! it converge prematurely?" (H1 corpus-near-optimal vs H2 weak-optimizer) — see
//! `.agents/specs/2026-07-06-gkr-ga-investigation-design.md`. It exercises the
//! Phase-A telemetry/ablation instrumentation added to
//! `schedule_search::search::optimize_instrumented`.
//!
//! Two parts:
//!   * `optimize_instrumented_default_matches_production` — a FAST, non-ignored
//!     determinism gate (runs under a normal `cargo test`): the default-ablation
//!     + telemetry-on run must be byte-identical to `optimize_from_population`.
//!   * `ga_battery` — the `#[ignore]`d, env-gated experiment battery (ablations,
//!     incumbent-vs-scratch, seed variance, budget sweep, config sensitivity),
//!     writing per-run telemetry JSONL + a summary CSV under `target/ga_investigation/`.
//!
//! Both testbeds use LAYER 0 at the production cache budget `BUDGET = 16` (b16).
//! The *eval* budgets (`cfg.evals`) are the sweep axis, driven by env.
//!
//! Env knobs (battery only):
//!   * `GKR_GA_INVESTIGATE=1`     — required, else the battery no-ops.
//!   * `GKR_GA_INV_TESTBED`       — `add_sub` (default) | `bigint` | `blake2_g` |
//!                                  `blake2_ext` | `keccak`.
//!   * `GKR_GA_INV_BUDGETS`       — comma list of eval budgets, default `20000,80000`.
//!   * `GKR_GA_INV_SEEDS`         — seed count for the variance experiment, default `8`.
//!   * `GKR_GA_INV_LOCAL_ELITE`   — comma list of local_elite values (exp6), default `0,1,2,4,8`.

mod common;

use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use cs::gkr_compiler::dag_ir::{lower_dag, validate, DagCircuit, FieldKind, ReadPlace};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;

use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, load_committed_schedule};
use gkr_eval_isa::schedule_search::scorer::{genome_from_schedule, LayerCtx};
use gkr_eval_isa::schedule_search::search::{
    optimize_from_population, optimize_instrumented, seeded_population, CrossoverKind, GaAblation,
    GaRun, GenStat, SearchConfig,
};

use common::{compiled_circuit_dir, load_fixture, schedule_stem};

/// Production cache budget (`*_schedule_b16_gkr.json`). Fixed for every run — the
/// investigation must match production conditions.
const BUDGET: usize = 16;

// ── Testbed loading ───────────────────────────────────────────────────────────

fn testbed_fixture(name: &str) -> &'static str {
    match name {
        "add_sub" => "add_sub_lui_auipc_mop_layout_gkr.json",
        "bigint" => "bigint_with_extended_control_layout_gkr.json",
        "blake2_g" => "blake2_g_function_layout_gkr.json",
        "blake2_ext" => "blake2_with_extended_control_layout_gkr.json",
        "keccak" => "keccak_special5_layout_gkr.json",
        other => panic!(
            "unknown GKR_GA_INV_TESTBED {other:?} \
             (expected add_sub|bigint|blake2_g|blake2_ext|keccak)"
        ),
    }
}

type Loaded = (DagCircuit, GKRCircuitArtifact<BabyBearField>, HashMap<ReadPlace, FieldKind>);

fn load_testbed(name: &str) -> Loaded {
    let fixture = testbed_fixture(name);
    let artifact = load_fixture(fixture);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{fixture}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{fixture}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    (dag, artifact, cross)
}

/// Layer-0 committed schedule for `testbed` (the Phase-1 incumbent).
fn committed_layer0(testbed: &str) -> cs::gkr_compiler::dag_ir::LayerSchedule {
    let stem = schedule_stem(testbed_fixture(testbed));
    let path = compiled_circuit_dir().join(format!("{stem}_schedule_b16_gkr.json"));
    let sched = load_committed_schedule(&path)
        .unwrap_or_else(|e| panic!("load committed schedule {path:?}: {e:?}"));
    assert!(!sched.layers.is_empty(), "committed schedule has no layers");
    sched.layers[0].clone()
}

// ── Determinism gate (fast, non-ignored) ─────────────────────────────────────

/// Phase-A correctness gate: the instrumented driver at its DEFAULT ablation with
/// telemetry ON must reproduce production (`optimize_from_population`) exactly —
/// same `best_genome` and `best_score`. This proves telemetry/ablation-default is
/// behavior-inert (no perturbation of the RNG stream or eval budget). Uses a tiny
/// cfg (pop=16, evals=600) on add_sub L0 so it stays fast under normal `cargo test`.
#[test]
fn optimize_instrumented_default_matches_production() {
    let (dag, artifact, cross) = load_testbed("add_sub");
    let ctx = LayerCtx::new(&dag.layers[0], &artifact.layers[0], &artifact, &cross, BUDGET);
    let cfg = SearchConfig { pop: 16, evals: 600, seed: 0, ..SearchConfig::default() };

    let prod = optimize_from_population(&ctx, seeded_population(&ctx, cfg.pop, cfg.seed), &cfg);
    let instr = optimize_instrumented(
        &ctx,
        seeded_population(&ctx, cfg.pop, cfg.seed),
        &cfg,
        GaAblation::default(),
        true,
    );

    assert_eq!(
        prod.best_score, instr.result.best_score,
        "default ablation + telemetry must be behavior-inert (best_score drift)"
    );
    assert_eq!(
        prod.best_genome, instr.result.best_genome,
        "default ablation + telemetry must be behavior-inert (best_genome drift)"
    );
    assert_eq!(prod.evals, instr.result.evals, "eval accounting must be unchanged by telemetry");
    assert!(instr.telemetry.is_some(), "collect=true must produce telemetry");
    let tel = instr.telemetry.unwrap();
    assert_eq!(
        tel.final_best,
        if prod.best_score.infeasible { usize::MAX } else { prod.best_score.dram_traffic },
        "telemetry.final_best must equal the production result"
    );
}

// ── Summary row ───────────────────────────────────────────────────────────────

#[derive(Clone)]
struct SummaryRow {
    experiment: String,
    tag: String,
    final_best: usize,
    floor: usize,
    gap_to_floor: i64,
    evals: usize,
    generations: usize,
    winner_origin: String,
    pct_xover_improved: f64,
    pct_mut_improved: f64,
    pct_ld_improved: f64,
    convergence_gen: usize,
    div_order_start: f64,
    div_order_end: f64,
    div_prio_start: f64,
    div_prio_end: f64,
    local_elite: usize,
    crossover_kind: String,
    wall_secs: f64,
}

impl SummaryRow {
    fn csv_header() -> &'static str {
        "experiment,tag,final_best,floor,gap_to_floor,evals,generations,winner_origin,\
         pct_xover_improved,pct_mut_improved,pct_ld_improved,convergence_gen,\
         div_order_start,div_order_end,div_prio_start,div_prio_end,local_elite,crossover_kind,wall_secs"
    }

    fn csv_line(&self) -> String {
        format!(
            "{},{},{},{},{},{},{},{},{:.2},{:.2},{:.2},{},{:.4},{:.4},{:.4},{:.4},{},{},{:.2}",
            self.experiment,
            self.tag,
            self.final_best,
            self.floor,
            self.gap_to_floor,
            self.evals,
            self.generations,
            self.winner_origin,
            self.pct_xover_improved,
            self.pct_mut_improved,
            self.pct_ld_improved,
            self.convergence_gen,
            self.div_order_start,
            self.div_order_end,
            self.div_prio_start,
            self.div_prio_end,
            self.local_elite,
            self.crossover_kind,
            self.wall_secs,
        )
    }
}

/// Display string for a [`CrossoverKind`] (matches the `GKR_SCHEDULE_XOVER_KIND`
/// env spelling).
fn crossover_kind_str(k: CrossoverKind) -> &'static str {
    match k {
        CrossoverKind::Blx => "blx",
        CrossoverKind::Order => "order",
    }
}

/// Aggregate one collected run into a summary row. Operator productivity is
/// `improved / total_offspring` across all generations (a per-offspring
/// productivity rate — a consistent denominator for the three operators).
fn summarize(experiment: &str, tag: &str, run: &GaRun, cfg: &SearchConfig, wall: Duration) -> SummaryRow {
    let t = run.telemetry.as_ref().expect("collect=true run must carry telemetry");
    let tot_off: usize = t.generations.iter().map(|g| g.offspring).sum();
    let tot_x: usize = t.generations.iter().map(|g| g.crossover_improved).sum();
    let tot_m: usize = t.generations.iter().map(|g| g.mutation_improved).sum();
    let tot_l: usize = t.generations.iter().map(|g| g.local_descent_improved).sum();
    let denom = tot_off.max(1) as f64;
    // Convergence generation = last generation where the global best improved.
    let conv = t.generations.iter().filter(|g| g.new_best).map(|g| g.generation).max().unwrap_or(0);
    let first = t.generations.first();
    let last = t.generations.last();
    SummaryRow {
        experiment: experiment.to_string(),
        tag: tag.to_string(),
        final_best: t.final_best,
        floor: t.floor,
        gap_to_floor: t.final_best as i64 - t.floor as i64,
        evals: t.total_evals,
        generations: last.map(|g| g.generation).unwrap_or(0),
        winner_origin: t.winner_origin.clone(),
        pct_xover_improved: 100.0 * tot_x as f64 / denom,
        pct_mut_improved: 100.0 * tot_m as f64 / denom,
        pct_ld_improved: 100.0 * tot_l as f64 / denom,
        convergence_gen: conv,
        div_order_start: first.map(|g| g.diversity_order).unwrap_or(0.0),
        div_order_end: last.map(|g| g.diversity_order).unwrap_or(0.0),
        div_prio_start: first.map(|g| g.diversity_prio).unwrap_or(0.0),
        div_prio_end: last.map(|g| g.diversity_prio).unwrap_or(0.0),
        local_elite: cfg.local_elite,
        crossover_kind: crossover_kind_str(cfg.crossover_kind).to_string(),
        wall_secs: wall.as_secs_f64(),
    }
}

// ── JSONL writer ──────────────────────────────────────────────────────────────

/// One JSONL record per generation: run context flattened over the [`GenStat`].
#[derive(serde::Serialize)]
struct GenRecord<'a> {
    testbed: &'a str,
    experiment: &'a str,
    tag: &'a str,
    label: &'a str,
    floor: usize,
    final_best: usize,
    winner_origin: &'a str,
    #[serde(flatten)]
    stat: &'a GenStat,
}

fn out_dir() -> PathBuf {
    let d = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../target/ga_investigation");
    std::fs::create_dir_all(&d).unwrap_or_else(|e| panic!("create {d:?}: {e}"));
    d
}

fn write_jsonl(dir: &std::path::Path, testbed: &str, experiment: &str, tag: &str, run: &GaRun) {
    let t = run.telemetry.as_ref().expect("collect=true run must carry telemetry");
    let path = dir.join(format!("{testbed}_{experiment}_{tag}.jsonl"));
    let mut f = std::fs::File::create(&path).unwrap_or_else(|e| panic!("create {path:?}: {e}"));
    for stat in &t.generations {
        let rec = GenRecord {
            testbed,
            experiment,
            tag,
            label: &t.label,
            floor: t.floor,
            final_best: t.final_best,
            winner_origin: &t.winner_origin,
            stat,
        };
        let line = serde_json::to_string(&rec).expect("serialize GenRecord");
        writeln!(f, "{line}").unwrap_or_else(|e| panic!("write {path:?}: {e}"));
    }
}

// ── One collected run (drives telemetry + JSONL + summary) ───────────────────

struct Ctx<'a> {
    testbed: &'a str,
    dir: &'a std::path::Path,
    rows: Vec<SummaryRow>,
}

impl<'a> Ctx<'a> {
    /// Run one configuration with telemetry ON, tag it, dump JSONL, print a line,
    /// record a summary row, and return the achieved `final_best`.
    fn run(
        &mut self,
        layer_ctx: &LayerCtx,
        cfg: &SearchConfig,
        ablation: GaAblation,
        seeds: Vec<gkr_eval_isa::schedule_search::genome::Genome>,
        experiment: &str,
        tag: &str,
    ) -> usize {
        let start = Instant::now();
        let mut run = optimize_instrumented(layer_ctx, seeds, cfg, ablation, true);
        let wall = start.elapsed();
        if let Some(t) = run.telemetry.as_mut() {
            t.label = format!("{experiment}/{tag}");
        }
        write_jsonl(self.dir, self.testbed, experiment, tag, &run);
        let row = summarize(experiment, tag, &run, cfg, wall);
        println!(
            "  [{exp}/{tag}] best={best} floor={floor} gap={gap:+} evals={evals} gens={gens} \
             origin={origin} xover%={x:.1} mut%={m:.1} ld%={l:.1} conv_gen={conv} \
             div_order {d0:.3}->{d1:.3} ({wall:.1}s)",
            exp = row.experiment,
            tag = row.tag,
            best = row.final_best,
            floor = row.floor,
            gap = row.gap_to_floor,
            evals = row.evals,
            gens = row.generations,
            origin = row.winner_origin,
            x = row.pct_xover_improved,
            m = row.pct_mut_improved,
            l = row.pct_ld_improved,
            conv = row.convergence_gen,
            d0 = row.div_order_start,
            d1 = row.div_order_end,
            wall = row.wall_secs,
        );
        let best = row.final_best;
        self.rows.push(row);
        best
    }
}

// ── The battery ───────────────────────────────────────────────────────────────

fn env_testbed() -> String {
    std::env::var("GKR_GA_INV_TESTBED").unwrap_or_else(|_| "add_sub".to_string())
}

fn env_budgets() -> Vec<usize> {
    let raw = std::env::var("GKR_GA_INV_BUDGETS").unwrap_or_else(|_| "20000,80000".to_string());
    let budgets: Vec<usize> = raw
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .map(|s| s.parse::<usize>().unwrap_or_else(|_| panic!("GKR_GA_INV_BUDGETS: bad usize {s:?}")))
        .collect();
    assert!(!budgets.is_empty(), "GKR_GA_INV_BUDGETS must list at least one budget");
    budgets
}

fn env_seed_count() -> usize {
    std::env::var("GKR_GA_INV_SEEDS")
        .ok()
        .map(|s| s.parse::<usize>().unwrap_or_else(|_| panic!("GKR_GA_INV_SEEDS: bad usize {s:?}")))
        .unwrap_or(8)
        .max(1)
}

fn env_local_elites() -> Vec<usize> {
    let raw = std::env::var("GKR_GA_INV_LOCAL_ELITE").unwrap_or_else(|_| "0,1,2,4,8".to_string());
    let vals: Vec<usize> = raw
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .map(|s| s.parse::<usize>().unwrap_or_else(|_| panic!("GKR_GA_INV_LOCAL_ELITE: bad usize {s:?}")))
        .collect();
    assert!(!vals.is_empty(), "GKR_GA_INV_LOCAL_ELITE must list at least one value");
    vals
}

/// Base crossover kind for the whole battery (default blx). Lets a sweep test
/// combined winners like `local_elite=0 + order-crossover`.
fn env_base_xover() -> CrossoverKind {
    match std::env::var("GKR_GA_INV_BASE_XOVER").as_deref() {
        Ok("order") => CrossoverKind::Order,
        Ok("blx") | Err(_) => CrossoverKind::Blx,
        Ok(other) => panic!("GKR_GA_INV_BASE_XOVER must be blx|order, got {other:?}"),
    }
}

/// Base `local_elite` for the whole battery (default = `SearchConfig::default`).
/// Lets a sweep pin the winner config (e.g. le0) across exp3/4/5.
fn env_base_local_elite() -> usize {
    std::env::var("GKR_GA_INV_BASE_LOCAL_ELITE")
        .ok()
        .map(|s| s.parse::<usize>().unwrap_or_else(|_| panic!("GKR_GA_INV_BASE_LOCAL_ELITE: bad usize {s:?}")))
        .unwrap_or(SearchConfig::default().local_elite)
}

/// The full experiment battery. `#[ignore]`d + gated on `GKR_GA_INVESTIGATE=1`
/// (so it never runs in a normal `cargo test`/CI). Drive it with
/// `GKR_GA_INVESTIGATE=1 cargo test --test ga_investigation -- --ignored --nocapture`.
#[test]
#[ignore = "diagnostic battery: set GKR_GA_INVESTIGATE=1 and run with --ignored --nocapture"]
fn ga_battery() {
    if std::env::var("GKR_GA_INVESTIGATE").is_err() {
        eprintln!("skipping GA battery (set GKR_GA_INVESTIGATE=1)");
        return;
    }
    let testbed = env_testbed();
    let budgets = env_budgets();
    let seed_count = env_seed_count();
    let first_budget = budgets[0];

    let (dag, artifact, cross) = load_testbed(&testbed);
    let layer = &dag.layers[0];
    let ctx = LayerCtx::new(layer, &artifact.layers[0], &artifact, &cross, BUDGET);
    let base = SearchConfig {
        evals: first_budget,
        seed: 0,
        crossover_kind: env_base_xover(),
        local_elite: env_base_local_elite(),
        ..SearchConfig::default()
    };

    println!(
        "\n=== GA investigation: testbed={testbed} L0 (budget={BUDGET}) units={units} sites={sites} floor={floor} ===",
        units = ctx.n_order_keys(),
        sites = ctx.n_sites(),
        floor = ctx.floor,
    );
    println!("budgets={budgets:?} seeds={seed_count} first_budget={first_budget}");

    let dir = out_dir();
    let mut cx = Ctx { testbed: &testbed, dir: &dir, rows: Vec::new() };

    // ── Experiment 1: operator ablations (first budget) ──────────────────────
    println!("\n-- exp1: operator ablations (evals={first_budget}) --");
    let ablations: &[(&str, GaAblation)] = &[
        ("full", GaAblation::default()),
        ("no_crossover", GaAblation { crossover: false, ..GaAblation::default() }),
        ("no_mutation", GaAblation { mutation: false, ..GaAblation::default() }),
        ("no_local_descent", GaAblation { local_descent: false, ..GaAblation::default() }),
        (
            "random_search",
            GaAblation { crossover: false, mutation: false, local_descent: false, random_search: true },
        ),
        (
            "ld_only",
            GaAblation { crossover: false, mutation: false, local_descent: true, random_search: true },
        ),
    ];
    for (tag, ab) in ablations {
        let seeds = seeded_population(&ctx, base.pop, base.seed);
        cx.run(&ctx, &base, *ab, seeds, "exp1_ablation", tag);
    }

    // ── Experiment 2: incumbent-seeded vs from-scratch (full GA, first budget) ─
    println!("\n-- exp2: incumbent-seeded vs from-scratch (evals={first_budget}) --");
    let committed = committed_layer0(&testbed);
    let committed_traffic = committed.predicted_traffic;
    let scratch_best = {
        let seeds = seeded_population(&ctx, base.pop, base.seed);
        cx.run(&ctx, &base, GaAblation::default(), seeds, "exp2_incumbent", "from_scratch")
    };
    let seeded_best = {
        let mut seeds = seeded_population(&ctx, base.pop, base.seed);
        seeds.insert(0, genome_from_schedule(&committed, &ctx));
        cx.run(&ctx, &base, GaAblation::default(), seeds, "exp2_incumbent", "incumbent_seeded")
    };
    println!(
        "  committed(b16 L0)={committed_traffic}  from_scratch={scratch_best}  incumbent_seeded={seeded_best}  \
         incumbent_beats_committed={}  incumbent_beats_scratch={}",
        seeded_best < committed_traffic,
        seeded_best < scratch_best,
    );

    // ── Experiment 3: seed variance (full GA, first budget) ──────────────────
    println!("\n-- exp3: seed variance (N={seed_count}, evals={first_budget}) --");
    let mut finals: Vec<usize> = Vec::with_capacity(seed_count);
    for s in 0..seed_count as u64 {
        let cfg = SearchConfig { seed: s, ..base };
        let seeds = seeded_population(&ctx, cfg.pop, cfg.seed);
        let best = cx.run(&ctx, &cfg, GaAblation::default(), seeds, "exp3_variance", &format!("seed{s}"));
        finals.push(best);
    }
    let feasible: Vec<usize> = finals.iter().copied().filter(|&v| v != usize::MAX).collect();
    if feasible.is_empty() {
        println!("  variance: ALL runs infeasible");
    } else {
        let n = feasible.len() as f64;
        let min = *feasible.iter().min().unwrap();
        let max = *feasible.iter().max().unwrap();
        let mean = feasible.iter().sum::<usize>() as f64 / n;
        let var = feasible.iter().map(|&v| (v as f64 - mean).powi(2)).sum::<f64>() / n;
        println!(
            "  variance: min={min} mean={mean:.2} max={max} stddev={:.3} (n_feasible={}/{})",
            var.sqrt(),
            feasible.len(),
            finals.len()
        );
    }

    // ── Experiment 4: budget sweep (full GA, seed 0) ─────────────────────────
    println!("\n-- exp4: budget sweep {budgets:?} (seed 0) --");
    for &b in &budgets {
        let cfg = SearchConfig { evals: b, seed: 0, ..base };
        let seeds = seeded_population(&ctx, cfg.pop, cfg.seed);
        cx.run(&ctx, &cfg, GaAblation::default(), seeds, "exp4_budget", &format!("evals{b}"));
    }

    // ── Experiment 5: config sensitivity (one-factor-at-a-time, first budget) ─
    println!("\n-- exp5: config sensitivity (evals={first_budget}) --");
    for sigma in [0.05f64, 0.15, 0.5] {
        let cfg = SearchConfig { mutation_sigma: sigma, ..base };
        let seeds = seeded_population(&ctx, cfg.pop, cfg.seed);
        cx.run(&ctx, &cfg, GaAblation::default(), seeds, "exp5_config", &format!("sigma{sigma}"));
    }
    for pop in [32usize, 64, 256] {
        let cfg = SearchConfig { pop, ..base };
        let seeds = seeded_population(&ctx, cfg.pop, cfg.seed);
        cx.run(&ctx, &cfg, GaAblation::default(), seeds, "exp5_config", &format!("pop{pop}"));
    }
    for tourn in [2usize, 3, 5] {
        let cfg = SearchConfig { tournament: tourn, ..base };
        let seeds = seeded_population(&ctx, cfg.pop, cfg.seed);
        cx.run(&ctx, &cfg, GaAblation::default(), seeds, "exp5_config", &format!("tourn{tourn}"));
    }

    // ── Experiment 6: local_elite sweep (full GA, first budget) ──────────────
    let local_elites = env_local_elites();
    println!("\n-- exp6: local_elite sweep {local_elites:?} (evals={first_budget}) --");
    for &le in &local_elites {
        let cfg = SearchConfig { local_elite: le, ..base };
        let seeds = seeded_population(&ctx, cfg.pop, cfg.seed);
        cx.run(&ctx, &cfg, GaAblation::default(), seeds, "exp6_local_elite", &format!("le{le}"));
    }

    // ── Experiment 7: crossover-kind sweep (full GA, first budget) ───────────
    println!("\n-- exp7: crossover kind (evals={first_budget}) --");
    {
        // none: crossover operator disabled entirely (BLX cfg is inert here).
        let seeds = seeded_population(&ctx, base.pop, base.seed);
        cx.run(
            &ctx,
            &base,
            GaAblation { crossover: false, ..GaAblation::default() },
            seeds,
            "exp7_xover",
            "none",
        );
    }
    {
        // blx: per-gene BLX-alpha on both gene vectors (production operator).
        let cfg = SearchConfig { crossover_kind: CrossoverKind::Blx, ..base };
        let seeds = seeded_population(&ctx, cfg.pop, cfg.seed);
        cx.run(&ctx, &cfg, GaAblation::default(), seeds, "exp7_xover", "blx");
    }
    {
        // order: permutation-preserving OX on the unit-order genes.
        let cfg = SearchConfig { crossover_kind: CrossoverKind::Order, ..base };
        let seeds = seeded_population(&ctx, cfg.pop, cfg.seed);
        cx.run(&ctx, &cfg, GaAblation::default(), seeds, "exp7_xover", "order");
    }

    // ── Summary table (CSV + pretty stdout) ──────────────────────────────────
    let csv_path = dir.join(format!("{testbed}_summary.csv"));
    let mut f = std::fs::File::create(&csv_path).unwrap_or_else(|e| panic!("create {csv_path:?}: {e}"));
    writeln!(f, "{}", SummaryRow::csv_header()).unwrap();
    for r in &cx.rows {
        writeln!(f, "{}", r.csv_line()).unwrap();
    }

    println!("\n=== SUMMARY: {testbed} L0 (floor={}) ===", ctx.floor);
    println!(
        "{:<16} {:<18} {:>6} {:>6} {:>6} {:>8} {:>5} {:>13} {:>7} {:>7} {:>7} {:>9} {:>10} {:>4} {:>6} {:>8}",
        "experiment", "tag", "best", "floor", "gap", "evals", "gens", "origin", "xover%", "mut%",
        "ld%", "conv_gen", "div_o(s→e)", "le", "xover", "wall_s",
    );
    for r in &cx.rows {
        println!(
            "{:<16} {:<18} {:>6} {:>6} {:>+6} {:>8} {:>5} {:>13} {:>7.1} {:>7.1} {:>7.1} {:>9} {:>4.2}->{:<4.2} {:>4} {:>6} {:>8.1}",
            r.experiment,
            r.tag,
            r.final_best,
            r.floor,
            r.gap_to_floor,
            r.evals,
            r.generations,
            r.winner_origin,
            r.pct_xover_improved,
            r.pct_mut_improved,
            r.pct_ld_improved,
            r.convergence_gen,
            r.div_order_start,
            r.div_order_end,
            r.local_elite,
            r.crossover_kind,
            r.wall_secs,
        );
    }
    println!("\nCSV: {}", csv_path.display());
    println!("JSONL (per run): {}/{}_<experiment>_<tag>.jsonl", dir.display(), testbed);
}
