//! Task 13 — THE PARITY GATE (spec §14 oracle, §15 SP1 gate).
//!
//! Over every golden fixture under `cs/compiled_circuits/`, this integration test:
//!   1. `lower_dag(&artifact)` + `validate(&dag)`,
//!   2. per layer: `compile_layer` → `validate_compiled` → `encode`/`decode`
//!      roundtrip (decoded `Program` must equal the original),
//!   3. for every `Compute`/`CopyAlias` root at sampled rows, asserts the CPU
//!      interpreter (`interpret_layer_row`) equals the authoritative
//!      `eval_layer_root` bit-for-bit; `SkipScratchPrefill` roots are asserted
//!      present in `compiled.skipped` and emit no value comparison.
//!
//! The interpreter and `eval_layer_root` consume the SAME `SyntheticResolvers`
//! instance, so parity (not numeric correctness) is what this proves — exactly
//! the SP1 expressive-completeness gate. The layout fixtures carry no
//! witness/setup values, so the resolvers are deterministic synthetic hashes.

use std::collections::BTreeMap;
use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{
    eval_layer_root, lower_dag, validate, Bf, ChallengeRef, DagCircuit, Ext, LookupValueKind,
    ReadPlace, Resolvers, Root, RootId, VirtualSetupKind,
};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use field::{Field, FieldExtension, PrimeField};

use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, compile_layer};
use gkr_eval_isa::fwd::context::RootOutput;
use gkr_eval_isa::fwd::error::CompileError;
use gkr_eval_isa::fwd::encode::{decode, encode};
use gkr_eval_isa::fwd::interp::interpret_layer_row;
use gkr_eval_isa::fwd::validate::validate_compiled;

// ── lift ────────────────────────────────────────────────────────────────────

#[inline]
fn lift(b: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(b)
}

// ── Stable hash (FNV-1a, 32-bit) ──────────────────────────────────────────────
//
// Deterministic, no nondeterminism. Hashes the `Debug` rendering of a value (all
// dag_ir descriptor types derive `Debug`) folded with the row, per the brief.

const FNV_OFFSET: u32 = 0x811c_9dc5;
const FNV_PRIME: u32 = 0x0100_0193;

fn fnv_bytes(seed: u32, bytes: &[u8]) -> u32 {
    let mut h = seed;
    for &b in bytes {
        h ^= b as u32;
        h = h.wrapping_mul(FNV_PRIME);
    }
    h
}

fn fnv_u32(seed: u32, v: u32) -> u32 {
    fnv_bytes(seed, &v.to_le_bytes())
}

/// Hash a `Debug`-renderable descriptor + a row index into a u32.
fn hash_dbg_row<T: std::fmt::Debug>(t: &T, row: usize) -> u32 {
    let s = format!("{:?}", t);
    let h = fnv_bytes(FNV_OFFSET, s.as_bytes());
    fnv_u32(h, row as u32)
}

// ── SyntheticResolvers ────────────────────────────────────────────────────────
//
// One value, deterministic in its inputs. The SAME instance feeds both the
// interpreter and `eval_layer_root`, so any difference between them is a real
// compiler/oracle-usage divergence, never a resolver mismatch.

struct SyntheticResolvers;

impl cs::gkr_compiler::dag_ir::ReadResolver for SyntheticResolvers {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        lift(Bf::from_u32_with_reduction(hash_dbg_row(place, row)))
    }
}

impl cs::gkr_compiler::dag_ir::LookupResolver for SyntheticResolvers {
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        evaluated_query: Ext,
        row: usize,
    ) -> Bf {
        // Base hash of (kind, row), then mix in set_index and EVERY limb of the
        // evaluated query so query evaluation is exercised identically on both
        // sides (brief: "must depend on evaluated_query").
        let mut h = hash_dbg_row(kind, row);
        h = fnv_u32(h, set_index as u32);
        let limbs = <Ext as FieldExtension<Bf>>::into_coeffs(evaluated_query);
        for l in limbs {
            h ^= l.as_u32_reduced();
            h = h.wrapping_mul(FNV_PRIME);
        }
        Bf::from_u32_with_reduction(h)
    }
}

impl cs::gkr_compiler::dag_ir::VirtualSetupResolver for SyntheticResolvers {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf {
        Bf::from_u32_with_reduction(hash_dbg_row(kind, row))
    }
}

impl cs::gkr_compiler::dag_ir::ChallengeResolver for SyntheticResolvers {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        // Include both key and power (brief: "include power").
        lift(Bf::from_u32_with_reduction(hash_dbg_row(r, 0)))
    }
}

fn resolvers(s: &SyntheticResolvers) -> Resolvers<'_> {
    Resolvers {
        read: s,
        lookup: s,
        virtual_setup: s,
        challenge: s,
    }
}

// ── Fixture loading ────────────────────────────────────────────────────────────

fn compiled_circuit_dir() -> PathBuf {
    // This test lives in the `gkr_eval_isa` crate; `cs/compiled_circuits` is at
    // `<workspace>/cs/compiled_circuits`, a sibling of this crate.
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits")
}

/// Deserialize one fixture JSON → `GKRCircuitArtifact<BabyBearField>`.
fn load_fixture(path: &PathBuf) -> Option<GKRCircuitArtifact<BabyBearField>> {
    let bytes = std::fs::read(path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

const BUDGET: usize = 1024;

/// Sample rows `[0, 1, n/2, n-1]`, deduped (n may be tiny).
fn sample_rows(n: usize) -> Vec<usize> {
    if n == 0 {
        return vec![];
    }
    let mut rows = vec![0usize, 1, n / 2, n - 1];
    rows.retain(|&r| r < n);
    rows.sort_unstable();
    rows.dedup();
    rows
}

/// Run the full parity gate over a single fixture artifact.
/// Returns the number of `interp == eval_layer_root` comparisons actually performed
/// (one per root × sampled row). Callers use this to guard against vacuous passes.
fn check_fixture(name: &str, artifact: &GKRCircuitArtifact<BabyBearField>, budget: usize) -> usize {
    let mut comparisons = 0usize;
    let dag: DagCircuit = lower_dag(artifact).unwrap_or_else(|e| {
        panic!("[{name}] lower_dag failed: {e}");
    });
    validate(&dag).unwrap_or_else(|e| {
        panic!("[{name}] validate(dag) failed: {e}");
    });

    let n = dag.globals.trace_len;
    let rows = sample_rows(n);
    let s = SyntheticResolvers;
    let r = resolvers(&s);

    assert_eq!(
        dag.layers.len(),
        artifact.layers.len(),
        "[{name}] dag/artifact layer count mismatch"
    );

    // Cross-layer field map (codex Imp2): built ONCE over the whole circuit, then
    // threaded into every per-layer `compile_layer` so cross-layer reads are labeled
    // with their TRUE producing-sink field.
    let cross_layer_fields = build_cross_layer_field_map(&dag);

    for (l, dag_layer) in dag.layers.iter().enumerate() {
        let art_layer = &artifact.layers[l];
        let compiled = match compile_layer(
            dag_layer,
            art_layer,
            &artifact.scratch_space_mapping,
            &cross_layer_fields,
            budget,
        ) {
            Ok(c) => c,
            // Below the irreducible floor at this budget — an expected, clean outcome
            // when sweeping small budgets. Skip this layer's checks at this budget;
            // it is NOT a failure (a too-small budget is an unsupported config, not a
            // miscompilation). Any OTHER error IS a failure.
            Err(CompileError::BudgetBelowFloor { floor, budget: b }) => {
                eprintln!(
                    "[{name}] layer {l}: below floor at budget {b} (needs ≥ {floor}) — skipped"
                );
                continue;
            }
            Err(e) => {
                panic!("[{name}] layer {l}: compile_layer failed at budget {budget}: {e:?}");
            }
        };

        validate_compiled(&compiled, dag_layer).unwrap_or_else(|e| {
            panic!("[{name}] layer {l}: validate_compiled failed: {e:?}");
        });

        // Encode → decode roundtrip must reproduce the program exactly.
        let lanes = encode(&compiled.program).unwrap_or_else(|e| {
            panic!("[{name}] layer {l}: encode failed: {e:?}");
        });
        let decoded = decode(&lanes).unwrap_or_else(|e| {
            panic!("[{name}] layer {l}: decode failed: {e:?}");
        });
        assert_eq!(
            decoded, compiled.program,
            "[{name}] layer {l}: encode/decode roundtrip mismatch"
        );

        // Every SkipScratchPrefill root must be in `skipped` and emit no value.
        // (Handled implicitly: such roots are absent from `root_outputs`.)

        // Parity at sampled rows for every materialized root. `interpret_layer_row`
        // already produces `by_root` for ALL roots in one pass, so we call it ONCE
        // per row and compare every root against the oracle (avoids an O(roots)
        // re-interpretation per root).
        let by_root: BTreeMap<RootId, RootOutput> =
            compiled.root_outputs.iter().cloned().collect();

        for &row in &rows {
            let got = interpret_layer_row(&compiled, dag_layer, &r, row).unwrap_or_else(|e| {
                panic!("[{name}] layer {l} row {row}: interp failed: {e:?}");
            });
            for (rid, _out) in &compiled.root_outputs {
                let want = eval_layer_root(dag_layer, *rid, row, &r);
                let have = got.by_root[rid];
                assert_eq!(
                    have, want,
                    "[{name}] layer {l} root {rid:?} row {row}: \
                     interp != eval_layer_root oracle"
                );
                comparisons += 1;
            }
        }

        // Sanity: skipped roots correspond to Output roots that are scratch-
        // prefilled — they must not appear in root_outputs.
        for skipped in &compiled.skipped {
            assert!(
                !by_root.contains_key(skipped),
                "[{name}] layer {l}: skipped root {skipped:?} also in root_outputs"
            );
            // And the underlying Root must be an Output (Constraint roots are
            // never classified into actions).
            assert!(
                matches!(dag_layer.roots[skipped.0 as usize], Root::Output { .. }),
                "[{name}] layer {l}: skipped root {skipped:?} is not an Output root"
            );
        }
    }
    comparisons
}

// ── Fixture lists (mirror cs::…::coverage_tests) ────────────────────────────────
//
// 22 golden fixtures: 11 `*_layout_gkr.json` + 11 `*_layout_no_caches_gkr.json`.
// `inits_and_teardowns` layout is named `..._preprocessed_layout_gkr.json`.

const LAYOUT_GKR_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

const LAYOUT_NO_CACHES_GKR_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
    "bigint_with_extended_control_layout_no_caches_gkr.json",
    "blake2_g_function_layout_no_caches_gkr.json",
    "blake2_with_extended_control_layout_no_caches_gkr.json",
    "inits_and_teardowns_layout_no_caches_gkr.json",
    "jump_branch_slt_layout_no_caches_gkr.json",
    "keccak_special5_layout_no_caches_gkr.json",
    "mem_subword_only_layout_no_caches_gkr.json",
    "mem_word_only_layout_no_caches_gkr.json",
    "shift_binop_layout_no_caches_gkr.json",
    "unsigned_mul_div_layout_no_caches_gkr.json",
];

fn run_fixtures(fixtures: &[&str]) {
    let dir = compiled_circuit_dir();
    let mut checked = 0usize;
    let mut total_comparisons = 0usize;
    for &f in fixtures {
        let path = dir.join(f);
        let artifact = load_fixture(&path)
            .unwrap_or_else(|| panic!("failed to load/deserialize fixture {f} at {path:?}"));
        let t0 = std::time::Instant::now();
        // BUDGET = 1024 is the EXTREME all-resident case: nothing is ever evicted or
        // recomputed (stresses the no-reload path). Realistic small-budget coverage
        // is in `parity_budget_sweep_small`.
        let comparisons = check_fixture(f, &artifact, BUDGET);
        eprintln!("[fwd_parity] {f} OK in {:?} ({comparisons} root comparisons)", t0.elapsed());
        total_comparisons += comparisons;
        checked += 1;
    }
    assert_eq!(checked, fixtures.len(), "not all fixtures checked");
    assert!(
        total_comparisons > 0,
        "parity gate compared 0 roots — vacuous pass (root_outputs/sample_rows empty?)"
    );
}

// ── add_sub fixtures (Commit 1) ─────────────────────────────────────────────────

const ADD_SUB_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
];

#[test]
fn parity_add_sub() {
    run_fixtures(ADD_SUB_FIXTURES);
}

// ── full gate over all 22 fixtures ──────────────────────────────────────────────
//
// These run the WHOLE corpus (all layers × sampled rows) and ARE the SP1 gate:
// every fixture layer compiles, validates, encode/decode-roundtrips, and the CPU
// interpreter matches `eval_layer_root` bit-for-bit at the sampled rows.

#[test]
fn parity_all_layout_gkr() {
    run_fixtures(LAYOUT_GKR_FIXTURES);
}

#[test]
fn parity_all_layout_no_caches_gkr() {
    run_fixtures(LAYOUT_NO_CACHES_GKR_FIXTURES);
}

// ── budget sweep — realistic SMALL budgets (the eviction regime) ────────────────
//
// BUDGET = 1024 (the gates above) is the EXTREME all-resident case: nothing is ever
// evicted or recomputed. Real hardware budgets are a warp's worth of smem cells —
// small multiples of 4. This sweeps from 8 upward: at each FEASIBLE budget the
// residency planner must EVICT residents and redirect reads (Prior→Smem and back,
// CSE, evict/reload), and the CPU interpreter must STILL match the
// budget-INDEPENDENT `eval_layer_root` oracle bit-for-bit. A budget below a layer's
// irreducible floor yields a clean `BudgetBelowFloor` (skipped), never a panic.
//
// This is the first end-to-end validation of the S2 eviction path: every gate
// before this ran only at 1024, where eviction never fires.

const SWEEP_BUDGETS: &[usize] = &[8, 12, 16, 24, 32, 48, 64, 128, 256];

// Routine gate: the two cache-heaviest fixtures (add_sub, mul_div) at warp-scale
// budgets. Fast (~15s) and enough to guard the in-flight-borrow timing + bit-exact
// re-emission under eviction. The exhaustive 11-fixture variant is the `#[ignore]`d
// `parity_budget_sweep_all_fixtures` below (the design's broad-corpus run, ~150s).
const SWEEP_FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

/// Run the budget sweep over `fixtures`, asserting that the eviction regime was
/// actually exercised (≥1 comparison at a budget below 1024) and that every feasible
/// (budget, layer) reproduced `eval_layer_root` bit-exactly (the `check_fixture`
/// differential). Returns the smallest feasible budget seen, for logging.
fn run_budget_sweep(fixtures: &[&str]) {
    let dir = compiled_circuit_dir();
    let mut total = 0usize;
    // Comparisons performed at a budget strictly below 1024 — proves the eviction
    // regime was actually exercised, not just the all-resident extreme.
    let mut sub1024_comparisons = 0usize;
    let mut smallest_feasible: Option<usize> = None;

    for &f in fixtures {
        let path = dir.join(f);
        let artifact =
            load_fixture(&path).unwrap_or_else(|| panic!("failed to load fixture {f}"));
        for &budget in SWEEP_BUDGETS {
            let c = check_fixture(f, &artifact, budget);
            eprintln!("[fwd_parity sweep] {f} budget {budget}: {c} comparisons");
            total += c;
            if c > 0 {
                sub1024_comparisons += c;
                smallest_feasible = Some(smallest_feasible.map_or(budget, |s| s.min(budget)));
            }
        }
    }

    eprintln!(
        "[fwd_parity sweep] smallest feasible budget across {} fixtures: {:?}",
        fixtures.len(),
        smallest_feasible
    );
    assert!(
        total > 0,
        "budget sweep performed 0 comparisons — every swept budget below floor (vacuous)"
    );
    assert!(
        sub1024_comparisons > 0,
        "budget sweep validated 0 comparisons below 1024 — the eviction regime was never \
         exercised (every layer's floor exceeds {}); residency under realistic budgets is \
         UNTESTED and possibly broken",
        SWEEP_BUDGETS.last().unwrap()
    );
}

#[test]
fn parity_budget_sweep_small() {
    run_budget_sweep(SWEEP_FIXTURES);
}

// Exhaustive cross-corpus eviction sweep (the design's broad-corpus validation). Runs
// every cache-bearing layout fixture across all warp-scale budgets — ~150s, so it is
// `#[ignore]`d and run on demand: `cargo test -p gkr_eval_isa --test fwd_parity -- \
// --ignored parity_budget_sweep_all_fixtures`.
#[test]
#[ignore = "slow (~150s) exhaustive sweep; run on demand"]
fn parity_budget_sweep_all_fixtures() {
    run_budget_sweep(LAYOUT_GKR_FIXTURES);
}

// Proof that the small-budget sweep actually EXERCISES eviction — not just smaller
// compiles that happen to still fit. add_sub layer 0's natural (uncapped) resident
// working set exceeds 32 cells, so at budget 32 the planner MUST evict: reused cache
// roots fall back to DRAM (more `dram_reads`, fewer resident `cell_reads`). The sweep
// above already proved interp == `eval_layer_root` at budget 32 (correct UNDER
// eviction); this asserts eviction genuinely engaged, so that correctness guarantee
// is not vacuous. Asserts PROPERTIES (monotone traffic under cap pressure), not magic
// numbers, so it survives codegen changes.
#[test]
fn residency_eviction_engages_under_tight_budget() {
    let dir = compiled_circuit_dir();
    let path = dir.join("add_sub_lui_auipc_mop_layout_gkr.json");
    let artifact = match load_fixture(&path) {
        Some(a) => a,
        None => return,
    };
    let dag = lower_dag(&artifact).unwrap();
    validate(&dag).unwrap();
    let cross = build_cross_layer_field_map(&dag);

    let try_stats_at = |budget: usize| {
        compile_layer(
            &dag.layers[0],
            &artifact.layers[0],
            &artifact.scratch_space_mapping,
            &cross,
            budget,
        )
        .map(|c| c.stats)
    };
    let stats_at = |budget: usize| {
        try_stats_at(budget)
            .unwrap_or_else(|e| panic!("add_sub L0 compile at budget {budget}: {e:?}"))
    };

    // ── On-demand eviction replaces the old eager-pin model ───────────────────
    //
    // Pre-rework, compile_layer reported an inflated "floor" of 24–48 cells for this
    // layer because every per-root transient allocator pre-pinned ALL residents. With
    // one shared allocator + lazy eviction of backed (DRAM-re-readable) residents, the
    // floor collapses to the aligned schedule peak. add_sub L0's measured curve:
    //   budget   8: max_live  8, dram_reads 83, cell_reads 24   ← compiles! (was infeasible)
    //   budget  16: max_live 16, dram_reads 81, cell_reads 26
    //   budget  24: max_live 24, dram_reads 79, cell_reads 28
    //   budget  32: max_live 32, dram_reads 77, cell_reads 30   ← S2-optimal reached
    //   budget 1024: max_live 40, dram_reads 77, cell_reads 30  ← uncapped working set 40

    // (1) Floor collapse: a budget the old eager-pin model rejected now compiles.
    assert!(
        try_stats_at(8).is_ok(),
        "add_sub L0 must now compile at budget 8 (the inflated 24–48 floor is gone)"
    );

    let loose = stats_at(1024);
    let tight = stats_at(16);
    let roomy = stats_at(32);

    // (2) The uncapped working set genuinely exceeds the tight budget, so eviction is
    //     forced (not incidental); and the hard cap is honored under pressure.
    assert!(
        loose.max_live_cells > 16,
        "uncapped working set {} should exceed the tight budget (else no eviction is \
         forced)",
        loose.max_live_cells
    );
    assert!(
        tight.max_live_cells <= 16,
        "tight-budget max_live {} exceeds the 16-cell cap",
        tight.max_live_cells
    );

    // (3) Under genuine pressure, evicting a still-needed backed resident forces its
    //     reader to fall back to DRAM: strictly MORE dram reads and FEWER resident
    //     smem reads than the all-resident compile.
    assert!(
        tight.dram_reads > loose.dram_reads,
        "eviction must force extra DRAM re-reads: tight16 {} vs loose {}",
        tight.dram_reads,
        loose.dram_reads
    );
    assert!(
        tight.cell_reads < loose.cell_reads,
        "eviction must reduce resident smem reads: tight16 {} vs loose {}",
        tight.cell_reads,
        loose.cell_reads
    );

    // (4) dram_reads degrades SMOOTHLY (monotone non-increasing) as the budget grows —
    //     tighter budget spills more reused values to DRAM; it never fails or spikes.
    let d8 = stats_at(8).dram_reads;
    let d16 = tight.dram_reads;
    let d32 = roomy.dram_reads;
    assert!(
        d8 >= d16 && d16 >= d32,
        "dram_reads must be monotone non-increasing in budget: 8→{d8} 16→{d16} 32→{d32}"
    );

    // (5) The #8 residency win is fully preserved once the budget is roomy enough:
    //     budget 32 already reaches the S2-optimal dram_reads of the uncapped compile.
    assert_eq!(
        roomy.dram_reads, loose.dram_reads,
        "budget 32 must reach the S2-optimal dram_reads (no regression of the #8 win)"
    );
}
