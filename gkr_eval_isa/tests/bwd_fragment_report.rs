//! CS-M5a Task 9: fragment resource report — identity + planned probe (spec §7).
//!
//! Mechanical reporting only (no gating beyond the two hard asserts below). Per
//! fixture x every bwd layer x {R0, Ext} at b16, this reports resource numbers for
//! TWO fragment-mode programs:
//!
//!   * `identity` — the uncached identity-schedule-order program
//!     (`compile_distilled_fragments(&d, 16, None)`, `order: None`).
//!   * `planned`  — the Task-7 constructed fragment order, replayed through the
//!     Task-8 all-`Bypass` planned pipeline: `order = construct_fragment_order(...)`,
//!     `frozen0 = coordinate_correct_frozen_with_backend(&d, 16, &FragmentBackend{order})`,
//!     `plan = all_bypass_plan(&frozen0)` (a local copy of `bwd_fragment_planned.rs`'s
//!     helper — plan-mode idioms mirrored exactly, not reused across test binaries),
//!     `compile_distilled_fragments_planned(&d, 16, &plan, Some(&order))`.
//!
//! The priced/shipped candidates (the actual CS-M5a search/pricing output) do NOT
//! exist yet — that is Task 10 — and are reported separately in Task 11. This report
//! covers ONLY the two probes above: an uncached lower bound and an all-Bypass replay
//! of the constructed order (never a priced/searched program).
//!
//! ## Line format
//!
//! One `REPORT` line per (program-kind, fixture, layer, regime), prefixed so the
//! saved+sorted file self-identifies every row:
//!
//! ```text
//! REPORT <kind> <fixture> L<layer> <regime> fragments=N program_lanes=L (cap 12288) \
//!   recipes=R terms_total=T max_terms=M factors_total=F recipe_encoded_bytes=B \
//!   c_init_terms=K traffic=G+F
//! ```
//!
//! * `fragments`  — `d.fragments.fragments.len()` (every fragment, trivial or not).
//! * `program_lanes` — `encode(&c.program).len()`, the wire-encoded `u16` lane count
//!   (mirrors `fwd_vm_desc_census.rs`'s `program_lanes`, NOT `CompileStats::
//!   program_lanes` which is the raw instruction count) — checked against the fwd-VM
//!   inline-program-ABI precedent cap of 12,288 lanes (spec §7).
//! * `recipes`/`terms_total`/`max_terms`/`factors_total` — over the NON-TRIVIAL
//!   fragment `MergedRecipe`s only (`!recipe.is_trivial()`) — exactly the set
//!   `fragment_descs` (`bwd/compile.rs`) interns a `Coefficient` descriptor for. A
//!   trivial recipe (the scalar `1`) needs no descriptor and carries no reportable
//!   resource cost, so it is excluded here the same way it is excluded from emission.
//! * `c_init_terms` — `d.fragments.c_init.terms.len()`, reported SEPARATELY and NOT
//!   folded into `recipes`/`terms_total`/`max_terms`/`factors_total`/
//!   `recipe_encoded_bytes`: `c_init` is the single always-present scalar-pure addend
//!   (its own `AccInit` descriptor, interned iff non-empty — `fragment_descs`), a
//!   different resource class from the per-fragment coefficient table.
//! * `recipe_encoded_bytes` — see `RECIPE_HEADER_BYTES` below for the exact formula.
//! * `traffic=G+F` — `c.stats_ext.global` and `c.stats_ext.fold_traffic` printed as the
//!   literal two addends (never pre-summed), matching the `(global + fold_traffic)`
//!   objective used throughout `bwd/price.rs`/`bwd/engine.rs`.
//!
//! ## Hard asserts (everything else is reported, not asserted — spec §7)
//!
//! * `max_terms <= 64` — a single coefficient's term count stays far below any
//!   plausible per-coefficient encoding width.
//! * `program_lanes < 65536` — the encoded lane stream must fit a `u16`-addressable
//!   index space (the fwd-VM ABI's own encoding precedent).
//!
//! ## Error handling
//!
//! Per Task 8's finding, fragment-R0 admission hits a placement `ExtCellMisaligned`
//! only in `Retain` trials; the all-`Bypass` replay this task drives was clean on
//! every fixture/layer/regime there. If the planned probe here nonetheless errors on
//! some (layer, regime), this test prints a `REPORT-ERROR <kind> <ctx>: <err>` line
//! (still matched by the `^REPORT` save filter) and continues — it does not panic.
//!
//! ## Run
//!
//! ```text
//! RUST_MIN_STACK=1073741824 RUSTFLAGS="-Awarnings" \
//!   cargo test -p gkr_eval_isa --release --test bwd_fragment_report -- --ignored --nocapture \
//!   2>&1 | rg '^REPORT' | sort > \
//!   /home/rr/code/zksync-airbender/blue/.agents/plans/m5a-resource-report.txt
//! ```

mod common;

use common::{encode, layers_with_bwd_roots, FIXTURES};

use cs::gkr_compiler::dag_ir::BwdRegime;
use gkr_eval_isa::bwd::compile::{
    compile_distilled_fragments, compile_distilled_fragments_planned, BwdCompiledLayer,
    FragmentBackend,
};
use gkr_eval_isa::bwd::construct::construct_fragment_order;
use gkr_eval_isa::bwd::distill::{distill, stable_distilled_site_domain, DistilledLayer};
use gkr_eval_isa::bwd::fif::coordinate_correct_frozen_with_backend;
use gkr_eval_isa::bwd::fragment::FragmentTable;
use gkr_eval_isa::bwd::plan::{plan_entries_fnv, BwdOccurrencePlan, PlanAction, PlanEntry};
use gkr_eval_isa::bwd::trace::FrozenDemand;

const BUDGET: usize = 16;

/// The fwd-VM inline-program-ABI precedent cap this report reviews `program_lanes`
/// against (spec §7; `fwd_vm_desc_census.rs`'s `PROGRAM_CAP`). NOT asserted here —
/// a required DELIVERABLE for human review, not a CS-M5a gate.
const PROGRAM_LANES_REVIEW_CAP: usize = 12288;

/// Directional per-recipe wire-format assumption for `recipe_encoded_bytes` (no CS-M5b
/// wire format is committed yet — this is a consistent accounting unit for the spec §7
/// review, mirroring the `u16`-lane convention `program_lanes`/`encode()` already use):
/// each encoded `MergedRecipe` carries a fixed 4-byte header (a `u16` term count plus a
/// `u16` reserved/alignment word), followed by 2 bytes per term (a `u16` slot — e.g. a
/// table index) and 2 bytes per factor (a `u16` index into a shared scalar-ref table).
const RECIPE_HEADER_BYTES: usize = 4;

// ── all-Bypass plan builder (local copy of `bwd_fragment_planned.rs`'s helper —
// each test binary is a separate crate target, so this is deliberately duplicated,
// not imported cross-binary) ─────────────────────────────────────────────────────

/// The all-`Bypass` plan over `frozen`'s domain serves, carrying `frozen`'s epoch /
/// `stream_reductions` so `compile_distilled_fragments_planned`'s epoch + `entries_fnv`
/// guards accept it. Mirrors `bwd_fragment_planned.rs::all_bypass_plan` /
/// `fif::all_bypass_plan` / `bwd_cs_engine.rs::coordinate_correct_baseline`.
fn all_bypass_plan(frozen: &FrozenDemand) -> BwdOccurrencePlan {
    let entries: Vec<PlanEntry> = frozen
        .domain_serves
        .iter()
        .map(|&(fp, _from)| PlanEntry { fp, action: PlanAction::Bypass })
        .collect();
    BwdOccurrencePlan {
        epoch: frozen.epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: frozen.stream_reductions,
        entries,
    }
}

// ── fragment resource stats ──────────────────────────────────────────────────────

#[derive(Default)]
struct FragmentStats {
    fragments: usize,
    recipes: usize,
    terms_total: usize,
    max_terms: usize,
    factors_total: usize,
    c_init_terms: usize,
    recipe_encoded_bytes: usize,
}

/// Compute the §7 `MergedRecipe` resource numbers from `table` (see the module doc for
/// exactly what is/isn't folded into which field).
fn fragment_stats(table: &FragmentTable) -> FragmentStats {
    let mut s = FragmentStats { fragments: table.fragments.len(), ..Default::default() };
    for f in &table.fragments {
        if f.recipe.is_trivial() {
            continue; // scalar `1`: no descriptor, no reportable resource cost
        }
        s.recipes += 1;
        let nt = f.recipe.terms.len();
        s.terms_total += nt;
        s.max_terms = s.max_terms.max(nt);
        for term in &f.recipe.terms {
            s.factors_total += term.factors.len();
        }
    }
    s.c_init_terms = table.c_init.terms.len();
    // Formula (documented above): terms x 2B + factors x 2B + one fixed header per
    // NON-TRIVIAL recipe (c_init excluded — see the module doc).
    s.recipe_encoded_bytes =
        s.terms_total * 2 + s.factors_total * 2 + s.recipes * RECIPE_HEADER_BYTES;
    s
}

// ── report line ───────────────────────────────────────────────────────────────────

#[allow(clippy::too_many_arguments)]
fn report(kind: &str, fixture: &str, li: usize, regime: BwdRegime, c: &BwdCompiledLayer, d: &DistilledLayer) {
    let program_lanes = encode(&c.program).len();
    let stats = fragment_stats(&d.fragments);

    assert!(
        stats.max_terms <= 64,
        "REPORT {kind} {fixture} L{li:02} {regime:?}: max_terms {} > 64",
        stats.max_terms
    );
    assert!(
        program_lanes < 65536,
        "REPORT {kind} {fixture} L{li:02} {regime:?}: program_lanes {program_lanes} >= 65536"
    );

    println!(
        "REPORT {kind} {fixture} L{li:02} {regime:?} fragments={} program_lanes={} \
         (cap {PROGRAM_LANES_REVIEW_CAP}) recipes={} terms_total={} max_terms={} \
         factors_total={} recipe_encoded_bytes={} c_init_terms={} traffic={}+{}",
        stats.fragments,
        program_lanes,
        stats.recipes,
        stats.terms_total,
        stats.max_terms,
        stats.factors_total,
        stats.recipe_encoded_bytes,
        stats.c_init_terms,
        c.stats_ext.global,
        c.stats_ext.fold_traffic,
    );
}

// ── the report ────────────────────────────────────────────────────────────────────

#[test]
#[ignore] // heavy: every fixture x every bwd layer x both regimes, run explicitly
fn fragment_resource_report() {
    let mut instances = 0usize;
    let mut errors = 0usize;

    for &name in FIXTURES {
        for (li, layer, cross) in layers_with_bwd_roots(name) {
            for &regime in &[BwdRegime::R0, BwdRegime::Ext] {
                let d = distill(&layer, regime, &cross, None);
                if d.skipped_decoder {
                    continue; // out of v1 in both regimes (fenced upstream — expected empty)
                }
                let ctx = format!("{name} L{li:02} {regime:?}");

                // 1. Identity-order uncached program.
                match compile_distilled_fragments(&d, BUDGET, None) {
                    Ok(c) => report("identity", name, li, regime, &c, &d),
                    Err(e) => {
                        println!("REPORT-ERROR identity {ctx}: {e:?}");
                        errors += 1;
                    }
                }

                // 2. Constructed-order all-Bypass planned program (Task 7 order + Task 8
                // planned pipeline, mirrored — never a raw traced freeze).
                let stable_domain = stable_distilled_site_domain(&d);
                let order = construct_fragment_order(&layer, &d, &stable_domain);
                let planned = coordinate_correct_frozen_with_backend(
                    &d,
                    BUDGET,
                    &FragmentBackend { order: order.clone() },
                )
                .map_err(|e| format!("{e:?}"))
                .and_then(|frozen0| {
                    let plan = all_bypass_plan(&frozen0);
                    compile_distilled_fragments_planned(&d, BUDGET, &plan, Some(&order))
                        .map_err(|e| format!("{e:?}"))
                });
                match planned {
                    Ok((c, _t)) => report("planned", name, li, regime, &c, &d),
                    Err(e) => {
                        println!("REPORT-ERROR planned {ctx}: {e}");
                        errors += 1;
                    }
                }

                instances += 1;
            }
        }
    }

    println!("fragment_resource_report: {instances} layer instances, {errors} REPORT-ERROR lines");
    assert!(instances > 0, "no layer instances exercised — enumeration broke");
}
