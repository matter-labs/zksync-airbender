//! Task 9 (CS-M0): the engine driver [`cs_schedule_bwd_layer`] — the top-level
//! assembly of the hint-model backward-schedule pipeline.
//!
//! ## Revision 4 (hint-model, binding)
//!
//! `compile + certify` is the SOLE decision authority; the offline model is only a
//! ranking hint. This driver wires the four consumed stages into one non-regressing
//! schedule:
//!
//! 1. **Canonical baseline** — `distill(.., None)` + [`compile_distilled_traced`] at
//!    `budget`: the exact uncached per-demand-recompute compile the fixture gates pin.
//!    It is BOTH the non-regression floor and the fallback if the CS path errors or
//!    fails to beat it.
//! 2. **Constructive order** — [`construct_unit_order`] over the canonical reuse
//!    structure yields a deterministic unit permutation; `distill(.., Some(&perm))`
//!    re-interns in that order.
//! 3. **Priced greedy** — [`coordinate_correct_frozen`] seeds the `lower==place==
//!    budget` all-`Bypass` frozen demand, then [`priced_rounds`] runs the
//!    compiler-in-the-loop compound + leaf reclaim (compile+certify validated per
//!    candidate; the model never selects).
//! 4. **Ship + certify** — the returned plan is recompiled to the SHIPPED program via
//!    [`compile_distilled_planned`], then [`certify`]d.
//!
//! ## Non-regression by construction
//!
//! Mirrors `search_bwd_layer` (`bwd/search.rs:475-483`): the CS lexicographic key
//! `(infeasible, traffic, instrs)` must STRICTLY beat the canonical baseline's;
//! otherwise the baseline outcome is returned (`plan: None`, identity permutation,
//! `fell_back_to_baseline: true`). Any `Err` anywhere in the CS path (a
//! `BudgetBelowFloor` from a construction that raised the placement floor above
//! `budget`, or otherwise) also falls back — the engine NEVER panics on a schedule
//! problem. The forward program is untouched: this is a bwd/new-module + test-only
//! addition, so fwd byte-identity is inviolable by construction.

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, ExprId, FieldKind, ReadPlace};

use super::compile::{
    compile_distilled_planned, compile_distilled_traced, BwdCompiledLayer, BwdTrafficStats,
};
use super::construct::construct_unit_order;
use super::distill::{distill, stable_distilled_site_domain, DistilledLayer};
use super::fif::coordinate_correct_frozen;
use super::plan::BwdOccurrencePlan;
use super::price::priced_rounds;
use super::trace::{certify, BwdCompileTrace, BwdEvent, CertificateReport};
use crate::fwd::error::CompileError;

/// The full outcome of one [`cs_schedule_bwd_layer`] run.
///
/// `compiled` is the SHIPPED backward program — the value-parity gate and the Task-11
/// comparator run against it directly, with no re-derivation — and `pins` (the
/// committed compound cone-suppression set) feeds the comparator ledger.
/// `stats`/`instrs`/`certificate` describe exactly `compiled`; `rounds`/`converged`
/// report the priced-round activity that produced the CS `plan`.
///
/// `fell_back_to_baseline` records whether the CS path failed to beat (or errored out
/// below) the canonical baseline. When it is `true`, `compiled` is the canonical
/// `decisions:None` baseline compile, `plan` is `None`, `unit_permutation` is the
/// identity `0..n`, `pins` is empty, and `rounds`/`converged` are `0`/`false`.
#[derive(Clone, Debug)]
pub struct CsOutcome {
    pub unit_permutation: Vec<usize>,
    pub plan: Option<BwdOccurrencePlan>,
    pub compiled: BwdCompiledLayer,
    pub pins: Vec<ExprId>,
    pub stats: BwdTrafficStats,
    pub instrs: usize,
    pub certificate: CertificateReport,
    pub rounds: usize,
    pub converged: bool,
    pub fell_back_to_baseline: bool,
}

/// The lexicographic non-regression key `(infeasible, traffic, instrs)` — lower is
/// better, feasible (`false`) sorts first. Identical shape to `search_bwd_layer`'s
/// `objective_key`, so the CS driver's non-regression contract matches the GA search's.
fn schedule_key(infeasible: bool, traffic: usize, instrs: usize) -> (bool, usize, usize) {
    (infeasible, traffic, instrs)
}

/// True iff `trace` recorded a replay divergence from its plan.
fn diverged(trace: &BwdCompileTrace) -> bool {
    trace.events.iter().any(|e| matches!(e, BwdEvent::Diverge { .. }))
}

/// The certificate report of a compile+trace (regardless of pass/fail) plus whether the
/// pair is feasible: it certifies EXACTLY (`counted == reported`) AND never diverged.
fn report_and_feasible(
    c: &BwdCompiledLayer,
    trace: &BwdCompileTrace,
) -> (CertificateReport, bool) {
    match certify(c, trace) {
        Ok(r) => (r, !diverged(trace)),
        Err(r) => (r, false),
    }
}

/// The constructive CS path, all-or-nothing: on any compile error the caller falls
/// back to the canonical baseline (`try_cs_path` propagates the `Err`). Returns the
/// constructed permutation, the priced plan/pins/round-counters, and the SHIPPED
/// compile with its certificate report + feasibility.
struct CsPath {
    unit_permutation: Vec<usize>,
    plan: BwdOccurrencePlan,
    pins: Vec<ExprId>,
    compiled: BwdCompiledLayer,
    report: CertificateReport,
    feasible: bool,
    rounds: usize,
    converged: bool,
}

fn try_cs_path(
    layer: &DagLayer,
    regime: BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
    bl_d: &DistilledLayer,
) -> Result<CsPath, CompileError> {
    // (2) constructive order off the canonical distillation's reuse structure.
    let stable_domain = stable_distilled_site_domain(bl_d);
    let perm = construct_unit_order(layer, bl_d, &stable_domain);

    // (3) re-distill in the constructed order, seed the coordinate-correct frozen
    // demand, and run the compiler-in-the-loop priced greedy.
    let d = distill(layer, regime, cross, Some(&perm));
    let frozen0 = coordinate_correct_frozen(&d, budget)?;
    let outcome = priced_rounds(&d, budget, frozen0)?;

    // (4) recompile the returned plan to the SHIPPED program, then certify it.
    let (compiled, trace) = compile_distilled_planned(&d, budget, &outcome.plan)?;
    let (report, feasible) = report_and_feasible(&compiled, &trace);

    Ok(CsPath {
        unit_permutation: perm,
        plan: outcome.plan,
        pins: outcome.pins,
        compiled,
        report,
        feasible,
        rounds: outcome.rounds,
        converged: outcome.converged,
    })
}

/// Assemble the canonical-baseline `CsOutcome` (the non-regression fallback): identity
/// permutation, no plan, no pins, and the baseline compile's own stats/instrs/report.
fn baseline_outcome(
    n_units: usize,
    bl_c: BwdCompiledLayer,
    bl_report: CertificateReport,
) -> CsOutcome {
    CsOutcome {
        unit_permutation: (0..n_units).collect(),
        plan: None,
        stats: bl_c.stats_ext,
        instrs: bl_c.stats.program_lanes,
        compiled: bl_c,
        pins: Vec::new(),
        certificate: bl_report,
        rounds: 0,
        converged: false,
        fell_back_to_baseline: true,
    }
}

/// Schedule one backward layer × regime at `budget` via the hint-model pipeline
/// (constructive order → coordinate-correct freeze → compiler-in-the-loop priced greedy
/// → certify → non-regression fallback). See the module docs for the full contract.
///
/// NEVER panics on a schedule problem: an infeasible or non-improving CS path falls
/// back to the canonical `decisions:None` baseline. It panics ONLY if even that
/// baseline is infeasible at `budget` — a genuine layer/budget problem (the
/// `PINNED_B16_INFEASIBLE` class), mirroring `search_bwd_layer`'s single hard-fail.
pub fn cs_schedule_bwd_layer(
    layer: &DagLayer,
    regime: BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
) -> CsOutcome {
    // ── (1) canonical baseline: the non-regression floor AND the fallback ──────────
    let bl_d = distill(layer, regime, cross, None);
    let n_units = bl_d.unit_order.len();
    let (bl_c, bl_trace) = compile_distilled_traced(&bl_d, budget, None).unwrap_or_else(|e| {
        panic!(
            "cs_schedule_bwd_layer: even the no-decisions canonical baseline is \
             infeasible ({regime:?}, budget {budget}, {n_units} units): {e:?}"
        )
    });
    let (bl_report, bl_feasible) = report_and_feasible(&bl_c, &bl_trace);
    let bl_traffic = bl_c.stats_ext.global + bl_c.stats_ext.fold_traffic;
    let bl_key = schedule_key(!bl_feasible, bl_traffic, bl_c.stats.program_lanes);

    // ── run the CS path; fall back on any compile error ────────────────────────────
    let cs = match try_cs_path(layer, regime, cross, budget, &bl_d) {
        Ok(cs) => cs,
        Err(_) => return baseline_outcome(n_units, bl_c, bl_report),
    };

    // ── non-regression: ship CS only if it STRICTLY beats the baseline key ─────────
    let cs_traffic = cs.compiled.stats_ext.global + cs.compiled.stats_ext.fold_traffic;
    let cs_instrs = cs.compiled.stats.program_lanes;
    let cs_key = schedule_key(!cs.feasible, cs_traffic, cs_instrs);
    if cs_key < bl_key {
        CsOutcome {
            unit_permutation: cs.unit_permutation,
            plan: Some(cs.plan),
            stats: cs.compiled.stats_ext,
            instrs: cs_instrs,
            compiled: cs.compiled,
            pins: cs.pins,
            certificate: cs.report,
            rounds: cs.rounds,
            converged: cs.converged,
            fell_back_to_baseline: false,
        }
    } else {
        baseline_outcome(n_units, bl_c, bl_report)
    }
}
