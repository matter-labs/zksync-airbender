//! Task 8 (CS-M5a): non-vacuous fragment planned-replay + pinned retention gate.
//!
//! This is the FIRST value-gating of the fragment PLAN-MODE code paths. Tasks 5-7
//! built `compile_distilled_fragments{,_traced,_planned}`, the `FragmentBackend` /
//! `coordinate_correct_frozen_with_backend` seed, and the constructive
//! `construct_fragment_order`, but no test ever replayed a plan through the fragment
//! driver and checked the result against the value oracle. In particular the plan-mode
//! arms of `lower_bwd_top_atom` (`fwd/compile/lower.rs`: resident-hit / source-admit /
//! compound-admit) were compiled but NEVER executed. The `Retain` trials here are what
//! finally drive them.
//!
//! # Per fixture × {R0, Ext} × every bwd layer at b16
//!
//! 1. `order = construct_fragment_order(...)` — the real (generally non-identity)
//!    constructed fragment schedule order (Task 7).
//! 2. `frozen0 = coordinate_correct_frozen_with_backend(&d, 16, &FragmentBackend{order})`
//!    — NEVER a raw traced freeze. Per `fif.rs`'s doc, every priced planner MUST seed
//!    from this planned all-`Bypass` `lower==place==budget` coordinate; so does this gate.
//! 3. All-`Bypass` planned replay (built from `frozen0.domain_serves`, mirroring
//!    `all_bypass_plan` / the term path's `coordinate_correct_baseline`):
//!    `compile_distilled_fragments_planned(&d, 16, &plan, Some(&order))` must
//!    (a) NOT diverge (`BwdEvent::Diverge` absent), (b) certify EXACTLY
//!    (`counted_traffic == reported_traffic`, exact integers), (c) match the independent
//!    value oracle bit-for-bit (`assert_bwd_value_parity` over the RAW canonical layer).
//!
//! # Certificate is an Ext-regime invariant
//!
//! `certify` recounts `TrafficRead` events against `stats_ext.global + fold_traffic`, and
//! that identity is exact ONLY in the folded Ext regime — the same reason the term-path
//! certificate gate (`bwd_cs_engine.rs::certificate_exact_on_baseline_and_planned`) runs
//! Ext L0 exclusively. In R0 even the shipped TERM driver's uncached compile fails to
//! certify (measured: add_sub L0 counted 343 vs reported 346), so certify is not a valid
//! tool there. This gate therefore asserts the EXACT certificate in the Ext regime, and
//! (a) no-diverge + (c) oracle value parity in BOTH regimes. The two pins are Ext L0.
//! 4. **Retain non-vacuity.** From the all-`Bypass` plan, pick a DOMAIN LEAF value (a
//!    `Source`/resolution atom — its resident hit suppresses NO descendant cone, so the
//!    serve stream is unchanged and the fail-closed matcher cannot EOF-diverge) with ≥ 2
//!    occurrences (a closing occurrence therefore exists), flip its earliest small-gap
//!    occurrence to `Retain`, recompile planned, and check the retention was actually
//!    REALIZED (an `Admit` of that value + a `Serve{from: Resident}` of it, no `Refuse`
//!    of it) — a REFUSED retain would pass (a)/(b)/(c) vacuously, which is precisely the
//!    silent-skip failure mode this task exists to prevent. Trial candidates
//!    (smallest-serve-gap first, bounded) until one is clean+realized, then assert the
//!    same three properties on that Retain-carrying program.
//!
//! **PINNED (unconditional):** ≥ 1 Retain trial MUST succeed on `bigint` L0 Ext AND on
//! `blake2_with_extended_control` (blake2_ext) L0 Ext. The gate FAILS if either pin
//! cannot retain — a "silently skip everything" outcome is the bug, not a pass.

mod common;

use std::collections::BTreeMap;

use common::{assert_bwd_value_parity, layers_with_bwd_roots, FIXTURES};
use cs::gkr_compiler::dag_ir::{BwdRegime, Expr, ExprId};
use gkr_eval_isa::bwd::compile::{compile_distilled_fragments_planned, FragmentBackend};
use gkr_eval_isa::bwd::construct::construct_fragment_order;
use gkr_eval_isa::bwd::distill::{distill, stable_distilled_site_domain, DistilledLayer};
use gkr_eval_isa::bwd::fif::coordinate_correct_frozen_with_backend;
use gkr_eval_isa::bwd::plan::{plan_entries_fnv, BwdOccurrencePlan, PlanAction, PlanEntry};
use gkr_eval_isa::bwd::trace::{certify, BwdCompileTrace, BwdEvent, BwdServedFrom, FrozenDemand};

const BUDGET: usize = 16;

/// The two unconditional Ext-L0 retention pins.
const BIGINT: &str = "bigint_with_extended_control_layout_gkr.json";
const BLAKE2_EXT: &str = "blake2_with_extended_control_layout_gkr.json";

/// Max `Retain` candidate trials per (fixture, layer, regime). Candidates are ordered
/// smallest-serve-gap first (a short residency window is likeliest to fit the streamed
/// headroom), so a realizable retain — if one exists — is reached early. The pins are
/// asserted against the OUTCOME within this bound, so an unreachable retain on a pin
/// fails loudly rather than being masked.
const MAX_TRIALS: usize = 8;

// ── plan builders (all built FROM the frozen snapshot, never hand-derived) ─────

/// The all-`Bypass` plan over `frozen`'s domain serves, carrying `frozen`'s (fragment)
/// epoch / `stream_reductions` so `compile_distilled_fragments_planned`'s epoch +
/// `entries_fnv` guards accept it. Mirrors `fif::all_bypass_plan` /
/// `bwd_cs_engine.rs::coordinate_correct_baseline`.
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

/// `base` with the entry at `pos` flipped to `Retain` (and `entries_fnv` re-hashed).
fn with_retain_at(base: &BwdOccurrencePlan, pos: usize) -> BwdOccurrencePlan {
    let mut entries = base.entries.clone();
    entries[pos].action = PlanAction::Retain;
    BwdOccurrencePlan {
        epoch: base.epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: base.stream_reductions,
        entries,
    }
}

// ── event probes on a returned trace ───────────────────────────────────────────

fn diverged(t: &BwdCompileTrace) -> bool {
    t.events.iter().any(|e| matches!(e, BwdEvent::Diverge { .. }))
}
fn refused(t: &BwdCompileTrace, v: ExprId) -> bool {
    t.events.iter().any(|e| matches!(e, BwdEvent::Refuse { value, .. } if *value == v))
}
fn admitted(t: &BwdCompileTrace, v: ExprId) -> bool {
    t.events.iter().any(|e| matches!(e, BwdEvent::Admit { value, .. } if *value == v))
}
/// The load-bearing non-vacuity signal: the retained value was actually served FROM its
/// resident cell (the plan-mode resident-hit arm of `lower_bwd_top_atom` fired). A refused
/// or never-retained value never produces this event.
fn served_resident(t: &BwdCompileTrace, v: ExprId) -> bool {
    t.events.iter().any(
        |e| matches!(e, BwdEvent::Serve { fp, from: BwdServedFrom::Resident } if fp.value == v),
    )
}

/// The three properties every planned fragment program in this gate must satisfy:
/// (a) no `Diverge` (both regimes), (b) EXACT certificate (`counted == reported`, Ext
/// regime only — see the module doc), (c) oracle value parity over the raw canonical
/// `layer` (both regimes).
fn assert_clean_certified_and_valued(
    ctx: &str,
    c: &gkr_eval_isa::bwd::compile::BwdCompiledLayer,
    t: &BwdCompileTrace,
    d: &DistilledLayer,
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    certify_exact: bool,
) {
    assert!(!diverged(t), "[{ctx}] planned replay diverged");
    if certify_exact {
        let rep = certify(c, t).unwrap_or_else(|r| {
            panic!(
                "[{ctx}] certificate NOT exact: counted={} reported={}",
                r.counted_traffic, r.reported_traffic
            )
        });
        assert_eq!(
            rep.counted_traffic, rep.reported_traffic,
            "[{ctx}] certificate counted != reported"
        );
        assert!(
            rep.diverged.is_none(),
            "[{ctx}] certificate reports divergence at {:?}",
            rep.diverged
        );
    }
    assert_bwd_value_parity(c, d, layer);
}

/// Whether `v` is a fragment-atom LEAF (`Source` expr or a resolution atom) — the arm-2
/// (source-admit) path of `lower_bwd_top_atom`. Retaining a leaf suppresses no descendant
/// cone, so the actual serve stream stays identical to the all-`Bypass` plan and the
/// fail-closed matcher cannot EOF-diverge (a compound retention would need the
/// `compound_batch_plan` suppressed-stream machinery, out of scope here).
fn is_leaf(d: &DistilledLayer, v: ExprId) -> bool {
    d.layer.resolutions.contains_key(&v)
        || matches!(d.layer.exprs[v.0 as usize], Expr::Source(_))
}

/// Deterministic `Retain` candidates over `base`'s entries: for each DOMAIN LEAF value with
/// ≥ 2 occurrences, its smallest-gap consecutive occurrence pair, returned as `(pos)` of the
/// earlier (producer) occurrence — ordered smallest-gap first, then by value, then position.
fn retain_candidates(d: &DistilledLayer, base: &BwdOccurrencePlan) -> Vec<(ExprId, usize)> {
    let mut positions: BTreeMap<ExprId, Vec<usize>> = BTreeMap::new();
    for (i, e) in base.entries.iter().enumerate() {
        if is_leaf(d, e.fp.value) {
            positions.entry(e.fp.value).or_default().push(i);
        }
    }
    // (gap, value, producer-position) for the tightest consecutive pair of each leaf.
    let mut ranked: Vec<(usize, ExprId, usize)> = Vec::new();
    for (&v, pos_list) in &positions {
        if pos_list.len() < 2 {
            continue;
        }
        let (gap, pos) = pos_list
            .windows(2)
            .map(|w| (w[1] - w[0], w[0]))
            .min_by_key(|&(gap, pos)| (gap, pos))
            .expect("len >= 2 has a window");
        ranked.push((gap, v, pos));
    }
    ranked.sort_by_key(|&(gap, v, pos)| (gap, v.0, pos));
    ranked.into_iter().map(|(_, v, pos)| (v, pos)).collect()
}

/// Trial `Retain` candidates (bounded, smallest-gap first) until one compiles cleanly AND
/// realizes the retention (admitted + a resident serve, never refused). On success returns
/// the retained value + producer position, having asserted the three properties on the
/// Retain-carrying program. `None` iff no candidate in the bound was clean+realized.
///
/// A candidate whose planned compile returns `Err` is NOT clean — per the brief's step 4
/// ("trial candidates until one compiles cleanly") it is skipped and counted (`errs`). This
/// matters only in R0, where the fragment plan-mode admission of a Base-width leaf currently
/// hits a placement `ExtCellMisaligned` on some candidates (a real fragment-R0 finding,
/// reported); the Ext regime — where the two pins live and all leaf admissions compile —
/// never errors here.
#[allow(clippy::too_many_arguments)]
fn try_retain(
    ctx: &str,
    d: &DistilledLayer,
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    order: &[usize],
    base: &BwdOccurrencePlan,
    certify_exact: bool,
    trials: &mut usize,
    errs: &mut usize,
) -> Option<(ExprId, usize)> {
    for (v, pos) in retain_candidates(d, base).into_iter().take(MAX_TRIALS) {
        *trials += 1;
        let plan = with_retain_at(base, pos);
        let (c, t) = match compile_distilled_fragments_planned(d, BUDGET, &plan, Some(order)) {
            Ok(ct) => ct,
            Err(_) => {
                *errs += 1;
                continue; // did not compile cleanly — try the next candidate
            }
        };

        // Realized? An admitted value served from residency, with no refusal — the
        // plan-mode resident-hit + source-admit arms genuinely fired for `v`.
        if diverged(&t) || refused(&t, v) || !admitted(&t, v) || !served_resident(&t, v) {
            continue; // not realized (or refused): try the next candidate
        }

        assert_clean_certified_and_valued(
            &format!("{ctx} Retain {v:?}"),
            &c,
            &t,
            d,
            layer,
            certify_exact,
        );
        return Some((v, pos));
    }
    None
}

// ── the gate ────────────────────────────────────────────────────────────────

#[test]
fn fragment_planned_replay_and_retention_gate() {
    let mut instances = 0usize; // (fixture, layer, regime) instances exercised
    let mut clean_retains = 0usize; // instances with a clean+realized Retain
    let mut retain_trials = 0usize; // total Retain compiles attempted
    let mut retain_errs = 0usize; // trials that did not compile (R0 ExtCellMisaligned)
    let mut with_candidates = 0usize; // instances that had ≥1 leaf retain candidate
    let mut ext_clean_retains = 0usize; // Ext-regime clean+realized retains

    // Pin bookkeeping: (reached, retained) for bigint / blake2_ext L0 Ext.
    let mut bigint_pin = (false, false);
    let mut blake2_pin = (false, false);

    for &name in FIXTURES {
        for (li, layer, cross) in layers_with_bwd_roots(name) {
            for &regime in &[BwdRegime::R0, BwdRegime::Ext] {
                let d = distill(&layer, regime, &cross, None);
                if d.skipped_decoder {
                    continue; // out of v1 in both regimes (fenced upstream — expected empty)
                }
                let ctx = format!("{name} L{li} {regime:?}");
                let certify_exact = regime == BwdRegime::Ext; // certify is Ext-only (module doc)
                let is_bigint_l0_ext = name == BIGINT && li == 0 && regime == BwdRegime::Ext;
                let is_blake2_l0_ext = name == BLAKE2_EXT && li == 0 && regime == BwdRegime::Ext;
                if is_bigint_l0_ext {
                    bigint_pin.0 = true;
                }
                if is_blake2_l0_ext {
                    blake2_pin.0 = true;
                }

                // 1. Real constructed fragment order.
                let stable_domain = stable_distilled_site_domain(&d);
                let order = construct_fragment_order(&layer, &d, &stable_domain);

                // 2. Coordinate-correct fragment freeze (NEVER a raw traced freeze).
                let frozen0 = coordinate_correct_frozen_with_backend(
                    &d,
                    BUDGET,
                    &FragmentBackend { order: order.clone() },
                )
                .unwrap_or_else(|e| panic!("[{ctx}] coordinate_correct_frozen (fragment): {e:?}"));

                // 3. All-Bypass planned replay: no diverge, exact certificate, oracle parity.
                let bypass_plan = all_bypass_plan(&frozen0);
                let (c0, t0) =
                    compile_distilled_fragments_planned(&d, BUDGET, &bypass_plan, Some(&order))
                        .unwrap_or_else(|e| panic!("[{ctx}] all-Bypass planned compile: {e:?}"));
                assert_clean_certified_and_valued(
                    &format!("{ctx} all-Bypass"),
                    &c0,
                    &t0,
                    &d,
                    &layer,
                    certify_exact,
                );

                // 4. Retain non-vacuity.
                if !retain_candidates(&d, &bypass_plan).is_empty() {
                    with_candidates += 1;
                }
                let retained = try_retain(
                    &ctx,
                    &d,
                    &layer,
                    &order,
                    &bypass_plan,
                    certify_exact,
                    &mut retain_trials,
                    &mut retain_errs,
                );
                if let Some((v, pos)) = retained {
                    clean_retains += 1;
                    if regime == BwdRegime::Ext {
                        ext_clean_retains += 1;
                    }
                    if is_bigint_l0_ext {
                        bigint_pin.1 = true;
                        eprintln!("PIN bigint L0 Ext: retained {v:?} @entry {pos}");
                    }
                    if is_blake2_l0_ext {
                        blake2_pin.1 = true;
                        eprintln!("PIN blake2_ext L0 Ext: retained {v:?} @entry {pos}");
                    }
                }

                instances += 1;
            }
        }
    }

    println!(
        "fragment_planned_replay_and_retention_gate: {instances} layer instances \
         (all-Bypass planned: no-diverge + Ext-exact-cert + oracle-parity); \
         {with_candidates} had leaf retain candidates; {clean_retains} realized a clean \
         Retain ({ext_clean_retains} in Ext) over {retain_trials} trials ({retain_errs} \
         R0 compile-errs skipped)"
    );
    println!(
        "pins — bigint L0 Ext: reached={} retained={}; blake2_ext L0 Ext: reached={} retained={}",
        bigint_pin.0, bigint_pin.1, blake2_pin.0, blake2_pin.1
    );

    assert!(instances > 0, "no layer instances exercised — enumeration broke");
    assert!(
        ext_clean_retains > 0,
        "no Ext layer realized a clean Retain anywhere — the plan-mode resident-hit / \
         source-admit arms were never exercised (fragment retention is vacuous)"
    );

    // The unconditional pins: silent skip-all is the failure this gate exists to catch.
    assert!(bigint_pin.0, "bigint L0 Ext was never reached — the pin cannot be vacuously green");
    assert!(
        bigint_pin.1,
        "PIN FAILED: bigint L0 Ext could not realize any Retain within {MAX_TRIALS} trials"
    );
    assert!(
        blake2_pin.0,
        "blake2_ext L0 Ext was never reached — the pin cannot be vacuously green"
    );
    assert!(
        blake2_pin.1,
        "PIN FAILED: blake2_ext L0 Ext could not realize any Retain within {MAX_TRIALS} trials"
    );
}
