//! Fragment planned-replay and finite Retain-corpus gate at b16.
//!
//! For every backward layer of every fixture in both R0 and Ext, this gate uses the
//! constructed fragment order and its coordinate-correct all-`Bypass` freeze. It first
//! checks that both the incumbent fragment compiler and the shared replay path accept
//! the all-`Bypass` schedule with identical values and no shared-path traffic regression.
//!
//! The Retain corpus then ranks every consecutive opening by
//! `(serve gap, ExprId, opening position)` and selects the first eight leaf openings and
//! first eight compound openings independently in each layer/regime instance. Every
//! selected plan contains exactly one `Retain`. A compound resident hit suppresses only
//! the closing occurrence's descendant cone, computed by the local consumer-stack rule.
//! There is no first-success exit: every selected candidate is attempted.
//!
//! Every clean incumbent acceptance is a hard obligation for the shared replay path.
//! The gate checks exact action realization, oracle value parity, the incumbent traffic
//! ceiling, encode/decode round trips, and the b16 lane bound. Ext certificates are exact; R0
//! additionally pins the incumbent's known `ExtCellMisaligned` rejection class. All
//! other rejections, divergences, refusals, or unrealized Retains fail directly or via
//! the pinned category counts.
//!
//! The complete category and acceptance census is pinned below, as are successful
//! `bigint` L0 Ext and `blake2_with_extended_control` L0 Ext Retains, preventing a
//! vacuous skip-all corpus from passing.

mod common;

use std::collections::BTreeMap;

use common::{FIXTURES, assert_bwd_value_parity, layers_with_bwd_roots};
use cs::gkr_compiler::dag_ir::{BwdRegime, Expr, ExprId};
use gkr_eval_isa::bwd::compile::{
    BwdCompiledLayer, FragmentBackend, compile_distilled_fragments_planned,
};
use gkr_eval_isa::bwd::construct::construct_fragment_order;
use gkr_eval_isa::bwd::distill::{DistilledLayer, distill, stable_distilled_site_domain};
use gkr_eval_isa::bwd::fif::coordinate_correct_frozen_with_backend;
use gkr_eval_isa::bwd::plan::{BwdOccurrencePlan, PlanAction, PlanEntry, plan_entries_fnv};
use gkr_eval_isa::bwd::trace::{BwdCompileTrace, BwdEvent, BwdServedFrom, FrozenDemand, certify};
use gkr_eval_isa::eval_plan::{CompiledBackwardEvaluation, compile_backward_fragments_replayed};
use gkr_eval_isa::fwd::encode::{decode, encode};
use gkr_eval_isa::fwd::error::CompileError;

const BUDGET: usize = 16;

/// The two unconditional Ext-L0 retention pins.
const BIGINT: &str = "bigint_with_extended_control_layout_gkr.json";
const BLAKE2_EXT: &str = "blake2_with_extended_control_layout_gkr.json";
const INITS: &str = "inits_and_teardowns_preprocessed_layout_gkr.json";

/// Finite deterministic corpus bound per `(fixture, layer, regime, category)`.
/// Every eligible consecutive opening is ranked by `(gap, ExprId, opening
/// position)`; the first eight leaf and first eight compound openings are
/// included independently for each layer/regime instance.
const MAX_TRIALS: usize = 8;
const EXPECTED_RETAIN_CANDIDATES: usize = 832;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CandidateKind {
    Leaf,
    Compound,
}

#[derive(Clone, Copy, Debug)]
struct RetainCandidate {
    value: ExprId,
    opening: usize,
    closing: usize,
    kind: CandidateKind,
}

#[derive(Default, Debug, PartialEq, Eq)]
struct RegimeCorpus {
    bypass_schedules: usize,
    leaf_instances: usize,
    compound_instances: usize,
    leaf_candidates: usize,
    compound_candidates: usize,
    compound_suppressed: usize,
    leaf_incumbent_accepted: usize,
    compound_incumbent_accepted: usize,
    leaf_shared_realized: usize,
    compound_shared_realized: usize,
    incumbent_compile_r0: usize,
    incumbent_diverged: usize,
    incumbent_refused_or_infeasible: usize,
}

impl RegimeCorpus {
    fn retain_candidates(&self) -> usize {
        self.leaf_candidates + self.compound_candidates
    }

    fn scheduled(&self) -> usize {
        self.bypass_schedules + self.retain_candidates()
    }

    fn incumbent_accepted(&self) -> usize {
        self.bypass_schedules + self.leaf_incumbent_accepted + self.compound_incumbent_accepted
    }

    fn shared_realized_retains(&self) -> usize {
        self.leaf_shared_realized + self.compound_shared_realized
    }
}

// ── plan builders (all built FROM the frozen snapshot, never hand-derived) ─────

/// The all-`Bypass` plan over `frozen`'s domain serves, carrying `frozen`'s (fragment)
/// epoch / `stream_reductions` so `compile_distilled_fragments_planned`'s epoch +
/// `entries_fnv` guards accept it. Mirrors `fif::all_bypass_plan` /
/// `bwd_cs_engine.rs::coordinate_correct_baseline`.
fn all_bypass_plan(frozen: &FrozenDemand) -> BwdOccurrencePlan {
    let entries: Vec<PlanEntry> = frozen
        .domain_serves
        .iter()
        .map(|&(fp, _from)| PlanEntry {
            fp,
            action: PlanAction::Bypass,
        })
        .collect();
    BwdOccurrencePlan {
        epoch: frozen.epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: frozen.stream_reductions,
        entries,
    }
}

// ── event probes on a returned trace ───────────────────────────────────────────

fn diverged(t: &BwdCompileTrace) -> bool {
    t.events
        .iter()
        .any(|e| matches!(e, BwdEvent::Diverge { .. }))
}
fn refused(t: &BwdCompileTrace, v: ExprId) -> bool {
    t.events
        .iter()
        .any(|e| matches!(e, BwdEvent::Refuse { value, .. } if *value == v))
}
fn admitted(t: &BwdCompileTrace, v: ExprId) -> bool {
    t.events
        .iter()
        .any(|e| matches!(e, BwdEvent::Admit { value, .. } if *value == v))
}
/// The load-bearing non-vacuity signal: the retained value was actually served FROM its
/// resident cell (the plan-mode resident-hit arm of `lower_bwd_top_atom` fired). A refused
/// or never-retained value never produces this event.
fn served_resident(t: &BwdCompileTrace, v: ExprId) -> bool {
    t.events.iter().any(
        |e| matches!(e, BwdEvent::Serve { fp, from: BwdServedFrom::Resident } if fp.value == v),
    )
}

fn backward_dram(compiled: &BwdCompiledLayer) -> usize {
    compiled.stats_ext.global + compiled.stats_ext.fold_traffic
}

fn assert_shared_replay(
    ctx: &str,
    old: &BwdCompiledLayer,
    new: &CompiledBackwardEvaluation,
    d: &DistilledLayer,
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
) {
    assert_eq!(decode(&new.encoded).unwrap(), new.compiled.program, "{ctx}");
    assert_bwd_value_parity(&new.compiled, d, layer);
    assert!(
        backward_dram(&new.compiled) <= backward_dram(old),
        "{ctx}: shared replay DRAM traffic regressed"
    );
    assert!(!diverged(&new.trace), "{ctx}: shared replay diverged");
    eprintln!(
        "{ctx}: instructions incumbent={} shared={} encoded_lanes incumbent={} shared={}",
        old.program.instrs.len(),
        new.compiled.program.instrs.len(),
        encode(&old.program).unwrap().len(),
        new.encoded.len(),
    );
}

fn assert_retains_realized(ctx: &str, plan: &BwdOccurrencePlan, trace: &BwdCompileTrace) {
    let mut cursor = 0usize;
    let serve_positions = plan
        .entries
        .iter()
        .map(|entry| {
            let relative = trace.events[cursor..]
                .iter()
                .position(|event| matches!(event, BwdEvent::Serve { fp, .. } if *fp == entry.fp))
                .unwrap_or_else(|| {
                    panic!("[{ctx}] no realized Serve for ordered plan entry {entry:?}")
                });
            let position = cursor + relative;
            cursor = position + 1;
            position
        })
        .collect::<Vec<_>>();

    for (entry_index, entry) in plan.entries.iter().enumerate() {
        if entry.action != PlanAction::Retain {
            continue;
        }
        let close_index = plan.entries[entry_index + 1..]
            .iter()
            .position(|later| later.fp.value == entry.fp.value)
            .map(|relative| entry_index + 1 + relative)
            .expect("an accepted Retain has a later occurrence");
        let opening = serve_positions[entry_index];
        let closing = serve_positions[close_index];
        let opening_from = match trace.events[opening] {
            BwdEvent::Serve { from, .. } => from,
            _ => unreachable!(),
        };
        assert!(
            matches!(
                trace.events[closing],
                BwdEvent::Serve {
                    fp,
                    from: BwdServedFrom::Resident,
                } if fp.value == entry.fp.value
            ),
            "[{ctx}] Retain at entry {entry_index} did not produce a later resident Serve"
        );
        assert!(
            !trace.events[opening..=closing].iter().any(
                |event| matches!(event, BwdEvent::Refuse { value, .. } if *value == entry.fp.value)
            ),
            "[{ctx}] Retain at entry {entry_index} was refused"
        );
        if opening_from == BwdServedFrom::Recomputed {
            assert!(
                trace.events[opening + 1..closing].iter().any(
                    |event| matches!(event, BwdEvent::Admit { value, .. } if *value == entry.fp.value)
                ),
                "[{ctx}] miss-side Retain at entry {entry_index} did not admit before its hit"
            );
        }
    }
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

/// Whether `v` is a fragment-atom leaf (`Source` expr or a resolution atom).
fn is_leaf(d: &DistilledLayer, v: ExprId) -> bool {
    d.layer.resolutions.contains_key(&v) || matches!(d.layer.exprs[v.0 as usize], Expr::Source(_))
}

/// Every eligible single-`Retain` opening, ordered deterministically. The finite
/// corpus applies its bound independently to the leaf and compound subsequences.
fn retain_candidates(d: &DistilledLayer, base: &BwdOccurrencePlan) -> Vec<RetainCandidate> {
    let mut positions: BTreeMap<ExprId, Vec<usize>> = BTreeMap::new();
    for (i, e) in base.entries.iter().enumerate() {
        positions.entry(e.fp.value).or_default().push(i);
    }
    let mut ranked = Vec::new();
    for (&v, pos_list) in &positions {
        let kind = if is_leaf(d, v) {
            CandidateKind::Leaf
        } else {
            CandidateKind::Compound
        };
        ranked.extend(pos_list.windows(2).map(|window| {
            let opening = window[0];
            let closing = window[1];
            (
                closing - opening,
                v.0,
                opening,
                RetainCandidate {
                    value: v,
                    opening,
                    closing,
                    kind,
                },
            )
        }));
    }
    ranked.sort_by_key(|&(gap, value, opening, _)| (gap, value, opening));
    ranked
        .into_iter()
        .map(|(_, _, _, candidate)| candidate)
        .collect()
}

/// Per-serve exclusive subtree ends over the frozen domain stream. A compound
/// hit at `closing` removes exactly `(closing + 1)..end[closing]`; leaf ranges
/// are empty. This is the same consumer-stack rule used by the incumbent's
/// compound plan construction, specialized here to one chosen gap.
fn subtree_ends(base: &BwdOccurrencePlan) -> Vec<usize> {
    let mut end = vec![base.entries.len(); base.entries.len()];
    let mut stack = Vec::<(ExprId, usize)>::new();
    for (index, entry) in base.entries.iter().enumerate() {
        while let Some(&(value, opening)) = stack.last() {
            if Some(value) == entry.fp.consumer {
                break;
            }
            end[opening] = index;
            stack.pop();
        }
        stack.push((entry.fp.value, index));
    }
    for (_, opening) in stack {
        end[opening] = base.entries.len();
    }
    end
}

fn single_retain_plan(base: &BwdOccurrencePlan, candidate: RetainCandidate) -> BwdOccurrencePlan {
    assert_eq!(base.entries[candidate.opening].fp.value, candidate.value);
    assert_eq!(base.entries[candidate.closing].fp.value, candidate.value);
    let end = subtree_ends(base);
    let suppressed = (candidate.closing + 1)..end[candidate.closing];
    let entries = base
        .entries
        .iter()
        .enumerate()
        .filter(|(index, _)| !suppressed.contains(index))
        .map(|(index, entry)| PlanEntry {
            fp: entry.fp,
            action: if index == candidate.opening {
                PlanAction::Retain
            } else {
                PlanAction::Bypass
            },
        })
        .collect::<Vec<_>>();
    assert_eq!(
        entries
            .iter()
            .filter(|entry| entry.action == PlanAction::Retain)
            .count(),
        1
    );
    BwdOccurrencePlan {
        epoch: base.epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: base.stream_reductions,
        entries,
    }
}

/// Exercise every incumbent-accepted plan in the pinned candidate set. The
/// first accepted candidate is retained only for the two historical
/// non-vacuity pins; it never terminates iteration.
#[allow(clippy::too_many_arguments)]
fn exercise_retain_corpus(
    ctx: &str,
    d: &DistilledLayer,
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    order: &[usize],
    base: &BwdOccurrencePlan,
    certify_exact: bool,
    corpus: &mut RegimeCorpus,
) -> Option<(ExprId, usize)> {
    let candidates = retain_candidates(d, base);
    let mut first_accepted = None;
    for kind in [CandidateKind::Leaf, CandidateKind::Compound] {
        let selected = candidates
            .iter()
            .copied()
            .filter(|candidate| candidate.kind == kind)
            .take(MAX_TRIALS)
            .collect::<Vec<_>>();
        match kind {
            CandidateKind::Leaf => {
                corpus.leaf_candidates += selected.len();
                corpus.leaf_instances += usize::from(!selected.is_empty());
            }
            CandidateKind::Compound => {
                corpus.compound_candidates += selected.len();
                corpus.compound_instances += usize::from(!selected.is_empty());
            }
        }
        for candidate in selected {
            let v = candidate.value;
            let plan = single_retain_plan(base, candidate);
            if kind == CandidateKind::Compound && plan.entries.len() < base.entries.len() {
                corpus.compound_suppressed += 1;
            }
            let (c, t) = match compile_distilled_fragments_planned(d, BUDGET, &plan, Some(order)) {
                Ok(ct) => ct,
                Err(CompileError::ExtCellMisaligned(_)) => {
                    assert_eq!(
                        d.regime,
                        BwdRegime::R0,
                        "only R0 may retain the known ExtCellMisaligned classification"
                    );
                    corpus.incumbent_compile_r0 += 1;
                    continue;
                }
                Err(error) => panic!("[{ctx}] unexpected incumbent candidate rejection: {error:?}"),
            };

            if diverged(&t) {
                corpus.incumbent_diverged += 1;
                continue;
            }
            if refused(&t, v) {
                corpus.incumbent_refused_or_infeasible += 1;
                continue;
            }
            if !admitted(&t, v) || !served_resident(&t, v) {
                corpus.incumbent_refused_or_infeasible += 1;
                continue;
            }

            match kind {
                CandidateKind::Leaf => corpus.leaf_incumbent_accepted += 1,
                CandidateKind::Compound => corpus.compound_incumbent_accepted += 1,
            }

            assert_clean_certified_and_valued(
                &format!("{ctx} {kind:?} Retain {v:?} @{}", candidate.opening),
                &c,
                &t,
                d,
                layer,
                certify_exact,
            );
            let new = compile_backward_fragments_replayed(d, &plan, Some(order), 4).unwrap_or_else(
                |error| {
                    panic!(
                        "[{ctx}] shared rejected incumbent-accepted {kind:?} Retain {v:?} \
                     @{}: {error:?}",
                        candidate.opening
                    )
                },
            );
            let candidate_ctx = format!("{ctx} {kind:?} Retain {v:?} @{}", candidate.opening);
            assert_shared_replay(&candidate_ctx, &c, &new, d, layer);
            assert_retains_realized(&candidate_ctx, &plan, &new.trace);
            match kind {
                CandidateKind::Leaf => corpus.leaf_shared_realized += 1,
                CandidateKind::Compound => corpus.compound_shared_realized += 1,
            }
            first_accepted.get_or_insert((v, candidate.opening));
        }
    }
    first_accepted
}

// ── the gate ────────────────────────────────────────────────────────────────

#[test]
fn retained_leaf_mixed_eliminated_product_fits_b16() {
    let (_, layer, cross) = layers_with_bwd_roots(INITS)
        .find(|(layer_index, _, _)| *layer_index == 0)
        .expect("the pinned fixture has backward layer 0");
    let d = distill(&layer, BwdRegime::Ext, &cross, None);
    let stable_domain = stable_distilled_site_domain(&d);
    let order = construct_fragment_order(&layer, &d, &stable_domain);
    let frozen = coordinate_correct_frozen_with_backend(
        &d,
        BUDGET,
        &FragmentBackend {
            order: order.clone(),
        },
    )
    .unwrap();
    let bypass = all_bypass_plan(&frozen);
    let candidate = RetainCandidate {
        value: ExprId(5),
        opening: 2,
        closing: 3,
        kind: CandidateKind::Leaf,
    };
    let plan = single_retain_plan(&bypass, candidate);
    let ctx = "inits L0 Ext mixed eliminated product";

    let (old, old_trace) =
        compile_distilled_fragments_planned(&d, BUDGET, &plan, Some(&order)).unwrap();
    assert_clean_certified_and_valued(ctx, &old, &old_trace, &d, &layer, true);
    assert!(admitted(&old_trace, candidate.value));
    assert!(served_resident(&old_trace, candidate.value));

    let new = compile_backward_fragments_replayed(&d, &plan, Some(&order), 4)
        .unwrap_or_else(|error| panic!("[{ctx}] shared replay: {error:?}"));
    assert_shared_replay(ctx, &old, &new, &d, &layer);
    assert_retains_realized(ctx, &plan, &new.trace);
    assert!(
        new.symbolic.plan.stats.peak_live_lanes <= BUDGET,
        "[{ctx}] mixed product lowering exceeded b16: {}",
        new.symbolic.plan.stats.peak_live_lanes
    );
}

#[test]
fn fragment_planned_replay_and_retention_gate() {
    let mut instances = 0usize; // (fixture, layer, regime) instances exercised
    let mut r0_corpus = RegimeCorpus::default();
    let mut ext_corpus = RegimeCorpus::default();

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
                let corpus = match regime {
                    BwdRegime::R0 => &mut r0_corpus,
                    BwdRegime::Ext => &mut ext_corpus,
                };
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
                    &FragmentBackend {
                        order: order.clone(),
                    },
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
                let new0 = compile_backward_fragments_replayed(&d, &bypass_plan, Some(&order), 4)
                    .unwrap_or_else(|error| panic!("[{ctx}] shared all-Bypass replay: {error:?}"));
                assert_shared_replay(&format!("{ctx} all-Bypass"), &c0, &new0, &d, &layer);
                corpus.bypass_schedules += 1;

                // 4. Every incumbent-accepted plan in the finite pinned
                // leaf+compound candidate corpus must replay through the shared path.
                let first_retained = exercise_retain_corpus(
                    &ctx,
                    &d,
                    &layer,
                    &order,
                    &bypass_plan,
                    certify_exact,
                    corpus,
                );
                if let Some((v, pos)) = first_retained {
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

    for (regime, corpus) in [("R0", &r0_corpus), ("Ext", &ext_corpus)] {
        println!(
            "fragment replay corpus {regime}: scheduled={} bypass={} retain_candidates={} \
             incumbent_accepted={} shared_realized_retains={} compile_rejected={} \
             diverged={} refused/infeasible={}; leaf instances={} candidates={} \
             accepted={} realized={}; compound instances={} candidates={} suppressing={} \
             accepted={} realized={}",
            corpus.scheduled(),
            corpus.bypass_schedules,
            corpus.retain_candidates(),
            corpus.incumbent_accepted(),
            corpus.shared_realized_retains(),
            corpus.incumbent_compile_r0,
            corpus.incumbent_diverged,
            corpus.incumbent_refused_or_infeasible,
            corpus.leaf_instances,
            corpus.leaf_candidates,
            corpus.leaf_incumbent_accepted,
            corpus.leaf_shared_realized,
            corpus.compound_instances,
            corpus.compound_candidates,
            corpus.compound_suppressed,
            corpus.compound_incumbent_accepted,
            corpus.compound_shared_realized,
        );
    }
    println!(
        "fragment replay corpus total: instances={instances} scheduled={} \
         retain_candidates={} incumbent_accepted={} shared_realized_retains={} \
         compile_rejected={}",
        r0_corpus.scheduled() + ext_corpus.scheduled(),
        r0_corpus.retain_candidates() + ext_corpus.retain_candidates(),
        r0_corpus.incumbent_accepted() + ext_corpus.incumbent_accepted(),
        r0_corpus.shared_realized_retains() + ext_corpus.shared_realized_retains(),
        r0_corpus.incumbent_compile_r0 + ext_corpus.incumbent_compile_r0,
    );
    println!(
        "pins — bigint L0 Ext: reached={} retained={}; blake2_ext L0 Ext: reached={} retained={}",
        bigint_pin.0, bigint_pin.1, blake2_pin.0, blake2_pin.1
    );

    assert_eq!(instances, 114, "the pinned layer/regime census changed");
    assert_eq!(
        r0_corpus,
        RegimeCorpus {
            bypass_schedules: 57,
            leaf_instances: 53,
            compound_instances: 24,
            leaf_candidates: 347,
            compound_candidates: 65,
            compound_suppressed: 15,
            leaf_incumbent_accepted: 282,
            compound_incumbent_accepted: 65,
            leaf_shared_realized: 282,
            compound_shared_realized: 65,
            incumbent_compile_r0: 65,
            incumbent_diverged: 0,
            incumbent_refused_or_infeasible: 0,
        },
        "the pinned R0 replay corpus changed"
    );
    assert_eq!(
        ext_corpus,
        RegimeCorpus {
            bypass_schedules: 57,
            leaf_instances: 54,
            compound_instances: 24,
            leaf_candidates: 355,
            compound_candidates: 65,
            compound_suppressed: 15,
            leaf_incumbent_accepted: 355,
            compound_incumbent_accepted: 65,
            leaf_shared_realized: 355,
            compound_shared_realized: 65,
            incumbent_compile_r0: 0,
            incumbent_diverged: 0,
            incumbent_refused_or_infeasible: 0,
        },
        "the pinned Ext replay corpus changed"
    );
    assert_eq!(
        r0_corpus.retain_candidates() + ext_corpus.retain_candidates(),
        EXPECTED_RETAIN_CANDIDATES,
        "the finite Retain candidate corpus silently changed"
    );
    assert_eq!(
        r0_corpus.scheduled() + ext_corpus.scheduled(),
        946,
        "the all-Bypass plus bounded Retain schedule corpus silently changed"
    );
    assert_eq!(
        r0_corpus.incumbent_accepted() + ext_corpus.incumbent_accepted(),
        881,
        "the incumbent-accepted schedule corpus silently changed"
    );

    // The unconditional pins: silent skip-all is the failure this gate exists to catch.
    assert!(
        bigint_pin.0,
        "bigint L0 Ext was never reached — the pin cannot be vacuously green"
    );
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
