//! CS-M5a Task 2: FragmentTable stable-view invariance gate.
//!
//! Distilled `ExprId`s are relation-unit-ORDER dependent, so a permuted distill
//! numbers the same values differently and raw `FragmentTable`s from two runs
//! cannot be compared. `FragmentTable::stable_view` / `stable_c_init` project
//! every fragment atom + coefficient factor to an order-independent
//! `StableBwdExprKey` / `FactorKey`, which MUST be invariant under any unit
//! permutation. This gate distills every fixture × bwd layer × Ext regime in the
//! canonical order and under the REVERSED unit permutation and asserts:
//!   (a) `stable_view` fragment tuples are equal as MULTISETS,
//!   (b) `stable_c_init` term lists are equal as MULTISETS,
//!   (c) two canonical distills yield byte-identical stable views (determinism).

mod common;

use std::collections::HashMap;

use common::{layers_with_bwd_roots, load_layer, FIXTURES};
use cs::gkr_compiler::dag_ir::BwdRegime;
use gkr_eval_isa::bwd::compile::compile_distilled_fragments;
use gkr_eval_isa::bwd::construct::construct_fragment_order;
use gkr_eval_isa::bwd::distill::{distill, stable_distilled_site_domain};
use gkr_eval_isa::bwd::fragment::FactorKey;

/// Multiset (count map) of a slice — the canonical order-independent comparison.
fn multiset<T: std::hash::Hash + Eq + Clone>(v: &[T]) -> HashMap<T, usize> {
    let mut m: HashMap<T, usize> = HashMap::new();
    for x in v {
        *m.entry(x.clone()).or_insert(0) += 1;
    }
    m
}

#[test]
fn fragment_stable_views_are_unit_permutation_invariant() {
    let mut layers_checked = 0usize;
    let mut permuted_layers = 0usize;

    for &name in FIXTURES {
        for (li, layer, cross) in layers_with_bwd_roots(name) {
            let d = distill(&layer, BwdRegime::Ext, &cross, None);
            let n_units = d.unit_order.len();
            let ctx = format!("{name} L{li} Ext");

            // (c) Canonical determinism: a second identical distill is byte-equal
            // (no sort — the same call must reproduce the same order).
            let d2 = distill(&layer, BwdRegime::Ext, &cross, None);
            assert_eq!(
                d.fragments.stable_view(&d),
                d2.fragments.stable_view(&d2),
                "[{ctx}] two canonical distills must yield identical stable views"
            );
            assert_eq!(
                d.fragments.stable_c_init(&d),
                d2.fragments.stable_c_init(&d2),
                "[{ctx}] two canonical distills must yield identical stable c_init"
            );

            // The reversed unit permutation renumbers distilled ExprIds while
            // staying value-identical (every root keeps its beta exponent).
            let rev: Vec<usize> = (0..n_units).rev().collect();
            let dp = distill(&layer, BwdRegime::Ext, &cross, Some(&rev));

            // (a) stable_view invariant as a multiset (order differs across runs).
            let view = d.fragments.stable_view(&d);
            let view_p = dp.fragments.stable_view(&dp);
            assert_eq!(
                multiset(&view),
                multiset(&view_p),
                "[{ctx}] stable_view drifted under the reversed unit permutation"
            );

            // (b) stable_c_init invariant as a multiset (duplicates preserved).
            let ci = d.fragments.stable_c_init(&d);
            let ci_p = dp.fragments.stable_c_init(&dp);
            assert_eq!(
                multiset(&ci),
                multiset(&ci_p),
                "[{ctx}] stable_c_init drifted under the reversed unit permutation"
            );

            layers_checked += 1;
            if n_units >= 2 {
                permuted_layers += 1;
            }

            // Directional sanity (NOT a gate — eyeball only): L0 fragment counts.
            if li == 0 {
                println!(
                    "[{name}] L0 Ext fragments = {} (c_init terms = {})",
                    d.fragments.fragments.len(),
                    d.fragments.c_init.terms.len()
                );
            }
        }
    }

    assert!(layers_checked > 0, "no distillable layers — fixture enumeration broke");
    assert!(
        permuted_layers > 0,
        "no layer had >= 2 units — the reversed permutation never exercised a reorder"
    );
    println!(
        "fragment invariance: {layers_checked} layer instances checked, \
         {permuted_layers} with a non-trivial reversed permutation"
    );
}

/// Reviewer finding (CS-M5a T5): `lower_bwd_fragments_virtual` indexed
/// `table.fragments[frag_idx]` / `coeff_descs[frag_idx]` per schedule position with no
/// validation that `order` is a permutation of `0..n`. An in-range DUPLICATE (unlike a
/// wrong length or an out-of-range index, which already panic on the raw index) would
/// silently double-count one fragment and drop another — a wrong accumulator with no
/// panic. This gate compiles the first real fixture/layer with >= 2 fragments under an
/// `order` with position 1 duplicating position 0's fragment index, and asserts the
/// compile PANICS instead of silently corrupting the accumulator.
#[test]
fn fragment_order_duplicate_index_panics() {
    for &name in FIXTURES {
        for (_li, layer, cross) in layers_with_bwd_roots(name) {
            let d = distill(&layer, BwdRegime::Ext, &cross, None);
            if d.skipped_decoder {
                continue;
            }
            let n = d.fragments.fragments.len();
            if n < 2 {
                continue; // need >= 2 fragments to construct a genuine duplicate
            }

            let mut ord: Vec<usize> = (0..n).collect();
            ord[1] = 0; // duplicate: fragment 0 double-counted, fragment 1 dropped

            let prev_hook = std::panic::take_hook();
            std::panic::set_hook(Box::new(|_| {})); // silence expected-panic noise
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                compile_distilled_fragments(&d, 16, Some(&ord))
            }));
            std::panic::set_hook(prev_hook);

            assert!(
                result.is_err(),
                "[{name} Ext] compile_distilled_fragments must panic on a duplicate `order` \
                 index (n={n}, order={ord:?}) instead of silently corrupting the accumulator"
            );
            return; // one real instance is sufficient
        }
    }
    panic!("no fixture/layer had >= 2 fragments — could not exercise the duplicate-order panic");
}

// ── CS-M5a Task 7: fragment-granular constructive order (`construct_fragment_order`) ─

/// (7.1a) For every fixture × every bwd layer × Ext, `construct_fragment_order`
/// returns a valid PERMUTATION of `0..d.fragments.fragments.len()`: same length,
/// and the sorted order equals `0..n` (every fragment index present exactly once,
/// none out of range or repeated). The fragment index space is the value the
/// Task-5 lowering driver already validates as a permutation of `order`.
#[test]
fn fragment_order_is_permutation_all_fixtures() {
    let mut checked = 0usize;
    for &name in FIXTURES {
        for (li, layer, cross) in layers_with_bwd_roots(name) {
            let d = distill(&layer, BwdRegime::Ext, &cross, None);
            let stable_domain = stable_distilled_site_domain(&d);
            let n = d.fragments.fragments.len();

            let order = construct_fragment_order(&layer, &d, &stable_domain);

            assert_eq!(order.len(), n, "[{name} L{li} Ext] permutation length");
            let mut sorted = order.clone();
            sorted.sort_unstable();
            assert_eq!(
                sorted,
                (0..n).collect::<Vec<usize>>(),
                "[{name} L{li} Ext] order is not a permutation of 0..{n} (got {order:?})"
            );
            checked += 1;
        }
    }
    assert!(checked > 0, "no distillable bwd layer — fixture enumeration broke");
    println!("fragment_order_is_permutation_all_fixtures: {checked} layer instances held");
}

/// (7.1b) Determinism: two `construct_fragment_order` calls over the SAME distill
/// are byte-equal (no wall-clock / hashmap-iteration-order dependence).
#[test]
fn fragment_order_is_deterministic() {
    let (layer, cross) = load_layer("add_sub_lui_auipc_mop_layout_gkr.json", 0);
    let d = distill(&layer, BwdRegime::Ext, &cross, None);
    let stable_domain = stable_distilled_site_domain(&d);

    let a = construct_fragment_order(&layer, &d, &stable_domain);
    let b = construct_fragment_order(&layer, &d, &stable_domain);
    assert_eq!(a, b, "construct_fragment_order must be deterministic on the same distill");
}

/// (7.1c) Non-vacuity: on bigint L0 Ext there IS fragment-level reuse to
/// co-locate, so the constructed order MUST differ from identity. A constructor
/// that always returned `0..n` would satisfy (a)/(b) trivially — this pins that
/// the reuse structure actually MOVES fragments.
#[test]
fn fragment_order_moves_reuse() {
    let (layer, cross) = load_layer("bigint_with_extended_control_layout_gkr.json", 0);
    let d = distill(&layer, BwdRegime::Ext, &cross, None);
    let stable_domain = stable_distilled_site_domain(&d);
    let n = d.fragments.fragments.len();

    let order = construct_fragment_order(&layer, &d, &stable_domain);
    let identity: Vec<usize> = (0..n).collect();
    assert_ne!(
        order, identity,
        "bigint L0 Ext ({n} fragments) has reuse to co-locate — constructed order must not be identity"
    );
}
