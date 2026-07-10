//! Task-4 smoke test: distill every layer of the 12 pinned fixtures in both
//! backward regimes (spec §2.2).
//!
//! Per layer × regime this checks (i) `distill` completes without panicking,
//! (ii) the distilled root is VALUE-identical to the alpha-combined canonical
//! claim roots under a rewrite-aware reference evaluation (`LookupValue` leaf
//! ↦ its query expr — the backward semantics), and (iii) the pinned
//! `skipped_decoder` set, asserted exactly so coverage changes are loud.

mod common;

use std::collections::{BTreeSet, HashMap};

use common::{load_fixture, resolvers, SyntheticResolvers};
use cs::gkr_compiler::dag_ir::{
    bwd_roots, eval_layer_root, lower_dag, validate, BwdRegime, ChallengeKey, ChallengePower,
    ChallengeRef, DagLayer, Expr, ExprId, Ext, Resolvers, SourceKind,
};
use field::Field;
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;

/// The 12 pinned Global Constraints fixtures: the 11 classic with-caches
/// layouts (same list as `fwd_vm_desc_census.rs`) + the unified machine.
const FIXTURES: &[&str] = &[
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
    "unified_reduced_machine_layout_gkr.json",
];

/// The pinned decoder-bearing set: `"{fixture_stem}[L{layer}]"` for every layer
/// whose claim cone reaches a `PeekDecoder` resolution key (skipped in BOTH
/// regimes). Update deliberately when decoder coverage changes.
/// Observed 2026-07-10: exactly the machine circuits' base layers — the three
/// delegation circuits (bigint, blake2_with_extended_control, keccak_special5)
/// and blake2_g_function/inits_and_teardowns carry no reachable decoder cone.
const PINNED_SKIPPED_DECODER: &[&str] = &[
    "add_sub_lui_auipc_mop[L0]",
    "jump_branch_slt[L0]",
    "mem_subword_only[L0]",
    "mem_word_only[L0]",
    "shift_binop[L0]",
    "unified_reduced_machine[L0]",
    "unsigned_mul_div[L0]",
];

/// Rewrite-aware reference evaluation of a canonical expr: identical to
/// `eval_layer_expr` except a `LookupValue` leaf evaluates to its QUERY expr
/// (the distillation rewrite), not the lookup resolver. Memoized per row.
fn eval_rewritten(
    layer: &DagLayer,
    e: ExprId,
    row: usize,
    r: &Resolvers<'_>,
    memo: &mut HashMap<ExprId, Ext>,
) -> Ext {
    if let Some(&v) = memo.get(&e) {
        return v;
    }
    let v = match &layer.exprs[e.0 as usize] {
        Expr::Source(sid) => match &layer.sources[sid.0 as usize].kind {
            SourceKind::LookupValue { query, .. } => eval_rewritten(layer, *query, row, r, memo),
            SourceKind::Constant { .. }
            | SourceKind::Challenge { .. }
            | SourceKind::Read { .. }
            | SourceKind::VirtualSetup { .. } => {
                // Delegate single-leaf evaluation to the authoritative evaluator
                // (a leaf expr has no LookupValue beneath it to rewrite).
                cs::gkr_compiler::dag_ir::eval_layer_expr(layer, e, row, r)
            }
        },
        Expr::Add(children) => {
            let mut acc = Ext::ZERO;
            for &c in children {
                let t = eval_rewritten(layer, c, row, r, memo);
                acc.add_assign(&t);
            }
            acc
        }
        Expr::Mul(children) => {
            let mut acc = Ext::ONE;
            for &c in children {
                let t = eval_rewritten(layer, c, row, r, memo);
                acc.mul_assign(&t);
            }
            acc
        }
    };
    memo.insert(e, v);
    v
}

/// beta^i challenge value as the distilled spine resolves it (i >= 1).
fn beta_i(r: &Resolvers<'_>, i: usize) -> Ext {
    let power = if i == 1 { ChallengePower::One } else { ChallengePower::Static(i as u32) };
    r.challenge.challenge(&ChallengeRef { key: ChallengeKey::ClaimBatching, power })
}

#[test]
fn distill_all_fixtures_both_regimes() {
    let syn = SyntheticResolvers;
    let r = resolvers(&syn);
    let mut skipped: BTreeSet<String> = BTreeSet::new();
    let mut add_sub_nonempty_domain = false;

    for name in FIXTURES {
        let stem = common::schedule_stem(name);
        let artifact = load_fixture(name);
        let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));

        let cross = build_cross_layer_field_map(&dag);
        for (li, layer) in dag.layers.iter().enumerate() {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let d = gkr_eval_isa::bwd::distill::distill(layer, regime, &cross, None);
                if d.skipped_decoder {
                    skipped.insert(format!("{stem}[L{li}]"));
                }

                // Value parity: distilled root == alpha-combined rewritten
                // canonical roots (holds regardless of skipped_decoder — the
                // rebuild itself is always well-defined).
                for row in [0usize, 1] {
                    let mut memo: HashMap<ExprId, Ext> = HashMap::new();
                    let mut expected = Ext::ZERO;
                    for (i, &rid) in bwd_roots(layer).iter().enumerate() {
                        let mut t = eval_rewritten(
                            layer,
                            layer.roots[rid.0 as usize].expr,
                            row,
                            &r,
                            &mut memo,
                        );
                        if i >= 1 {
                            t.mul_assign(&beta_i(&r, i));
                        }
                        expected.add_assign(&t);
                    }
                    let got = eval_layer_root(&d.layer, d.root, row, &r);
                    assert_eq!(
                        got, expected,
                        "[{stem} L{li} {regime:?}] distilled root value mismatch at row {row}"
                    );
                }

                // The site domain over the REBUILT layer is non-empty for the
                // constraint-bearing add_sub layers (checked below).
                if *name == FIXTURES[0]
                    && regime == BwdRegime::R0
                    && !gkr_eval_isa::bwd::distill::distilled_site_domain(&d).is_empty()
                {
                    add_sub_nonempty_domain = true;
                }
            }
        }
    }

    println!("skipped_decoder set ({}):", skipped.len());
    for s in &skipped {
        println!("  {s}");
    }
    let pinned: BTreeSet<String> = PINNED_SKIPPED_DECODER.iter().map(|s| s.to_string()).collect();
    assert_eq!(
        skipped, pinned,
        "skipped_decoder set drifted from the pinned expectation — update deliberately"
    );

    assert!(
        add_sub_nonempty_domain,
        "at least one add_sub distilled layer must expose a non-empty backward site domain"
    );
}
