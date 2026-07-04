//! G-diff-b (spec §5): legacy (flatten-on, no simplify) vs simplified pipeline,
//! per-root positional eval equality on the 11-fixture corpus, plus shrink metrics
//! (reachable-node count + `dag_traffic_floor`) that Task 7's brief asks RR to see
//! the effect size of.
//!
//! Cache-priority-site-count metric: SKIPPED here (deviation from the brief) —
//! `enumerate_cache_priority_sites` lives in `tests/s3_planner/metaheuristic.rs` and
//! is wired into `s3_gap_experiment.rs`'s own module tree; duplicating that wiring
//! into this file for a single extra metric was judged not worth the coupling. If
//! wanted, add it to `s3_gap_experiment.rs` instead (brief explicitly allows this).
mod common;
// `s3_gap` as a whole (as included by `s3_gap_experiment.rs`) pulls in sibling
// submodules (`cluster`/`instance`/`pack`/`driver`/`report`) whose `#[cfg(test)]`
// blocks reference `crate::load_layer_source`, a helper defined in
// `s3_gap_experiment.rs` itself — not available in this binary's crate root. Only
// `floor.rs` is self-contained (deps are `cs`/`gkr_eval_isa` only), so include just
// that module rather than the full `s3_gap` tree.
#[path = "s3_gap/floor.rs"]
mod floor;

use common::{load_fixture, resolvers, sample_rows, SyntheticResolvers};

use std::collections::HashSet;

use cs::gkr_compiler::dag_ir::{
    eval_layer_root, lower_dag, lower_dag_legacy, validate, validate_simplified, DagLayer, Expr,
    RootId, SourceKind,
};

use floor::dag_traffic_floor;
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;

const CORPUS: &[&str] = &[
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

/// Root-reachable expr-node count: a local worklist copy of the traversal
/// `cs::gkr_compiler::dag_ir::simplify::fan_out` uses (root exprs + Add/Mul
/// children + `LookupValue.query` edges), without requiring `cs` to export a
/// crate-private counter for test-only consumption.
fn reachable_count(layer: &DagLayer) -> usize {
    let mut seen: HashSet<u32> = HashSet::new();
    let mut worklist: Vec<u32> = Vec::new();
    for root in &layer.roots {
        if seen.insert(root.expr.0) {
            worklist.push(root.expr.0);
        }
    }
    while let Some(id) = worklist.pop() {
        match &layer.exprs[id as usize] {
            Expr::Add(children) | Expr::Mul(children) => {
                for &c in children {
                    if seen.insert(c.0) {
                        worklist.push(c.0);
                    }
                }
            }
            Expr::Source(sid) => {
                if let SourceKind::LookupValue { query, .. } = &layer.sources[sid.0 as usize].kind
                {
                    if seen.insert(query.0) {
                        worklist.push(query.0);
                    }
                }
            }
        }
    }
    seen.len()
}

#[test]
fn simplified_eval_matches_legacy_on_corpus() {
    let sr = SyntheticResolvers;
    let mut checks = 0usize;
    for name in CORPUS {
        let artifact = load_fixture(name);
        let legacy = lower_dag_legacy(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag_legacy: {e}"));
        let simplified =
            lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        validate(&simplified).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
        validate_simplified(&simplified)
            .unwrap_or_else(|e| panic!("[{name}] validate_simplified: {e}"));
        assert_eq!(
            legacy.layers.len(),
            simplified.layers.len(),
            "{name} layer count"
        );
        for (li, (ll, sl)) in legacy.layers.iter().zip(&simplified.layers).enumerate() {
            assert_eq!(ll.roots.len(), sl.roots.len(), "{name} L{li} root count");
            let rows = if std::env::var("G2_ALL_ROWS").as_deref() == Ok("1") {
                (0..legacy.globals.trace_len).collect::<Vec<_>>()
            } else {
                sample_rows(legacy.globals.trace_len)
            };
            for &row in &rows {
                for ri in 0..ll.roots.len() {
                    let rid = RootId(ri as u32);
                    let a = eval_layer_root(ll, rid, row, &resolvers(&sr));
                    let b = eval_layer_root(sl, rid, row, &resolvers(&sr));
                    assert_eq!(a, b, "{name} L{li} root {ri} row {row}");
                    checks += 1;
                }
            }
        }
    }
    assert!(checks > 0, "vacuous");
}

#[test]
fn simplify_shrink_metrics_and_floor_non_increase() {
    let mut any_shrink = false;
    for name in CORPUS {
        let artifact = load_fixture(name);
        let legacy = lower_dag_legacy(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag_legacy: {e}"));
        let simplified =
            lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));

        let cross_l = build_cross_layer_field_map(&legacy);
        let cross_s = build_cross_layer_field_map(&simplified);

        let mut total_nodes_l = 0usize;
        let mut total_nodes_s = 0usize;
        let mut total_floor_l = 0usize;
        let mut total_floor_s = 0usize;

        assert_eq!(legacy.layers.len(), simplified.layers.len(), "{name} layer count");
        for (li, (ll, sl)) in legacy.layers.iter().zip(&simplified.layers).enumerate() {
            let nodes_l = reachable_count(ll);
            let nodes_s = reachable_count(sl);
            let floor_l = dag_traffic_floor(ll, &cross_l);
            let floor_s = dag_traffic_floor(sl, &cross_s);

            eprintln!(
                "[shrink] {name} L{li}: nodes {nodes_l} -> {nodes_s} ({}), floor {floor_l} -> {floor_s} ({})",
                nodes_s as i64 - nodes_l as i64,
                floor_s as i64 - floor_l as i64,
            );

            // `floor` (DAG-intrinsic read traffic) is the load-bearing invariant this
            // gate enforces hard: `simplify_circuit`'s rewrites are value-preserving
            // (Step 1 proves it) and must never WIDEN the read cone.
            assert!(
                floor_s <= floor_l,
                "{name} L{li}: simplified floor {floor_s} > legacy {floor_l}"
            );
            // Reachable-node count is a SOFT signal, not a hard invariant: it is
            // observed (see task-7 report, "node-count non-monotonicity" deviation)
            // that `lower_dag`'s unflatten+re-CSE-to-fixpoint occasionally lands a
            // few MORE nodes than `lower_dag_legacy`'s build-time flatten on a
            // single L0 layer per fixture (max +254 nodes, bigint), even though the
            // rewrite is value-preserving and never widens the traffic floor. Log
            // it loudly instead of hard-failing the gate on a non-safety metric.
            if nodes_s > nodes_l {
                eprintln!(
                    "[shrink] NODE-COUNT REGRESSION (non-fatal) {name} L{li}: nodes_s {nodes_s} > nodes_l {nodes_l}"
                );
            }
            if nodes_s < nodes_l || floor_s < floor_l {
                any_shrink = true;
            }

            total_nodes_l += nodes_l;
            total_nodes_s += nodes_s;
            total_floor_l += floor_l;
            total_floor_s += floor_s;
        }

        eprintln!(
            "[shrink] {name} TOTAL: nodes {total_nodes_l} -> {total_nodes_s} ({}), floor {total_floor_l} -> {total_floor_s} ({})",
            total_nodes_s as i64 - total_nodes_l as i64,
            total_floor_s as i64 - total_floor_l as i64,
        );
    }
    if !any_shrink {
        eprintln!("[shrink] WARNING: no fixture/layer showed a strict shrink in nodes or floor");
    }
}
