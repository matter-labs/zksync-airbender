//! M0 sizing DP (spec §3 decision point): five DAG-memoized quantities that
//! together answer the flattener's central sizing question for a layer's
//! roots — is the all-recompute site space small enough to address
//! literally (per-site genes), or does it require hashed genome addressing?
//!
//! # DP conventions
//!
//! `sites`, `max_depth`, `ceiling` are computed by a single bottom-up pass
//! over the sub-DAG reachable from `roots` (`compute_node_stats`, gated by
//! `mark_reachable`), memoized per `ExprId` in a plain `Vec` (not
//! `Vec<Option<_>>` + recursion): arena construction
//! (`ArenaBuilder::intern_expr`, `cs::gkr_compiler::dag_ir::arena`) only ever
//! *appends*, so an `Add`/`Mul`'s children always carry a strictly smaller
//! `ExprId` than the node itself. A single ascending scan over `0..dag_nodes`
//! therefore sees every child before its parent — the memo is complete by
//! construction, with no recursion and no stack-depth risk regardless of DAG
//! depth (`debug_assert`ed defensively per edge, in case that invariant is
//! ever broken upstream). Each node is visited exactly once no matter how
//! many parents/roots reference it — this is what makes the DP safe even
//! though the *quantity* it stands for (the all-recompute tree) would be
//! exponential to walk directly. Nodes NOT reachable from any given root
//! (e.g. a `LookupValue`'s `query` sub-expression — resolution metadata,
//! never a value-cone child) are skipped entirely: `dag_nodes` in the report
//! is still the layer's total arena size, but the DP and its debug
//! assertion only ever run over the roots' actual dependency cone.
//!
//! - `sites`: `tree_count(leaf) = 1`; `tree_count(n) = 1 + Σ_children
//!   tree_count(c)` for `Add`/`Mul`. Report value = `Σ_roots
//!   tree_count(root)`. `u128`: a DAG with reconvergent fan-in can make this
//!   astronomical — the scenario M0 exists to detect.
//! - `ceiling`: width-weighted all-recompute `Dram`-leaf touches:
//!   `ceiling(leaf) = width` if `Dram`, else `0`; `ceiling(n) = Σ_children
//!   ceiling(c)` for `Add`/`Mul` (no "+1" — only leaf touches count, not
//!   node visits). Report value = `Σ_roots ceiling(root)`. `u128` for the
//!   same reason as `sites`.
//! - `max_depth`: `depth(leaf) = 1`; `depth(n) = 1 + max_children depth(c)`
//!   for `Add`/`Mul` (empty max = 0, so a childless `Add`/`Mul` — degenerate,
//!   but handled — is depth 1 too). Report value = `max_roots depth(root)`:
//!   the deepest root-to-leaf path in the recompute tree, computed as a DAG
//!   height (memoized, never walked).
//!
//! `peak` is NOT reimplemented here — it is `max_roots su::cone_peak(view,
//! root)`, deferring entirely to the authoritative streaming-peak model.
//!
//! `floor` (width-weighted DISTINCT `Dram` leaves) is not a per-root sum — a
//! leaf shared across roots must count once, not once per root — so it is
//! not expressible as the same additive per-node memo. It reuses the same
//! `mark_reachable` table and just sums the width of each reachable `Dram`
//! leaf exactly once (`distinct_dram_floor`). Still O(dag_nodes) total,
//! still never walks the recompute tree.
//!
//! All `u128` accumulations use `checked_add`, panicking loudly on overflow
//! rather than silently wrapping — a wraparound here would silently corrupt
//! the M0 decision this DP exists to inform.

use cs::gkr_compiler::dag_ir::ExprId;

use crate::dag::{LayerView, LeafClass, NodeKind};
use crate::su;

/// The five M0 sizing quantities for one layer's `roots` (see module docs
/// for the exact DP each field is defined by).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SizingReport {
    pub roots: usize,
    pub dag_nodes: usize,
    /// All-recompute tree cardinality = Σ_roots tree_count(root);
    /// tree_count(n) = 1 + Σ_children tree_count(c). u128: may be astronomical.
    pub sites: u128,
    pub max_depth: u32,
    /// max over roots of su::cone_peak (lanes) — the feasibility assert value.
    pub peak: u32,
    /// Width-weighted all-recompute Dram-leaf touches (the traffic ceiling).
    pub ceiling: u128,
    /// Width-weighted distinct Dram leaves (the traffic floor).
    pub floor: u64,
}

/// Sizes `roots` within `view`'s layer: all five M0 quantities, each
/// memoized over the DAG (never the recompute tree — see module docs).
pub fn size_layer(view: &LayerView<'_>, roots: &[ExprId]) -> SizingReport {
    let dag_nodes = view.layer.exprs.len();
    let reachable = mark_reachable(view, roots, dag_nodes);
    let stats = compute_node_stats(view, dag_nodes, &reachable);

    let mut sites: u128 = 0;
    let mut ceiling: u128 = 0;
    let mut max_depth: u32 = 0;
    let mut peak: u32 = 0;
    for &r in roots {
        let s = stats[r.0 as usize]
            .unwrap_or_else(|| panic!("gkr_flatten: root {r:?} not marked reachable from itself"));
        sites = checked_add_u128(sites, s.sites, "sites (root sum)");
        ceiling = checked_add_u128(ceiling, s.ceiling, "ceiling (root sum)");
        max_depth = max_depth.max(s.depth);
        peak = peak.max(su::cone_peak(view, r));
    }

    let floor = distinct_dram_floor(view, &reachable, dag_nodes);

    SizingReport { roots: roots.len(), dag_nodes, sites, max_depth, peak, ceiling, floor }
}

/// Marks every node reachable from `roots` by following structural `Add`/
/// `Mul` arguments (never a `LookupValue::query` — that's resolution
/// metadata, not a value-cone child; see `dag::LayerView::kind`'s doc). A
/// single descending pass over `0..dag_nodes` suffices: a node's children
/// always carry a strictly smaller `ExprId` than the node itself (arena
/// construction only ever appends — see `compute_node_stats`), so scanning
/// top-down guarantees a node is marked (if reachable) before we decide
/// whether to mark its children.
fn mark_reachable(view: &LayerView<'_>, roots: &[ExprId], dag_nodes: usize) -> Vec<bool> {
    let mut reachable = vec![false; dag_nodes];
    for &r in roots {
        reachable[r.0 as usize] = true;
    }
    for i in (0..dag_nodes).rev() {
        if !reachable[i] {
            continue;
        }
        if let NodeKind::Add(args) | NodeKind::Mul(args) = view.kind(ExprId(i as u32)) {
            for &a in args {
                reachable[a.0 as usize] = true;
            }
        }
    }
    reachable
}

/// Per-node `(sites, depth, ceiling)` triple, memoized bottom-up (see module
/// docs for the exact recurrences).
#[derive(Clone, Copy)]
struct NodeStats {
    sites: u128,
    depth: u32,
    ceiling: u128,
}

/// Computes `NodeStats` for every node reachable from the `roots` passed to
/// `size_layer` (per `reachable`, from `mark_reachable`) — not the whole
/// layer arena, which may contain nodes disconnected from any given root
/// (e.g. a `LookupValue`'s `query` sub-expression, never a value-cone
/// child). Skipping unreached nodes is safe: `reachable`'s construction
/// guarantees every child of a reachable `Add`/`Mul` is itself reachable, so
/// by the time an ascending scan reaches a reachable node, all of its
/// (reachable) children already have computed stats.
///
/// Also carries the extra debug assertion beyond the DP itself: for every
/// reachable non-leaf node, `view.width(e) >= view.width(child)` for each
/// child (a Task-2 review carry-forward). Since `LayerView::width` became
/// an override-aware recursive join (see its doc — a composite's field is
/// the join over its children's resolved fields, overrides consulted at
/// every level), this holds by construction UNLESS an explicit override
/// forces a composite below one of its children — so the assertion now
/// serves as an override-consistency tripwire and is expected to stay
/// silent. (Historical note: under the original `expr_field`-delegating
/// `width`, it fired pervasively on real fixtures — every bwd L0 plus
/// ~10/12 fwd fixtures — which is what motivated the width fix; see the M0
/// sizing audit.)
fn compute_node_stats(
    view: &LayerView<'_>,
    dag_nodes: usize,
    reachable: &[bool],
) -> Vec<Option<NodeStats>> {
    let mut stats: Vec<Option<NodeStats>> = vec![None; dag_nodes];
    for i in 0..dag_nodes {
        if !reachable[i] {
            continue;
        }
        let e = ExprId(i as u32);
        let s = match view.kind(e) {
            NodeKind::Leaf(class) => NodeStats {
                sites: 1,
                depth: 1,
                ceiling: match class {
                    LeafClass::Dram { width } => width as u128,
                    LeafClass::Free => 0,
                },
            },
            NodeKind::Add(args) | NodeKind::Mul(args) => {
                let node_width = view.width(e);
                let mut site_sum: u128 = 1;
                let mut ceiling_sum: u128 = 0;
                let mut max_child_depth: u32 = 0;
                for &a in args {
                    debug_assert!(
                        a.0 < e.0,
                        "gkr_flatten: forward-scan invariant violated: child {a:?} does not \
                         precede parent {e:?} (expected arena children to always have a \
                         strictly smaller ExprId than their parent)"
                    );
                    let child_width = view.width(a);
                    debug_assert!(
                        node_width >= child_width,
                        "gkr_flatten: parent width {node_width} < child width {child_width} at \
                         expr {e:?}, child {a:?} (bwd field_overrides invariant violated: a \
                         parent must never be narrower than a child it folds)"
                    );
                    let c = stats[a.0 as usize].unwrap_or_else(|| {
                        panic!(
                            "gkr_flatten: child {a:?} of {e:?} has no computed stats yet \
                             (forward-scan invariant violated)"
                        )
                    });
                    site_sum = checked_add_u128(site_sum, c.sites, "sites");
                    ceiling_sum = checked_add_u128(ceiling_sum, c.ceiling, "ceiling");
                    max_child_depth = max_child_depth.max(c.depth);
                }
                NodeStats { sites: site_sum, depth: max_child_depth + 1, ceiling: ceiling_sum }
            }
        };
        stats[i] = Some(s);
    }
    stats
}

/// Width-weighted count of DISTINCT `Dram` leaves reachable from `roots`
/// (per the precomputed `reachable` table from `mark_reachable`).
fn distinct_dram_floor(view: &LayerView<'_>, reachable: &[bool], dag_nodes: usize) -> u64 {
    let mut floor: u64 = 0;
    for i in 0..dag_nodes {
        if !reachable[i] {
            continue;
        }
        if let NodeKind::Leaf(LeafClass::Dram { width }) = view.kind(ExprId(i as u32)) {
            floor = floor.checked_add(width as u64).unwrap_or_else(|| {
                panic!("gkr_flatten: u64 overflow accumulating `floor` at expr {i}")
            });
        }
    }
    floor
}

fn checked_add_u128(a: u128, b: u128, label: &str) -> u128 {
    a.checked_add(b).unwrap_or_else(|| {
        panic!("gkr_flatten: u128 overflow accumulating `{label}` (a={a} b={b})")
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use cs::gkr_compiler::dag_ir::{DagLayer, FieldKind, ReadPlace};

    use super::*;
    use crate::dag::testdag::{mixed_peak_layer, shared_diamond, tiny_fma_layer};

    fn view<'a>(l: &'a DagLayer, cross: &'a HashMap<ReadPlace, FieldKind>) -> LayerView<'a> {
        LayerView::new(l, cross, None)
    }

    fn roots_of(l: &DagLayer) -> Vec<ExprId> {
        l.roots.iter().map(|r| r.expr).collect()
    }

    #[test]
    fn shared_subexpr_counts_per_path() {
        // s shared under two roots: sites counts s's subtree twice; floor
        // counts its leaves once; ceiling counts them twice (all-recompute
        // re-touches them).
        let layer = shared_diamond(); // r0=Add(s,a), r1=Add(s,b), s=Mul(w,w2)
        let cross = HashMap::new();
        let v = view(&layer, &cross);
        let roots = roots_of(&layer);
        let r = size_layer(&v, &roots);
        assert_eq!(r.floor, 4, "4 distinct Base reads (w, w2, a, b), width 1 each");
        assert_eq!(r.ceiling, 6, "w and w2 each touched twice (once per root)");
        assert!(r.sites > r.dag_nodes as u128, "shared subtree inflates all-recompute sites");
    }

    #[test]
    fn peak_matches_su() {
        // root0: flat Base Add (peak 0); root1: Ext spill cone (peak 4).
        let layer = mixed_peak_layer();
        let cross = HashMap::new();
        let v = view(&layer, &cross);
        let roots = roots_of(&layer);
        let r = size_layer(&v, &roots);
        let expected = roots.iter().map(|&e| su::cone_peak(&v, e)).max().unwrap();
        assert_eq!(r.peak, expected);
        assert_eq!(r.peak, 4, "non-degenerate: root 1's spill cone dominates root 0's zero peak");
    }

    /// No-sharing baseline: `tiny_fma_layer` is a pure tree (no shared
    /// subexpr), so all-recompute `sites` collapses to the plain node count.
    #[test]
    fn no_sharing_sites_equals_dag_nodes() {
        let layer = tiny_fma_layer();
        let cross = HashMap::new();
        let v = view(&layer, &cross);
        let roots = roots_of(&layer);
        let r = size_layer(&v, &roots);
        assert_eq!(r.dag_nodes, 5);
        assert_eq!(r.sites, 5);
        assert_eq!(r.ceiling, 3); // w0, w1, w2 Base reads, width 1 each, no sharing
        assert_eq!(r.floor, 3);
        assert_eq!(r.max_depth, 3);
        assert_eq!(r.peak, 0); // Mul(leaf,leaf) is a streamable fma; the Add fold is empty
    }

    /// Smoke test against a real fixture layer: no panics, and the
    /// floor <= ceiling bracket the spike itself asserts on every row.
    #[test]
    fn add_sub_l0_bracket_holds() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let layer = &dag.layers[0];
        let v = LayerView::new(layer, &cross, None);
        let roots: Vec<ExprId> = layer.roots.iter().map(|r| r.expr).collect();
        let r = size_layer(&v, &roots);
        assert!(
            r.floor as u128 <= r.ceiling,
            "bracket violated: floor={} ceiling={}",
            r.floor,
            r.ceiling
        );
    }
}
