//! Streaming Sethi–Ullman peak: lane demand to compute a cone with nothing
//! resident, under SU-optimal (peak-descending) child order.
//!
//! # Cost model (uniform streaming fold)
//!
//! `peak(leaf) = 0`; a streamable Mul fuses (product never materialized);
//! for ANY non-streamable fold node — Add and Mul alike — over its
//! NON-streamable children `F` sorted desc by peak: `|F|=0 → 0`,
//! `|F|=1 → peak(F0)`, `|F|≥2 → max(peak(F0), width(node) + peak(F1))` —
//! while the i-th (i ≥ 1) child computes in the accumulator, the fold's
//! partial value sits stashed at `width(node)`.
//!
//! No product-side temp is ever charged: fma is emitted only when both
//! operands are ready; non-ready products lower as Mul-folds (stash parent,
//! compute product in acc, combine), which is instruction-cheaper and
//! peak-lower than fma-with-temps.
//!
//! # Notes
//!
//! - Streamable children (leaves, fma-Muls) stream into the accumulator for
//!   free; a single non-streamable child computes straight into the
//!   accumulator (`|F|=1 → peak(F0)`, no width charge).
//! - A ≥3-arity Mul is never streamable (`streamable` is strictly 2-arity
//!   per spec) — it is not an fma candidate — but a pure-leaf one is still
//!   peak-free: all operands stream into its own Mul-fold accumulator
//!   (`F = ∅`).
//! - A root that is itself a leaf or a streamable Mul has peak 0 (its value
//!   streams into the materialize sink without occupying a cell).
//!
//! Both entry points memoize over the DAG per call (`Vec<Option<_>>` indexed
//! by `ExprId`), so shared subgraphs are visited once — O(nodes) per call.

use cs::gkr_compiler::dag_ir::ExprId;

use crate::dag::{LayerView, NodeKind};

/// Peak stash demand (lanes) to compute `root` with nothing resident,
/// under SU-optimal child order. Memoized over the DAG (O(nodes)).
pub fn cone_peak(view: &LayerView<'_>, root: ExprId) -> u32 {
    let n = view.layer.exprs.len();
    let mut memo = Memo { peak: vec![None; n], streamable: vec![None; n] };
    memo.peak(view, root)
}

/// True iff the node streams into an accumulation without occupying a cell:
/// any leaf, or a 2-arity Mul whose operands are both streamable (fma).
pub fn streamable(view: &LayerView<'_>, e: ExprId) -> bool {
    let mut memo = vec![None; view.layer.exprs.len()];
    streamable_memo(view, e, &mut memo)
}

/// Per-call memo tables, indexed by `ExprId`.
struct Memo {
    peak: Vec<Option<u32>>,
    streamable: Vec<Option<bool>>,
}

impl Memo {
    fn streamable(&mut self, view: &LayerView<'_>, e: ExprId) -> bool {
        streamable_memo(view, e, &mut self.streamable)
    }

    fn peak(&mut self, view: &LayerView<'_>, e: ExprId) -> u32 {
        if let Some(v) = self.peak[e.0 as usize] {
            return v;
        }
        let v = match view.kind(e) {
            NodeKind::Leaf(_) => 0,
            // Uniform fold: Add and Mul alike, over non-streamable children
            // only (streamables stream, contributing nothing). A streamable
            // Mul is a fused fma — never materialized, peak 0 (its F would
            // be empty anyway, so the formula agrees; the check just skips
            // the walk).
            NodeKind::Add(args) | NodeKind::Mul(args) => {
                if self.streamable(view, e) {
                    0
                } else {
                    let mut fold = Vec::new();
                    for &a in args {
                        if !self.streamable(view, a) {
                            fold.push(self.peak(view, a));
                        }
                    }
                    fold_peak(view, e, fold)
                }
            }
        };
        self.peak[e.0 as usize] = Some(v);
        v
    }
}

fn streamable_memo(view: &LayerView<'_>, e: ExprId, memo: &mut [Option<bool>]) -> bool {
    if let Some(v) = memo[e.0 as usize] {
        return v;
    }
    let v = match view.kind(e) {
        NodeKind::Leaf(_) => true,
        NodeKind::Mul(args) if args.len() == 2 => {
            let (a, b) = (args[0], args[1]);
            streamable_memo(view, a, memo) && streamable_memo(view, b, memo)
        }
        NodeKind::Add(_) | NodeKind::Mul(_) => false,
    };
    memo[e.0 as usize] = Some(v);
    v
}

/// The general fold formula over already-computed child peaks: sort desc;
/// `|F|=0 → 0`, `|F|=1 → peak(F0)`, `|F|≥2 → max(peak(F0), width(node) +
/// peak(F1))` — while the i-th (i ≥ 1) child computes, the fold's partial
/// value sits stashed at `width(node)`; sorted desc, `F1` maximizes it.
fn fold_peak(view: &LayerView<'_>, node: ExprId, mut peaks: Vec<u32>) -> u32 {
    peaks.sort_unstable_by(|a, b| b.cmp(a));
    match peaks.as_slice() {
        [] => 0,
        [p0] => *p0,
        [p0, p1, ..] => (*p0).max(view.width(node) + *p1),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::sync::OnceLock;

    use cs::gkr_compiler::dag_ir::{
        DagLayer, Expr, ExprId, FieldKind, ReadPlace, SourceId, SourceInfo,
    };

    use super::*;
    use crate::dag::testdag::{challenge_source, layer, read_source, root};

    fn view(l: &DagLayer) -> LayerView<'_> {
        static EMPTY_CROSS: OnceLock<HashMap<ReadPlace, FieldKind>> = OnceLock::new();
        LayerView::new(l, EMPTY_CROSS.get_or_init(HashMap::new), None)
    }

    fn base_read(col: usize) -> SourceInfo {
        read_source(ReadPlace::BaseLayerWitness { column: col })
    }

    /// Add of 4 Base leaves — everything streams; peak 0.
    #[test]
    fn flat_base_reduction_is_zero() {
        let sources = vec![base_read(0), base_read(1), base_read(2), base_read(3)];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
            Expr::Source(SourceId(3)),
            Expr::Add(vec![ExprId(0), ExprId(1), ExprId(2), ExprId(3)]),
        ];
        let l = layer(sources, exprs, vec![root(ExprId(4))]);
        assert_eq!(cone_peak(&view(&l), ExprId(4)), 0);
    }

    /// Add of two Mul(leaf, leaf) — both products are fused fmas; peak 0.
    #[test]
    fn sum_of_streamable_products_is_zero() {
        let sources = vec![base_read(0), base_read(1), base_read(2), base_read(3)];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
            Expr::Source(SourceId(3)),
            Expr::Mul(vec![ExprId(0), ExprId(1)]),
            Expr::Mul(vec![ExprId(2), ExprId(3)]),
            Expr::Add(vec![ExprId(4), ExprId(5)]),
        ];
        let l = layer(sources, exprs, vec![root(ExprId(6))]);
        let v = view(&l);
        assert!(streamable(&v, ExprId(4)), "Mul(leaf,leaf) must be a streamable fma");
        assert!(streamable(&v, ExprId(5)));
        assert!(!streamable(&v, ExprId(6)), "an Add is never streamable");
        assert_eq!(cone_peak(&v, ExprId(6)), 0);
    }

    /// Add(M1, M2) at Ext widths with M_i = Mul(Add(e,e), e): each product
    /// computes entirely in the accumulator (stream-add the inner Add, Mul
    /// the leaf in — `|F|=1 → 0`), but the outer fold has TWO non-streamable
    /// children: while M2 computes in the acc, M1's partial value is stashed
    /// at width 4. Peak = max(0, 4 + 0) = 4.
    #[test]
    fn nested_fold_spills_width() {
        let sources = vec![challenge_source(); 6];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
            Expr::Source(SourceId(3)),
            Expr::Source(SourceId(4)),
            Expr::Source(SourceId(5)),
            Expr::Add(vec![ExprId(0), ExprId(1)]), // A1, Ext (4 lanes)
            Expr::Mul(vec![ExprId(6), ExprId(2)]), // M1 = A1 * leaf: Mul-fold, peak 0
            Expr::Add(vec![ExprId(3), ExprId(4)]), // A2
            Expr::Mul(vec![ExprId(8), ExprId(5)]), // M2 = A2 * leaf
            Expr::Add(vec![ExprId(7), ExprId(9)]), // outer fold: F = {M1, M2}
        ];
        let l = layer(sources, exprs, vec![root(ExprId(10))]);
        let v = view(&l);
        assert!(!streamable(&v, ExprId(7)), "Mul with a computed operand must not stream");
        assert_eq!(cone_peak(&v, ExprId(7)), 0, "Mul-fold computes in the acc, no temp");
        assert_eq!(cone_peak(&v, ExprId(10)), 4);
    }

    /// Ext Add(M, e) with M = Mul(C, x), C = Add(b1,b2) Base-computed
    /// (peak 0), x/e Ext leaves. Walk trace: Load b1; Add b2 (C in acc);
    /// Mul x (product in acc); Add e — no stash anywhere. Peak = 0: a
    /// non-ready product lowers as a Mul-fold, never as fma-with-temp.
    #[test]
    fn mixed_width_product_needs_no_temp() {
        let sources =
            vec![base_read(0), base_read(1), challenge_source(), challenge_source()];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),             // x (Ext)
            Expr::Source(SourceId(3)),             // e (Ext)
            Expr::Add(vec![ExprId(0), ExprId(1)]), // C: Base computed, peak 0
            Expr::Mul(vec![ExprId(4), ExprId(2)]), // M: |F|=1 → peak(C) = 0
            Expr::Add(vec![ExprId(5), ExprId(3)]), // outer: |F|=1 → peak(M) = 0
        ];
        let l = layer(sources, exprs, vec![root(ExprId(6))]);
        let v = view(&l);
        assert_eq!(v.width(ExprId(6)), 4, "outer Add is Ext (precondition)");
        assert_eq!(cone_peak(&v, ExprId(6)), 0);
    }

    /// Add(Mul(l1,l2,l3), l4) all Base: a 3-arity Mul is not an fma
    /// candidate (streamable is strictly 2-arity) but is still free to
    /// fold — all operands stream into its own Mul-fold accumulator.
    #[test]
    fn pure_leaf_wide_product_is_free() {
        let sources = vec![base_read(0), base_read(1), base_read(2), base_read(3)];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
            Expr::Source(SourceId(3)),
            Expr::Mul(vec![ExprId(0), ExprId(1), ExprId(2)]),
            Expr::Add(vec![ExprId(4), ExprId(3)]),
        ];
        let l = layer(sources, exprs, vec![root(ExprId(5))]);
        let v = view(&l);
        assert!(!streamable(&v, ExprId(4)), "3-arity Mul is not an fma candidate");
        assert_eq!(cone_peak(&v, ExprId(5)), 0);
    }

    /// Fold with two computed Ext children: `max(p0, 4 + p1)` with F sorted
    /// desc by peak. Exercised at (p0, p1) = (4, 0) in both child orders
    /// (sorting must make order irrelevant) and at (4, 4).
    #[test]
    fn two_nonstreamable_children_charge_width() {
        // Builds the peak-4 spill cone from `nested_fold_spills_width` twice
        // and a peak-0 computed Ext child (Add of two challenge leaves),
        // then folds selected pairs.
        // Sources: 6 challenges per spill cone + 2 for the flat Add.
        let sources = vec![challenge_source(); 14];
        // Spill cone A: exprs 0..=10 (root 10, peak 4).
        // Spill cone B: exprs 11..=21 (root 21, peak 4).
        // Flat Ext Add C: exprs 22..=24 (root 24, peak 0).
        let mut exprs = Vec::new();
        for (expr_base, src_base) in [(0u32, 0u32), (11, 6)] {
            let e = |i: u32| ExprId(expr_base + i);
            let s = |i: u32| SourceId(src_base + i);
            exprs.extend([
                Expr::Source(s(0)),
                Expr::Source(s(1)),
                Expr::Source(s(2)),
                Expr::Source(s(3)),
                Expr::Source(s(4)),
                Expr::Source(s(5)),
                Expr::Add(vec![e(0), e(1)]), // A1
                Expr::Mul(vec![e(6), e(2)]), // M1
                Expr::Add(vec![e(3), e(4)]), // A2
                Expr::Mul(vec![e(8), e(5)]), // M2
                Expr::Add(vec![e(7), e(9)]), // cone root: F = {M1, M2} → 4
            ]);
        }
        exprs.extend([
            Expr::Source(SourceId(12)),
            Expr::Source(SourceId(13)),
            Expr::Add(vec![ExprId(22), ExprId(23)]),
        ]);
        let (a, b, c) = (ExprId(10), ExprId(21), ExprId(24));
        // Folds under test: (A, C) both orders, and (A, B).
        exprs.push(Expr::Add(vec![a, c])); // 25
        exprs.push(Expr::Add(vec![c, a])); // 26
        exprs.push(Expr::Add(vec![a, b])); // 27
        let l = layer(sources, exprs, vec![root(ExprId(25)), root(ExprId(26)), root(ExprId(27))]);
        let v = view(&l);
        assert_eq!(cone_peak(&v, a), 4, "spill cone peak (precondition)");
        assert_eq!(cone_peak(&v, c), 0, "flat Ext Add peak (precondition)");
        // (p0, p1) = (4, 0): max(4, 4 + 0) = 4, regardless of child order.
        assert_eq!(cone_peak(&v, ExprId(25)), 4);
        assert_eq!(cone_peak(&v, ExprId(26)), 4);
        // (p0, p1) = (4, 4): max(4, 4 + 4) = 8.
        assert_eq!(cone_peak(&v, ExprId(27)), 8);
    }

    /// A root that is itself a leaf, and one that is a streamable fma, both
    /// stream into their sink: peak 0.
    #[test]
    fn leaf_and_fma_roots_are_zero() {
        let sources = vec![base_read(0), base_read(1)];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Mul(vec![ExprId(0), ExprId(1)]),
        ];
        let l = layer(sources, exprs, vec![root(ExprId(2))]);
        let v = view(&l);
        assert_eq!(cone_peak(&v, ExprId(0)), 0);
        assert_eq!(cone_peak(&v, ExprId(2)), 0);
    }

    /// Every root of the real add_sub L0 fixture computes a finite peak
    /// without panicking (widths resolve; memoized walk covers the DAG).
    #[test]
    fn add_sub_l0_peaks_resolve() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let layer = &dag.layers[0];
        let v = LayerView::new(layer, &cross, None);
        for r in &layer.roots {
            let _ = cone_peak(&v, r.expr);
        }
    }
}
