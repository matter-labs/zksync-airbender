//! Streaming Sethi–Ullman peak: lane demand to compute a cone with nothing
//! resident, under SU-optimal (peak-descending) child order.
//!
//! # Cost model (corrected streaming model)
//!
//! `peak(leaf) = 0`; a streamable Mul fuses (product never materialized); for
//! a fold node over its NON-streamable children `F` sorted desc by peak:
//! `|F|=0 → 0`, `|F|=1 → peak(F0)`, `|F|≥2 → max(peak(F0), width(node) +
//! peak(F1))`. fma temp rule: a 2-arity Mul child under Add with a
//! non-streamable operand contributes that operand's computation as a fold
//! child (the temp is stashed at the operand's width).
//!
//! # Realization notes
//!
//! - An Add's fold set `F` is its non-streamable children only: streamable
//!   children (leaves, fma-Muls) stream into the accumulator for free, and a
//!   single non-streamable child computes straight into the accumulator
//!   (`|F|=1 → peak(F0)`, no width charge).
//! - A NON-streamable Mul has no additive streaming accumulator to hide
//!   behind: a computed operand must be stashed as a temp before the product
//!   can stream into the consumer. This is the fma temp rule, realized by
//!   applying the general fold formula to the Mul over ALL of its children
//!   (streamable operands contribute peak 0, non-streamable ones their own
//!   peak). Any non-streamable Mul has ≥2 children, so the `|F|≥2` arm fires
//!   and charges `width(mul)` over the second-highest operand peak — the
//!   nested-fold guard case `Add(Mul(Add(l,l), l), l)` lands on
//!   `max(peak(innerAdd), width(mul) + 0) = 4` at Ext widths.
//!   Conservative choice (documented as a Task-3 concern): the temp is
//!   charged at `width(mul)` (the join of operand widths), not the computed
//!   operand's own width — these differ only for a Base computed operand
//!   multiplied by an Ext leaf, where we charge 4 instead of 1.
//! - A >2-arity Mul is never streamable (streamable is strictly 2-arity per
//!   spec), so a pure-leaf 3-arity Mul charges `width(mul)` — conservative:
//!   the partial product is modeled as a stashed temp.
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
            NodeKind::Add(args) => {
                // Fold set = non-streamable children only; streamables are free.
                let mut fold = Vec::new();
                for &a in args {
                    if !self.streamable(view, a) {
                        fold.push(self.peak(view, a));
                    }
                }
                fold_peak(view, e, fold)
            }
            NodeKind::Mul(args) => {
                if self.streamable(view, e) {
                    0 // fused fma: the product is never materialized
                } else {
                    // fma temp rule: every operand is a fold child (streamable
                    // operands have peak 0 by definition); the |F|≥2 arm
                    // charges width(mul) for the stashed temp.
                    let mut fold = Vec::new();
                    for &a in args {
                        fold.push(self.peak(view, a));
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
        LayerView { layer: l, cross: EMPTY_CROSS.get_or_init(HashMap::new), overrides: None }
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

    /// Add(Mul(Add(l,l), l), l) at Ext widths (challenge leaves): the inner
    /// Add's value is a computed multiplicand — it must materialize as an fma
    /// temp of width 4. Peak = 4.
    #[test]
    fn nested_fold_spills_width() {
        let sources = vec![challenge_source(); 4];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
            Expr::Source(SourceId(3)),
            Expr::Add(vec![ExprId(0), ExprId(1)]), // inner Add, Ext (4 lanes)
            Expr::Mul(vec![ExprId(4), ExprId(2)]), // non-streamable fma: temp = inner Add
            Expr::Add(vec![ExprId(5), ExprId(3)]), // outer fold
        ];
        let l = layer(sources, exprs, vec![root(ExprId(6))]);
        let v = view(&l);
        assert!(!streamable(&v, ExprId(5)), "Mul with a computed operand must not stream");
        assert_eq!(cone_peak(&v, ExprId(6)), 4);
    }

    /// Fold with two computed Ext children: `max(p0, 4 + p1)` with F sorted
    /// desc by peak. Exercised at (p0, p1) = (4, 0) in both child orders
    /// (sorting must make order irrelevant) and at (4, 4).
    #[test]
    fn two_nonstreamable_children_charge_width() {
        // Builds the peak-4 cone from `nested_fold_spills_width` twice and a
        // peak-0 computed Ext child (Add of two challenge leaves), then folds
        // selected pairs.
        // Sources: 8 challenges for two nested cones + 2 for the flat Add.
        let sources = vec![challenge_source(); 10];
        // Nested cone A: exprs 0..=6 (root 6, peak 4).
        // Nested cone B: exprs 7..=13 (root 13, peak 4).
        // Flat Ext Add C: exprs 14..=16 (root 16, peak 0).
        let mut exprs = Vec::new();
        for (expr_base, src_base) in [(0u32, 0u32), (7, 4)] {
            let e = |i: u32| ExprId(expr_base + i);
            let s = |i: u32| SourceId(src_base + i);
            exprs.extend([
                Expr::Source(s(0)),
                Expr::Source(s(1)),
                Expr::Source(s(2)),
                Expr::Source(s(3)),
                Expr::Add(vec![e(0), e(1)]),
                Expr::Mul(vec![e(4), e(2)]),
                Expr::Add(vec![e(5), e(3)]),
            ]);
        }
        exprs.extend([
            Expr::Source(SourceId(8)),
            Expr::Source(SourceId(9)),
            Expr::Add(vec![ExprId(14), ExprId(15)]),
        ]);
        let (a, b, c) = (ExprId(6), ExprId(13), ExprId(16));
        // Folds under test: (A, C) both orders, and (A, B).
        exprs.push(Expr::Add(vec![a, c])); // 17
        exprs.push(Expr::Add(vec![c, a])); // 18
        exprs.push(Expr::Add(vec![a, b])); // 19
        let l = layer(sources, exprs, vec![root(ExprId(17)), root(ExprId(18)), root(ExprId(19))]);
        let v = view(&l);
        assert_eq!(cone_peak(&v, a), 4, "nested cone peak (precondition)");
        assert_eq!(cone_peak(&v, c), 0, "flat Ext Add peak (precondition)");
        // (p0, p1) = (4, 0): max(4, 4 + 0) = 4, regardless of child order.
        assert_eq!(cone_peak(&v, ExprId(17)), 4);
        assert_eq!(cone_peak(&v, ExprId(18)), 4);
        // (p0, p1) = (4, 4): max(4, 4 + 4) = 8.
        assert_eq!(cone_peak(&v, ExprId(19)), 8);
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
        let v = LayerView { layer, cross: &cross, overrides: None };
        for r in &layer.roots {
            let _ = cone_peak(&v, r.expr);
        }
    }
}
