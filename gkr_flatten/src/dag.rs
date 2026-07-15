//! `LayerView` adapter: uniform width-inference and leaf-classification over a
//! `DagLayer`, ready to drive the flattener's traversal (widths in lanes,
//! DRAM-vs-Free leaf split).
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};

use cs::gkr_compiler::dag_ir::{
    join, source_field, DagLayer, Expr, ExprId, FieldKind, ReadPlace, SourceKind,
};

/// A `DagLayer` plus the two field-kind resolvers needed to make width
/// inference total: the cross-layer map (for `LayerOutput`/`CacheOutput`
/// reads local source inference can't resolve on its own) and, for backward
/// layers, the distilled per-expr overrides
/// (`DistilledLayer.field_overrides`). Build via [`LayerView::new`] (the
/// width memo is a private field, so struct-literal construction is not
/// available outside this module).
pub struct LayerView<'a> {
    pub layer: &'a DagLayer,
    pub cross: &'a HashMap<ReadPlace, FieldKind>,
    /// bwd DistilledLayer.field_overrides; None for fwd layers.
    pub overrides: Option<&'a BTreeMap<ExprId, FieldKind>>,
    /// Lazily-filled per-expr field memo backing [`LayerView::width`] —
    /// recursion without it is exponential on shared DAGs.
    field_memo: RefCell<Vec<Option<FieldKind>>>,
}

/// The shape of a node in the layer's expr DAG, as seen by the flattener.
pub enum NodeKind<'a> {
    Leaf(LeafClass),
    Add(&'a [ExprId]),
    Mul(&'a [ExprId]),
}

/// How a leaf source contributes to DRAM traffic.
pub enum LeafClass {
    /// Real DRAM read; traffic = width lanes per touch. Cache candidate.
    Dram { width: u32 },
    /// Resolver/const/challenge/lookup-value leaf; 0 traffic, never cached.
    Free,
}

/// Lane width for a `FieldKind`: Base = 1, Ext = 4.
fn lanes(field: FieldKind) -> u32 {
    match field {
        FieldKind::Base => 1,
        FieldKind::Ext => 4,
    }
}

impl<'a> LayerView<'a> {
    /// Builds a view over `layer` with an empty (lazily-filled) width memo.
    pub fn new(
        layer: &'a DagLayer,
        cross: &'a HashMap<ReadPlace, FieldKind>,
        overrides: Option<&'a BTreeMap<ExprId, FieldKind>>,
    ) -> Self {
        let field_memo = RefCell::new(vec![None; layer.exprs.len()]);
        Self { layer, cross, overrides, field_memo }
    }

    /// Classifies expr `e`'s node shape. `Source` leaves split into
    /// `LeafClass::Dram` (a real `SourceKind::Read`) or `LeafClass::Free`
    /// (`Constant`/`Challenge`/`VirtualSetup`/`LookupValue` — the
    /// `LookupValue::query` expr is resolution metadata, never a child to
    /// walk here).
    pub fn kind(&self, e: ExprId) -> NodeKind<'a> {
        match &self.layer.exprs[e.0 as usize] {
            Expr::Source(src_id) => match &self.layer.sources[src_id.0 as usize].kind {
                SourceKind::Read { .. } => NodeKind::Leaf(LeafClass::Dram { width: self.width(e) }),
                SourceKind::Constant { .. }
                | SourceKind::Challenge { .. }
                | SourceKind::VirtualSetup { .. }
                | SourceKind::LookupValue { .. } => NodeKind::Leaf(LeafClass::Free),
            },
            Expr::Add(args) => NodeKind::Add(args.as_slice()),
            Expr::Mul(args) => NodeKind::Mul(args.as_slice()),
        }
    }

    /// Resolves expr `e`'s width in lanes (Base = 1, Ext = 4). Memoized per
    /// view — O(nodes) total across any number of queries.
    ///
    /// Resolution, at EVERY node (not just the queried one):
    /// - `overrides` first (bwd distilled per-expr field): an explicit
    ///   override is authoritative for that node.
    /// - Leaf (`Source`): `field_infer::source_field`; on `Err(place)` (an
    ///   unresolvable cross-layer read) fall back to the `cross` map. A miss
    ///   in `cross` too is a fixture/adapter bug — panic with the offending
    ///   place.
    /// - Composite (`Add`/`Mul`): `field_infer::join` over the RECURSIVE
    ///   widths of all children — each child consults `overrides` again.
    ///
    /// Composites deliberately do NOT delegate to `field_infer::expr_field`,
    /// for two reasons (both produced real under-reports on fixtures — see
    /// the M0 sizing audit): (1) `expr_field` bails with the FIRST
    /// `Err(ReadPlace)` it hits, discarding any Ext sibling's field, so an
    /// `Add` mixing a cross-layer read with an `Ext` leaf could resolve
    /// `Base`; (2) `expr_field`'s internal recursion cannot see `overrides`,
    /// so a join above a bwd forced-`Ext` fold leaf inferred `Base`. Both
    /// under-report composite width, which makes `su::cone_peak`
    /// under-charge stash — an unsound feasibility floor (over-charging is
    /// tolerable, under-charging never).
    pub fn width(&self, e: ExprId) -> u32 {
        lanes(self.field(e))
    }

    /// The memoized override-aware field-kind join behind [`width`].
    fn field(&self, e: ExprId) -> FieldKind {
        let memoized = self.field_memo.borrow()[e.0 as usize];
        if let Some(f) = memoized {
            return f;
        }
        let f = if let Some(f) = self.overrides.and_then(|o| o.get(&e)) {
            *f
        } else {
            match &self.layer.exprs[e.0 as usize] {
                Expr::Source(src_id) => {
                    match source_field(&self.layer.sources[src_id.0 as usize].kind) {
                        Ok(f) => f,
                        Err(place) => match self.cross.get(&place) {
                            Some(f) => *f,
                            None => panic!(
                                "gkr_flatten: unresolved cross-layer read place {place:?} for \
                                 expr {e:?} (missing from both DagLayer inference and the \
                                 cross-layer field map)"
                            ),
                        },
                    }
                }
                Expr::Add(args) | Expr::Mul(args) => {
                    let mut acc = FieldKind::Base;
                    for &a in args {
                        acc = join(acc, self.field(a));
                        if acc == FieldKind::Ext {
                            break; // join is monotone: Ext absorbs.
                        }
                    }
                    acc
                }
            }
        };
        self.field_memo.borrow_mut()[e.0 as usize] = Some(f);
        f
    }
}

#[cfg(test)]
pub(crate) mod testdag {
    use super::*;
    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef, Root, SourceId, SourceInfo,
    };

    /// Builds a `DagLayer` from explicit tables; `batching`/`resolutions`
    /// default to empty (fine for the synthetic layers these tests need).
    pub fn layer(sources: Vec<SourceInfo>, exprs: Vec<Expr>, roots: Vec<Root>) -> DagLayer {
        DagLayer {
            sources,
            exprs,
            roots,
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        }
    }

    pub fn read_source(place: ReadPlace) -> SourceInfo {
        SourceInfo { kind: SourceKind::Read { place } }
    }

    /// An Ext-width (4-lane) free leaf: a challenge source. Least-ceremony way
    /// to get a `Source` expr that `source_field` resolves to `FieldKind::Ext`
    /// without needing a `cross`-map or `overrides` entry (see
    /// `field_infer::source_field`: `Challenge` is the only always-Ext,
    /// always-locally-resolvable `SourceKind`).
    pub fn challenge_source() -> SourceInfo {
        SourceInfo {
            kind: SourceKind::Challenge {
                reference: ChallengeRef {
                    key: ChallengeKey::ConstraintAggregation,
                    power: ChallengePower::One,
                },
            },
        }
    }

    pub fn root(expr: ExprId) -> Root {
        Root { expr, materialize: None, claim: None }
    }

    /// w0 + w1*w2 over three Base witness reads: roots=[Add(w0, Mul(w1,w2))].
    pub fn tiny_fma_layer() -> DagLayer {
        let sources = vec![
            read_source(ReadPlace::BaseLayerWitness { column: 0 }),
            read_source(ReadPlace::BaseLayerWitness { column: 1 }),
            read_source(ReadPlace::BaseLayerWitness { column: 2 }),
        ];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
            Expr::Mul(vec![ExprId(1), ExprId(2)]),
            Expr::Add(vec![ExprId(0), ExprId(3)]),
        ];
        let roots = vec![root(ExprId(4))];
        layer(sources, exprs, roots)
    }

    /// A `BaseLayerWitness` read at `column` — the least-ceremony way to get
    /// a Base-width (1-lane) `LeafClass::Dram` leaf for synthetic layers.
    pub fn base_read(column: usize) -> SourceInfo {
        read_source(ReadPlace::BaseLayerWitness { column })
    }

    /// `s = Mul(w, w2)` shared under two roots: `r0 = Add(s, a)`, `r1 =
    /// Add(s, b)`. All Base witness reads. Exercises the sites-vs-floor-vs-
    /// ceiling split under fan-in sharing (`analysis::tests::
    /// shared_subexpr_counts_per_path`): `s`'s subtree is double-counted by
    /// `sites`/`ceiling` (one full recompute per root) but its two leaves
    /// (`w`, `w2`) are each counted once by `floor` (distinct Dram leaves).
    pub fn shared_diamond() -> DagLayer {
        let sources = vec![base_read(0), base_read(1), base_read(2), base_read(3)];
        let exprs = vec![
            Expr::Source(SourceId(0)),             // w
            Expr::Source(SourceId(1)),             // w2
            Expr::Source(SourceId(2)),             // a
            Expr::Source(SourceId(3)),             // b
            Expr::Mul(vec![ExprId(0), ExprId(1)]), // s = w * w2
            Expr::Add(vec![ExprId(4), ExprId(2)]), // r0 = s + a
            Expr::Add(vec![ExprId(4), ExprId(3)]), // r1 = s + b
        ];
        layer(sources, exprs, vec![root(ExprId(5)), root(ExprId(6))])
    }

    /// Two-root layer for the `peak == max over roots of cone_peak`
    /// cross-check (`analysis::tests::peak_matches_su`): root 0 is a flat
    /// Base `Add` of 4 leaves (peak 0); root 1 reproduces the Ext
    /// nested-fold-spill shape from `su::tests::nested_fold_spills_width`
    /// (peak 4), so the test sees a non-degenerate, root-dependent maximum
    /// rather than an all-zero one.
    pub fn mixed_peak_layer() -> DagLayer {
        let mut sources = vec![base_read(0), base_read(1), base_read(2), base_read(3)];
        sources.extend((0..6).map(|_| challenge_source()));
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
            Expr::Source(SourceId(3)),
            Expr::Add(vec![ExprId(0), ExprId(1), ExprId(2), ExprId(3)]), // flat root, peak 0
            Expr::Source(SourceId(4)),
            Expr::Source(SourceId(5)),
            Expr::Source(SourceId(6)),
            Expr::Source(SourceId(7)),
            Expr::Source(SourceId(8)),
            Expr::Source(SourceId(9)),
            Expr::Add(vec![ExprId(5), ExprId(6)]),   // A1
            Expr::Mul(vec![ExprId(11), ExprId(7)]),  // M1 = A1 * leaf
            Expr::Add(vec![ExprId(8), ExprId(9)]),   // A2
            Expr::Mul(vec![ExprId(13), ExprId(10)]), // M2 = A2 * leaf
            Expr::Add(vec![ExprId(12), ExprId(14)]), // spill root, peak 4
        ];
        layer(sources, exprs, vec![root(ExprId(4)), root(ExprId(15))])
    }
}

#[cfg(test)]
mod tests {
    use cs::gkr_compiler::dag_ir::SourceId;

    use super::*;

    #[test]
    fn widths_and_kinds() {
        let layer = testdag::tiny_fma_layer();
        let cross = HashMap::new();
        let v = LayerView::new(&layer, &cross, None);
        assert_eq!(v.width(ExprId(0)), 1); // Base witness read
        assert!(matches!(v.kind(ExprId(0)), NodeKind::Leaf(LeafClass::Dram { width: 1 })));
        assert!(matches!(v.kind(ExprId(3)), NodeKind::Mul(_)));
        assert!(matches!(v.kind(ExprId(4)), NodeKind::Add(_)));
    }

    #[test]
    fn add_sub_l0_widths_and_kinds_resolve() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let layer = &dag.layers[0];
        let v = LayerView::new(layer, &cross, None);
        for i in 0..layer.exprs.len() {
            let e = ExprId(i as u32);
            let _ = v.width(e); // must not panic: resolvable via source_field or cross
            match v.kind(e) {
                NodeKind::Leaf(_) | NodeKind::Add(_) | NodeKind::Mul(_) => {}
            }
        }
    }

    /// The bwd under-report shape (M0 sizing audit finding 1): a Base leaf
    /// carrying an Ext OVERRIDE under an Add of otherwise-Base leaves. The
    /// override must propagate through the join — parent width 4, not the
    /// override-oblivious structural inference's 1.
    #[test]
    fn override_on_leaf_widens_parent_join() {
        let layer = testdag::layer(
            vec![testdag::base_read(0), testdag::base_read(1)],
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Add(vec![ExprId(0), ExprId(1)]),
            ],
            vec![testdag::root(ExprId(2))],
        );
        let cross = HashMap::new();
        let overrides = BTreeMap::from([(ExprId(0), FieldKind::Ext)]);
        let v = LayerView::new(&layer, &cross, Some(&overrides));
        assert_eq!(v.width(ExprId(0)), 4, "override is authoritative for the leaf");
        assert_eq!(v.width(ExprId(1)), 1, "sibling stays Base");
        assert_eq!(v.width(ExprId(2)), 4, "join must see the overridden child");
    }

    /// The fwd under-report shape (M0 sizing audit finding 2): an Add whose
    /// FIRST child is a cross-layer read resolving Base via `cross`, and
    /// whose sibling is a locally-Ext Challenge leaf. `expr_field` bails
    /// with the first `Err(place)` and would discard the sibling's Ext-ness
    /// (Base, width 1); the recursive join must yield Ext (width 4).
    #[test]
    fn cross_read_sibling_ext_widens_parent_join() {
        let place = ReadPlace::LayerOutput { layer: 1, offset: 0 };
        let layer = testdag::layer(
            vec![testdag::read_source(place.clone()), testdag::challenge_source()],
            vec![
                Expr::Source(SourceId(0)), // cross-layer read (Err from source_field)
                Expr::Source(SourceId(1)), // Challenge: locally Ext
                Expr::Add(vec![ExprId(0), ExprId(1)]),
            ],
            vec![testdag::root(ExprId(2))],
        );
        let cross = HashMap::from([(place, FieldKind::Base)]);
        let v = LayerView::new(&layer, &cross, None);
        assert_eq!(v.width(ExprId(0)), 1, "cross map resolves the read Base");
        assert_eq!(v.width(ExprId(1)), 4, "challenge is Ext");
        assert_eq!(v.width(ExprId(2)), 4, "join must keep the Ext sibling");
    }
}
