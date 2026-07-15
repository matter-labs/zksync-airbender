//! `LayerView` adapter: uniform width-inference and leaf-classification over a
//! `DagLayer`, ready to drive the flattener's traversal (widths in lanes,
//! DRAM-vs-Free leaf split).
use std::collections::{BTreeMap, HashMap};

use cs::gkr_compiler::dag_ir::{
    expr_field, DagLayer, Expr, ExprId, FieldKind, ReadPlace, SourceKind,
};

/// A `DagLayer` plus the two field-kind resolvers needed to make width
/// inference total: the cross-layer map (for `LayerOutput`/`CacheOutput`
/// reads `expr_field` can't resolve on its own) and, for backward layers,
/// the distilled per-expr overrides (`DistilledLayer.field_overrides`).
pub struct LayerView<'a> {
    pub layer: &'a DagLayer,
    pub cross: &'a HashMap<ReadPlace, FieldKind>,
    /// bwd DistilledLayer.field_overrides; None for fwd layers.
    pub overrides: Option<&'a BTreeMap<ExprId, FieldKind>>,
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

    /// Resolves expr `e`'s width in lanes (Base = 1, Ext = 4).
    ///
    /// Resolution order: `overrides` (bwd distilled per-expr field, if
    /// present) first, then `expr_field` over the layer's own tables; if
    /// that hits an unresolvable cross-layer read (`Err(place)`), fall back
    /// to the `cross` map. A miss in `cross` too is a fixture/adapter bug —
    /// panic with the offending place.
    pub fn width(&self, e: ExprId) -> u32 {
        if let Some(field) = self.overrides.and_then(|o| o.get(&e)) {
            return lanes(*field);
        }
        match expr_field(&self.layer.exprs, &self.layer.sources, e) {
            Ok(field) => lanes(field),
            Err(place) => match self.cross.get(&place) {
                Some(field) => lanes(*field),
                None => panic!(
                    "gkr_flatten: unresolved cross-layer read place {place:?} for expr {e:?} \
                     (missing from both DagLayer inference and the cross-layer field map)"
                ),
            },
        }
    }
}

#[cfg(test)]
pub(crate) mod testdag {
    use super::*;
    use cs::gkr_compiler::dag_ir::{BatchingOrder, Root, SourceId, SourceInfo};

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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn widths_and_kinds() {
        let layer = testdag::tiny_fma_layer();
        let cross = HashMap::new();
        let v = LayerView { layer: &layer, cross: &cross, overrides: None };
        assert_eq!(v.width(ExprId(0)), 1); // Base witness read
        assert!(matches!(v.kind(ExprId(0)), NodeKind::Leaf(LeafClass::Dram { width: 1 })));
        assert!(matches!(v.kind(ExprId(3)), NodeKind::Mul(_)));
        assert!(matches!(v.kind(ExprId(4)), NodeKind::Add(_)));
    }

    #[test]
    fn add_sub_l0_widths_and_kinds_resolve() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let layer = &dag.layers[0];
        let v = LayerView { layer, cross: &cross, overrides: None };
        for i in 0..layer.exprs.len() {
            let e = ExprId(i as u32);
            let _ = v.width(e); // must not panic: resolvable via expr_field or cross
            match v.kind(e) {
                NodeKind::Leaf(_) | NodeKind::Add(_) | NodeKind::Mul(_) => {}
            }
        }
    }
}
