//! Value-preserving DAG simplification (spec:
//! .agents/specs/2026-07-04-gkr-dag-simplify-design.md). Memoized bottom-up
//! rebuild into a fresh unflattened arena; reachability and remapping include
//! the `SourceKind::LookupValue::query` edge. Fenced = `resolutions` keys.

use std::collections::{BTreeMap, HashMap, HashSet};

use super::{ArenaBuilder, DagCircuit, DagLayer, Expr, ExprId, Root, SourceKind};

pub fn simplify_circuit(dag: DagCircuit) -> DagCircuit {
    DagCircuit {
        layers: dag.layers.iter().map(simplify_layer).collect(),
        globals: dag.globals,
    }
}

pub(crate) fn simplify_layer(layer: &DagLayer) -> DagLayer {
    let mut rb = Rebuild {
        arena: ArenaBuilder::with_flatten(false),
        map: HashMap::new(),
        layer,
        // Fence set = the layer's own `resolutions` keys (the arena's private
        // fence set does not survive lowering). No rewrites read this yet
        // (Task 5); it is populated here so the field exists on `Rebuild`
        // ahead of that use.
        fenced: layer.resolutions.keys().copied().collect(),
    };
    let roots: Vec<Root> = layer
        .roots
        .iter()
        .map(|r| Root {
            expr: rb.rebuild(r.expr),
            materialize: r.materialize.clone(),
            claim: r.claim.clone(),
        })
        .collect();
    let mut resolutions = BTreeMap::new();
    for (old, strat) in &layer.resolutions {
        // Fenced keys must be root-reachable to survive rewrites; if a key
        // is NOT in the memo map, its subtree was never rebuilt (dead
        // resolution) — drop it rather than panicking.
        let Some(&new) = rb.map.get(old) else {
            continue;
        };
        if let Some(existing) = resolutions.insert(new, strat.clone()) {
            assert_eq!(
                &existing, strat,
                "dag_ir simplify: resolution CSE collision at {:?}",
                new
            );
        }
    }
    DagLayer {
        sources: rb.arena.sources().to_vec(),
        exprs: rb.arena.exprs().to_vec(),
        roots,
        batching: layer.batching.clone(),
        resolutions,
    }
}

struct Rebuild<'a> {
    arena: ArenaBuilder,
    map: HashMap<ExprId, ExprId>,
    layer: &'a DagLayer,
    /// Fenced (resolution-keyed) old `ExprId`s. Unused by this skeleton (no
    /// rewrites yet); read by later tasks that must not rewrite across a
    /// resolution-keyed fold-leaf boundary.
    #[allow(dead_code)]
    fenced: HashSet<ExprId>,
}

impl Rebuild<'_> {
    fn rebuild(&mut self, old: ExprId) -> ExprId {
        if let Some(&new) = self.map.get(&old) {
            return new;
        }
        let new = match self.layer.exprs[old.0 as usize].clone() {
            Expr::Source(sid) => {
                let kind = match self.layer.sources[sid.0 as usize].kind.clone() {
                    SourceKind::LookupValue {
                        kind,
                        set_index,
                        query,
                    } => {
                        let query = self.rebuild(query);
                        SourceKind::LookupValue {
                            kind,
                            set_index,
                            query,
                        }
                    }
                    other => other,
                };
                let sid = self.arena.intern_source(kind);
                self.arena.source_expr(sid)
            }
            Expr::Add(children) => {
                let ch: Vec<ExprId> = children.iter().map(|&c| self.rebuild(c)).collect();
                self.arena.add(ch)
            }
            Expr::Mul(children) => {
                let ch: Vec<ExprId> = children.iter().map(|&c| self.rebuild(c)).collect();
                self.arena.mul(ch)
            }
        };
        self.map.insert(old, new);
        new
    }
}

// ── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr_compiler::dag_ir::{BatchingOrder, LookupValueKind, ResolutionStrategy};

    /// Hand-build a `DagLayer` from an in-progress `ArenaBuilder` plus roots and
    /// resolutions; `batching` is irrelevant to these tests so it's left empty.
    fn layer_of(
        arena: ArenaBuilder,
        roots: Vec<Root>,
        resolutions: BTreeMap<ExprId, ResolutionStrategy>,
    ) -> DagLayer {
        DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots,
            batching: BatchingOrder { roots: vec![] },
            resolutions,
        }
    }

    /// DCE: an expr unreachable from any root/query edge does not survive the rebuild.
    #[test]
    fn rebuild_drops_unreachable() {
        let mut a = ArenaBuilder::with_flatten(false);
        let c1 = {
            let s = a.intern_source(SourceKind::Constant { value: 7 });
            a.source_expr(s)
        };
        let dead = {
            let s = a.intern_source(SourceKind::Constant { value: 9 });
            a.source_expr(s)
        };
        let _ = a.add(vec![dead, dead]); // unreachable
        let root = Root {
            expr: c1,
            materialize: None,
            claim: None,
        };
        let layer = layer_of(a, vec![root], BTreeMap::new());
        let out = simplify_layer(&layer);
        assert_eq!(out.exprs.len(), 1, "only the root constant survives: {:?}", out.exprs);
        assert_eq!(out.roots.len(), 1);
    }

    /// LookupValue.query is remapped AND keeps its subtree alive.
    #[test]
    fn lookup_query_is_remapped_and_reachable() {
        let mut a = ArenaBuilder::with_flatten(false);
        let q = {
            let s = a.intern_source(SourceKind::Constant { value: 3 });
            a.source_expr(s)
        };
        let lv = {
            let s = a.intern_source(SourceKind::LookupValue {
                kind: LookupValueKind::RangeCheck16Index,
                set_index: 0,
                query: q,
            });
            a.source_expr(s)
        };
        let root = Root {
            expr: lv,
            materialize: None,
            claim: None,
        };
        let layer = layer_of(a, vec![root], BTreeMap::new());
        let out = simplify_layer(&layer);
        // find the LookupValue source in the output and follow its query
        let lv_src = out
            .sources
            .iter()
            .find_map(|s| match &s.kind {
                SourceKind::LookupValue { query, .. } => Some(*query),
                _ => None,
            })
            .expect("LookupValue survives");
        assert!(
            matches!(&out.exprs[lv_src.0 as usize], Expr::Source(_)),
            "query edge points at the rebuilt constant"
        );
    }
}
