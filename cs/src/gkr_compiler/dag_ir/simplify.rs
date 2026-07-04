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

/// Consumer-edge fan-out over root-reachable nodes only: per-edge counts
/// (repeats count) for Add/Mul parent→child edges, each `Root.expr`
/// occurrence (once per root), and each reachable `LookupValue.query` edge.
/// Reachability traverses children AND query edges; dead arena nodes never
/// appear in the result.
fn fan_out(layer: &DagLayer) -> HashMap<ExprId, usize> {
    let mut counts: HashMap<ExprId, usize> = HashMap::new();
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut worklist: Vec<ExprId> = Vec::new();
    for root in &layer.roots {
        *counts.entry(root.expr).or_insert(0) += 1;
        if seen.insert(root.expr) {
            worklist.push(root.expr);
        }
    }
    while let Some(id) = worklist.pop() {
        match &layer.exprs[id.0 as usize] {
            Expr::Add(children) | Expr::Mul(children) => {
                for &c in children {
                    *counts.entry(c).or_insert(0) += 1;
                    if seen.insert(c) {
                        worklist.push(c);
                    }
                }
            }
            Expr::Source(sid) => {
                if let SourceKind::LookupValue { query, .. } = &layer.sources[sid.0 as usize].kind {
                    *counts.entry(*query).or_insert(0) += 1;
                    if seen.insert(*query) {
                        worklist.push(*query);
                    }
                }
            }
        }
    }
    counts
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
        fan_out: fan_out(layer),
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
    /// Fenced (resolution-keyed) old `ExprId`s: rewrites must not cross a
    /// resolution-keyed fold-leaf boundary (self-fence guard in Add/Mul, plus
    /// later tasks' const-fold/collapse rewrites).
    fenced: HashSet<ExprId>,
    /// Consumer-edge counts over the OLD layer, used to decide fan-out==1
    /// flatten in the Add/Mul arms below.
    fan_out: HashMap<ExprId, usize>,
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
                // SELF-FENCE GUARD: a fenced node skips all rewrites (later
                // tasks add more here) — rebuild children only, no flatten.
                if self.fenced.contains(&old) {
                    let ch: Vec<ExprId> = children.iter().map(|&c| self.rebuild(c)).collect();
                    self.arena.add(ch)
                } else {
                    let mut flat: Vec<ExprId> = Vec::with_capacity(children.len());
                    for &c in &children {
                        let inline = matches!(self.layer.exprs[c.0 as usize], Expr::Add(_))
                            && self.fan_out[&c] == 1
                            && !self.fenced.contains(&c);
                        if inline {
                            if let Expr::Add(gc) = self.layer.exprs[c.0 as usize].clone() {
                                // Rebuild grandchildren directly; the child
                                // node is DCE'd (never inserted into the new
                                // arena).
                                flat.extend(gc.iter().map(|&g| self.rebuild(g)));
                            }
                        } else {
                            flat.push(self.rebuild(c));
                        }
                    }
                    self.arena.add(flat)
                }
            }
            Expr::Mul(children) => {
                if self.fenced.contains(&old) {
                    let ch: Vec<ExprId> = children.iter().map(|&c| self.rebuild(c)).collect();
                    self.arena.mul(ch)
                } else {
                    let mut flat: Vec<ExprId> = Vec::with_capacity(children.len());
                    for &c in &children {
                        let inline = matches!(self.layer.exprs[c.0 as usize], Expr::Mul(_))
                            && self.fan_out[&c] == 1
                            && !self.fenced.contains(&c);
                        if inline {
                            if let Expr::Mul(gc) = self.layer.exprs[c.0 as usize].clone() {
                                flat.extend(gc.iter().map(|&g| self.rebuild(g)));
                            }
                        } else {
                            flat.push(self.rebuild(c));
                        }
                    }
                    self.arena.mul(flat)
                }
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

    /// Three distinct `Constant` sources standing in for read-like leaves
    /// (no folding exists yet, so constants are fine for flatten/CSE tests).
    fn three_read_like_sources(a: &mut ArenaBuilder) -> (ExprId, ExprId, ExprId) {
        let mut mk = |value: u32| {
            let s = a.intern_source(SourceKind::Constant { value });
            a.source_expr(s)
        };
        (mk(101), mk(102), mk(103))
    }

    /// fan-out==1 nested Add flattens; the association-invariant dup merges via CSE.
    #[test]
    fn flatten_fanout1_and_cse_associations() {
        let mut a = ArenaBuilder::with_flatten(false);
        let (x, y, z) = three_read_like_sources(&mut a);
        let xy = a.add(vec![x, y]);
        let n1 = a.add(vec![xy, z]); // Add(Add(x,y), z)
        let yz = a.add(vec![y, z]);
        let n2 = a.add(vec![x, yz]); // Add(x, Add(y,z))
        let roots = vec![
            Root {
                expr: n1,
                materialize: None,
                claim: None,
            },
            Root {
                expr: n2,
                materialize: None,
                claim: None,
            },
        ];
        let layer = layer_of(a, roots, BTreeMap::new());
        let out = simplify_layer(&layer);
        assert_eq!(
            out.roots[0].expr, out.roots[1].expr,
            "both associations flatten to Add(x,y,z) and CSE-merge"
        );
    }

    /// fan-out>=2 nested Add is PRESERVED (sharing wins over flatten).
    #[test]
    fn shared_nested_add_is_preserved() {
        let mut a = ArenaBuilder::with_flatten(false);
        let (x, y, z) = three_read_like_sources(&mut a);
        let xy = a.add(vec![x, y]);
        let n1 = a.add(vec![xy, z]);
        let n2 = a.mul(vec![xy, xy]); // second+third consumers of xy
        let roots = vec![
            Root {
                expr: n1,
                materialize: None,
                claim: None,
            },
            Root {
                expr: n2,
                materialize: None,
                claim: None,
            },
        ];
        let layer = layer_of(a, roots, BTreeMap::new());
        let out = simplify_layer(&layer);
        match &out.exprs[out.roots[0].expr.0 as usize] {
            Expr::Add(ops) => assert_eq!(ops.len(), 2, "Add(xy, z) must keep nested xy, got {:?}", ops),
            other => panic!("expected Add, got {:?}", other),
        }
    }

    /// A fenced (resolution-keyed) Add child is never flattened even at fan-out 1.
    #[test]
    fn fenced_child_never_flattens() {
        let mut a = ArenaBuilder::with_flatten(false);
        let (x, y, z) = three_read_like_sources(&mut a);
        let leaf = a.add(vec![y, z]);
        let top = a.add(vec![x, leaf]);
        let mut res = BTreeMap::new();
        res.insert(leaf, ResolutionStrategy::PeekSetup);
        let layer = layer_of(
            a,
            vec![Root {
                expr: top,
                materialize: None,
                claim: None,
            }],
            res,
        );
        let out = simplify_layer(&layer);
        match &out.exprs[out.roots[0].expr.0 as usize] {
            Expr::Add(ops) => assert_eq!(ops.len(), 2, "fenced leaf survives as one operand"),
            other => panic!("expected Add, got {:?}", other),
        }
        assert_eq!(out.resolutions.len(), 1, "resolution key remapped, not dropped");
    }

    /// The fenced node ITSELF skips rewrites: a same-op fan-out-1 child INSIDE a
    /// fenced Add must not be flattened (spec §3: fenced = child-rebuild only).
    #[test]
    fn fenced_node_own_children_not_flattened() {
        let mut a = ArenaBuilder::with_flatten(false);
        let (x, y, z) = three_read_like_sources(&mut a);
        let inner = a.add(vec![y, z]); // fan-out 1 — would flatten if unfenced
        let leaf = a.add(vec![x, inner]); // the fenced fold leaf
        let mut res = BTreeMap::new();
        res.insert(leaf, ResolutionStrategy::PeekSetup);
        let layer = layer_of(
            a,
            vec![Root {
                expr: leaf,
                materialize: None,
                claim: None,
            }],
            res,
        );
        let out = simplify_layer(&layer);
        match &out.exprs[out.roots[0].expr.0 as usize] {
            Expr::Add(ops) => assert_eq!(ops.len(), 2, "fenced node keeps nested child, got {:?}", ops),
            other => panic!("expected fenced Add to survive, got {:?}", other),
        }
    }

    /// A `LookupValue.query` reference counts toward fan-out: a nested Add consumed
    /// once as a normal child and once as a query has fan-out 2 → must NOT flatten.
    #[test]
    fn query_edge_counts_toward_fanout() {
        let mut a = ArenaBuilder::with_flatten(false);
        let (x, y, z) = three_read_like_sources(&mut a);
        let shared = a.add(vec![y, z]);
        let top = a.add(vec![x, shared]); // consumer 1 (would flatten alone)
        let lv = {
            let s = a.intern_source(SourceKind::LookupValue {
                kind: LookupValueKind::RangeCheck16Index,
                set_index: 0,
                query: shared, // consumer 2
            });
            a.source_expr(s)
        };
        let roots = vec![
            Root {
                expr: top,
                materialize: None,
                claim: None,
            },
            Root {
                expr: lv,
                materialize: None,
                claim: None,
            },
        ];
        let layer = layer_of(a, roots, BTreeMap::new());
        let out = simplify_layer(&layer);
        match &out.exprs[out.roots[0].expr.0 as usize] {
            Expr::Add(ops) => assert_eq!(ops.len(), 2, "query edge must keep fan-out at 2, got {:?}", ops),
            other => panic!("expected Add, got {:?}", other),
        }
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
        // Both the Constant source and the LookupValue source survive.
        assert_eq!(out.sources.len(), 2, "query subtree stays alive: {:?}", out.sources);
        // Find the LookupValue source in the output and follow its query edge.
        let query = out
            .sources
            .iter()
            .find_map(|s| match &s.kind {
                SourceKind::LookupValue { query, .. } => Some(*query),
                _ => None,
            })
            .expect("LookupValue survives");
        // The rebuilt query edge must point at a genuinely-rebuilt Constant(3)
        // — not a stale old ExprId copied through without rebuild(query),
        // which in this layout would self-refer to the LookupValue node.
        assert_ne!(
            query, out.roots[0].expr,
            "query must not point at the LookupValue node itself"
        );
        let sid = match &out.exprs[query.0 as usize] {
            Expr::Source(sid) => *sid,
            other => panic!("query edge must point at a Source expr, got {:?}", other),
        };
        assert_eq!(
            out.sources[sid.0 as usize].kind,
            SourceKind::Constant { value: 3 },
            "query edge points at the rebuilt constant"
        );
    }
}
