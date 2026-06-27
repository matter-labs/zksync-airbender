use cs::gkr_compiler::dag_ir::{DagLayer, ExprId, FieldKind, ReadPlace, Root, SourceKind};
use gkr_eval_isa::fwd::compile::expr_operand_field;
use gkr_eval_isa::fwd::isa::OperandField;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

// ── Public types ─────────────────────────────────────────────────────────────

/// Node classification: all six `SourceKind` variants + Expr variants + resolution-pruned.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NodeKind {
    /// `SourceKind::Read` — real DRAM access.
    Read,
    /// `SourceKind::Prior` before canonical extraction.
    ///
    /// Extracted instances rewrite Prior uses into direct edges to the producer
    /// expression and track reloadability in `OracleInstance::reloadable_values`.
    Prior,
    /// `SourceKind::VirtualSetup` — precomputed, zero DRAM traffic.
    VirtualSetup,
    /// Resolution-pruned expr — treated as a terminal with no DAG children.
    Special,
    /// `SourceKind::Constant | Challenge | LookupValue` — zero traffic.
    Literal,
    /// `Expr::Add`
    Add,
    /// `Expr::Mul`
    Mul,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OracleNode {
    pub id: u32,
    pub kind: NodeKind,
    /// Cell width: 4 for Ext operands, 1 for Base.
    pub width: u8,
    /// True iff the node incurs external DRAM read traffic.
    pub real_dram: bool,
    /// Remapped child node ids (empty for leaf/Special nodes).
    pub children: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OracleInstance {
    pub budget: usize,
    /// Root occurrence values in original root visitation order.
    ///
    /// Values may repeat when distinct output roots alias the same producer,
    /// e.g. through `Prior`; the occurrence identity is the index in this vector.
    pub roots: Vec<u32>,
    /// Root/output value ids that may be reloaded after their root has completed.
    pub reloadable_values: Vec<u32>,
    /// All reachable nodes in topological order (child id < parent id).
    pub nodes: Vec<OracleNode>,
}

// ── extract_instance ─────────────────────────────────────────────────────────

/// Lower a `DagLayer` DAG to a solver `OracleInstance`.
///
/// Nodes are the transitive closure of `Root::Output` top exprs, **topologically
/// ordered so every child id < its parent id** (post-order DFS). New contiguous
/// ids (topo position) are assigned. `roots` lists the remapped top-expr ids in
/// original root visitation order.
///
/// Resolution-prune guard — **byte-identical to Task-2's `dag_traffic_floor`**:
/// ```
/// layer.resolutions.contains_key(&ExprId(eid))
/// ```
/// A resolution-pruned expr becomes a `NodeKind::Special` **terminal with
/// `children: vec![]`** — do NOT descend into its children (spec §3 class 3).
pub fn extract_instance(
    layer: &DagLayer,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
) -> OracleInstance {
    extract_instance_impl(layer, cross, budget, false)
}

/// Like [`extract_instance`] but does NOT treat `Cache`-sink values as separate
/// scheduling roots. A cache value is an intra-unit intermediate: it is computed once
/// inline while its owning relation evaluates its num/den (the `Prior` rewire already
/// routes those cones through it), and materialized (a free streamed write the cost model
/// does not charge) for the backward pass. Excluding it as a root leaves exactly the
/// non-cache claim-root set, so the scheduler orders relations — not phantom cache atoms.
///
/// Sound here because every cache value's in-layer consumers belong to a SINGLE relation
/// (asserted by `dual_use_cache_consumers_share_relation`) and every cache value has an
/// in-layer consumer (no orphans), so excluding it never drops a reachable value.
pub fn extract_instance_materialized_cache(
    layer: &DagLayer,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
) -> OracleInstance {
    extract_instance_impl(layer, cross, budget, true)
}

fn extract_instance_impl(
    layer: &DagLayer,
    cross: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
    materialize_cache: bool,
) -> OracleInstance {
    use cs::gkr_compiler::dag_ir::{Expr, Root, SinkKind};
    use std::collections::HashSet;

    // --- Phase 1: collect Output-root top exprs in original order ---
    // With `materialize_cache`, Cache-sink Output roots are NOT scheduling roots — they
    // are reached inline as shared intermediates via their consumers' `Prior` edges.
    let top_exprs: Vec<u32> = layer
        .roots
        .iter()
        .filter_map(|r| match r {
            Root::Output { expr, sink } => {
                if materialize_cache
                    && matches!(layer.sinks[sink.0 as usize].kind, SinkKind::Cache { .. })
                {
                    None
                } else {
                    Some(expr.0)
                }
            }
            Root::Constraint { .. } => None,
        })
        .collect();

    // --- Phase 2: post-order DFS to build topo-ordered list of reachable eids ---
    // Post-order: children are pushed onto topo_order before their parent.
    // Result: child ids (topo positions) < parent ids → invariant satisfied.
    let mut visited: HashSet<u32> = HashSet::new();
    let mut topo_order: Vec<u32> = Vec::new();

    fn prior_target_expr(layer: &DagLayer, eid: u32) -> Option<u32> {
        if layer.resolutions.contains_key(&ExprId(eid)) {
            return None;
        }
        let Expr::Source(sid) = &layer.exprs[eid as usize] else {
            return None;
        };
        let SourceKind::Prior { id } = &layer.sources[sid.0 as usize].kind else {
            return None;
        };
        let Root::Output { expr, .. } = layer.roots[id.0 as usize] else {
            panic!("validated DAG must have Prior target an Output root");
        };
        Some(expr.0)
    }

    fn dfs(eid: u32, layer: &DagLayer, visited: &mut HashSet<u32>, topo_order: &mut Vec<u32>) {
        if !visited.insert(eid) {
            return;
        }
        // Resolution-pruned → Special terminal.
        // GUARD IS IDENTICAL TO floor.rs: layer.resolutions.contains_key(&ExprId(eid))
        if layer.resolutions.contains_key(&ExprId(eid)) {
            topo_order.push(eid);
            return; // do NOT descend
        }
        if let Some(target) = prior_target_expr(layer, eid) {
            dfs(target, layer, visited, topo_order);
            return;
        }
        match &layer.exprs[eid as usize] {
            Expr::Source(_) => {
                // Leaf — no children to visit.
            }
            Expr::Add(ch) | Expr::Mul(ch) => {
                // Visit children first (post-order).
                for child in ch.iter() {
                    dfs(child.0, layer, visited, topo_order);
                }
            }
        }
        topo_order.push(eid);
    }

    for &eid in &top_exprs {
        dfs(eid, layer, &mut visited, &mut topo_order);
    }

    // --- Phase 3: assign new contiguous ids (topo position = new_id) ---
    // old_eid → new_id; child appears before parent → child new_id < parent new_id.
    let mut remap: HashMap<u32, u32> = HashMap::with_capacity(topo_order.len());
    for (new_id, &old_eid) in topo_order.iter().enumerate() {
        remap.insert(old_eid, new_id as u32);
    }

    let remap_child = |child: ExprId| -> u32 {
        let target = prior_target_expr(layer, child.0).unwrap_or(child.0);
        remap[&target]
    };

    // --- Phase 4: emit OracleNodes ---
    let mut nodes: Vec<OracleNode> = Vec::with_capacity(topo_order.len());
    for &old_eid in &topo_order {
        let new_id = remap[&old_eid];

        // Resolution-pruned → Special terminal with empty children.
        // Guard mirrors floor.rs exactly: &ExprId(eid), NOT a bare u32.
        if layer.resolutions.contains_key(&ExprId(old_eid)) {
            let f = expr_operand_field(layer, ExprId(old_eid), cross);
            let width = if f == OperandField::Ext { 4 } else { 1 };
            nodes.push(OracleNode {
                id: new_id,
                kind: NodeKind::Special,
                width,
                real_dram: false,
                children: vec![],
            });
            continue;
        }

        let (kind, children) = match &layer.exprs[old_eid as usize] {
            Expr::Source(sid) => {
                // All six SourceKind variants classified:
                let kind = match &layer.sources[sid.0 as usize].kind {
                    SourceKind::Read { .. } => NodeKind::Read,
                    SourceKind::Prior { .. } => unreachable!("Prior source exprs are edge aliases"),
                    SourceKind::VirtualSetup { .. } => NodeKind::VirtualSetup,
                    SourceKind::Constant { .. }
                    | SourceKind::Challenge { .. }
                    | SourceKind::LookupValue { .. } => NodeKind::Literal,
                };
                (kind, vec![])
            }
            Expr::Add(ch) => {
                let remapped: Vec<u32> = ch.iter().map(|&c| remap_child(c)).collect();
                (NodeKind::Add, remapped)
            }
            Expr::Mul(ch) => {
                let remapped: Vec<u32> = ch.iter().map(|&c| remap_child(c)).collect();
                (NodeKind::Mul, remapped)
            }
        };

        let f = expr_operand_field(layer, ExprId(old_eid), cross);
        let width = if f == OperandField::Ext { 4 } else { 1 };
        let real_dram = matches!(kind, NodeKind::Read);

        nodes.push(OracleNode {
            id: new_id,
            kind,
            width,
            real_dram,
            children,
        });
    }

    // --- Phase 5: build remapped roots list in original visitation order ---
    let roots: Vec<u32> = top_exprs
        .iter()
        .map(|&eid| {
            let target = prior_target_expr(layer, eid).unwrap_or(eid);
            remap[&target]
        })
        .collect();
    let mut reloadable_values: Vec<u32> = visited
        .iter()
        .filter_map(|&eid| {
            let target = prior_target_expr(layer, eid)?;
            remap.get(&target).copied()
        })
        .collect();
    reloadable_values.sort_unstable();
    reloadable_values.dedup();

    OracleInstance {
        budget,
        roots,
        reloadable_values,
        nodes,
    }
}

// ── relation_units ───────────────────────────────────────────────────────────

/// Per-Output-root-occurrence "scheduling unit" assignment, aligned 1:1 with
/// `extract_instance`'s `roots` occurrence order (Output roots in `layer.roots`
/// order; `Root::Constraint` roots are not occurrences and are skipped, exactly
/// as `extract_instance` does).
///
/// Two occurrences share a unit id iff their `RootOrigin` has the same
/// `(group, relation_index)` — i.e. they are the num/den (and privately-shared
/// fold) of one gate relation, which is the atomic scheduling unit (asserted
/// single-relation by `dual_use_cache_consumers_share_relation`). Output roots
/// with no origin (cache / materialization-only roots — `origins` is sparse and
/// omits them) each get a fresh singleton unit.
///
/// Consumed by the group-atomic decoder so a relation's roots stay contiguous in
/// the schedule, keeping their shared fold co-resident. An all-singleton
/// assignment decodes identically to the flat decoder, so passing an empty slice
/// (or all-distinct units) is a no-op relative to the unconstrained order.
pub fn relation_units(layer: &DagLayer) -> Vec<u32> {
    relation_units_impl(layer, false)
}

/// `relation_units` aligned with [`extract_instance_materialized_cache`]: Cache-sink
/// Output roots are skipped (they are not scheduling atoms), so the result lines up
/// with the materialized-cache `roots` occurrence order. With cache roots removed, the
/// remaining roots are all claim-bearing, so units are grouped purely by relation.
pub fn relation_units_materialized_cache(layer: &DagLayer) -> Vec<u32> {
    relation_units_impl(layer, true)
}

fn relation_units_impl(layer: &DagLayer, materialize_cache: bool) -> Vec<u32> {
    use cs::gkr_compiler::dag_ir::{Root, RootGroup, RootId, SinkKind};

    let mut unit_of = Vec::new();
    let mut key_to_unit: HashMap<(RootGroup, usize), u32> = HashMap::new();
    let mut next_unit = 0u32;
    for (idx, root) in layer.roots.iter().enumerate() {
        let Root::Output { sink, .. } = root else {
            continue; // Constraint roots are not occurrences (see extract_instance).
        };
        if materialize_cache
            && matches!(layer.sinks[sink.0 as usize].kind, SinkKind::Cache { .. })
        {
            continue; // cache value is an inline intra-unit intermediate, not an atom
        }
        let unit = match layer.origins.get(&RootId(idx as u32)) {
            Some(origin) => *key_to_unit
                .entry((origin.group.clone(), origin.relation_index))
                .or_insert_with(|| {
                    let u = next_unit;
                    next_unit += 1;
                    u
                }),
            None => {
                // Cache / materialization-only root: own singleton unit.
                let u = next_unit;
                next_unit += 1;
                u
            }
        };
        unit_of.push(unit);
    }
    unit_of
}

// ── distinct_live_values ─────────────────────────────────────────────────────

/// Upper bound on simultaneously-live distinct values.
///
/// Left-to-right sweep of `roots`. For each root index, the live set is the
/// set of node ids whose first-use index ≤ current root index and whose
/// last-use index ≥ current root index. Returns the maximum count.
pub fn distinct_live_values(inst: &OracleInstance) -> usize {
    use std::collections::HashSet;

    let n_roots = inst.roots.len();
    if n_roots == 0 {
        return 0;
    }

    // Map node id → inst.nodes index for O(1) child traversal.
    let id_to_idx: HashMap<u32, usize> = inst
        .nodes
        .iter()
        .enumerate()
        .map(|(i, n)| (n.id, i))
        .collect();

    // Compute first_use and last_use for every node id.
    let mut first_use: HashMap<u32, usize> = HashMap::new();
    let mut last_use: HashMap<u32, usize> = HashMap::new();

    for (root_idx, &root_id) in inst.roots.iter().enumerate() {
        let mut stack: Vec<u32> = vec![root_id];
        let mut seen: HashSet<u32> = HashSet::new();
        while let Some(nid) = stack.pop() {
            if !seen.insert(nid) {
                continue;
            }
            first_use.entry(nid).or_insert(root_idx);
            let lu = last_use.entry(nid).or_insert(root_idx);
            if root_idx > *lu {
                *lu = root_idx;
            }
            if let Some(&idx) = id_to_idx.get(&nid) {
                for &child in &inst.nodes[idx].children {
                    stack.push(child);
                }
            }
        }
    }

    // Sweep: at each root index, count nodes alive (first_use ≤ idx ≤ last_use).
    let mut max_live = 0usize;
    for root_idx in 0..n_roots {
        let live = inst
            .nodes
            .iter()
            .filter(|n| {
                let fu = first_use.get(&n.id).copied().unwrap_or(usize::MAX);
                let lu = last_use.get(&n.id).copied().unwrap_or(0);
                fu <= root_idx && lu >= root_idx
            })
            .count();
        if live > max_live {
            max_live = live;
        }
    }
    max_live
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, DagLayer, Expr, ExprId, FieldKind, ReadPlace, Root, RootId, SinkId,
        SinkInfo, SinkKind, SourceId, SourceInfo, SourceKind,
    };
    use std::collections::BTreeMap;

    fn tests_support_two_roots_one_prior() -> (DagLayer, HashMap<ReadPlace, FieldKind>) {
        let src_ext = SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::LayerOutput {
                    layer: 1,
                    offset: 0,
                },
            },
        };
        let src_base_a = SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::BaseLayerWitness { column: 3 },
            },
        };
        let src_prior = SourceInfo {
            kind: SourceKind::Prior { id: RootId(0) },
        };
        let src_base_b = SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::BaseLayerWitness { column: 4 },
            },
        };

        let layer = DagLayer {
            sources: vec![src_ext, src_base_a, src_prior, src_base_b],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Add(vec![ExprId(0), ExprId(1)]),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
                Expr::Add(vec![ExprId(3), ExprId(4)]),
            ],
            roots: vec![
                Root::Output {
                    expr: ExprId(2),
                    sink: SinkId(0),
                },
                Root::Output {
                    expr: ExprId(5),
                    sink: SinkId(1),
                },
            ],
            sinks: vec![
                SinkInfo {
                    kind: SinkKind::Cache {
                        layer: 0,
                        offset: 0,
                    },
                    field: FieldKind::Ext,
                },
                SinkInfo {
                    kind: SinkKind::Inner {
                        layer: 0,
                        offset: 1,
                    },
                    field: FieldKind::Ext,
                },
            ],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        };

        let mut cross = HashMap::new();
        cross.insert(
            ReadPlace::LayerOutput {
                layer: 1,
                offset: 0,
            },
            FieldKind::Ext,
        );
        (layer, cross)
    }

    #[test]
    fn extract_topo_orders_children_before_parents_and_flags_dram() {
        let (layer, cross) = tests_support_two_roots_one_prior();
        let inst = extract_instance(&layer, &cross, 16);
        // every child id strictly less than its parent id
        for n in &inst.nodes {
            for &c in &n.children {
                assert!(c < n.id, "child {c} must precede parent {}", n.id);
            }
        }
        // real_dram is exactly external Read; Prior is an edge alias to a materialized root.
        let dram: Vec<_> = inst
            .nodes
            .iter()
            .filter(|n| n.real_dram)
            .map(|n| n.kind)
            .collect();
        assert!(dram.iter().all(|k| matches!(k, NodeKind::Read)));
        assert!(
            inst.nodes
                .iter()
                .all(|n| !matches!(n.kind, NodeKind::Prior)),
            "Prior must not survive extraction as a source-like value node"
        );
        assert_eq!(
            inst.reloadable_values,
            vec![inst.roots[0]],
            "Prior target root must be marked reloadable after materialization"
        );
        // ext Read has width 4, base Read width 1
        assert!(inst
            .nodes
            .iter()
            .any(|n| matches!(n.kind, NodeKind::Read) && n.width == 4));
        assert!(inst
            .nodes
            .iter()
            .any(|n| matches!(n.kind, NodeKind::Read) && n.width == 1));
    }

    #[test]
    fn instance_roundtrips_through_json() {
        let (layer, cross) = crate::s3_gap::floor::tests_support_two_reads_one_prior();
        let inst = extract_instance(&layer, &cross, 16);
        let s = serde_json::to_string(&inst).unwrap();
        let back: OracleInstance = serde_json::from_str(&s).unwrap();
        assert_eq!(back.budget, 16);
        assert_eq!(back.nodes.len(), inst.nodes.len());
        assert_eq!(back.roots, inst.roots);
    }

    /// Tests the NON-TRIVIAL "carry" case: a node live across a root that does
    /// not itself use it.
    ///
    /// Synthetic 3-root DAG (all base-field reads, no cross-layer entries):
    ///
    ///   e0 = Source(Read, BaseLayerWitness{column:0})  ← shared leaf
    ///   e1 = Source(Read, BaseLayerWitness{column:1})
    ///   e2 = Source(Read, BaseLayerWitness{column:2})
    ///   e3 = Source(Read, BaseLayerWitness{column:3})
    ///   e4 = Source(Read, BaseLayerWitness{column:4})
    ///   e5 = Add([e0, e1])   ← root 0 top
    ///   e6 = Add([e2, e3])   ← root 1 top  (does NOT use e0)
    ///   e7 = Add([e0, e4])   ← root 2 top  (reuses e0)
    ///
    /// Post-order DFS builds topo_order = [e0,e1,e5, e2,e3,e6, e4,e7]
    ///   new ids:  e0→0, e1→1, e5→2, e2→3, e3→4, e6→5, e4→6, e7→7
    ///   roots (remapped): [2, 5, 7]
    ///   children: node2→[0,1], node5→[3,4], node7→[0,6]
    ///
    /// `distinct_live_values` first/last use (DFS walk per root_idx):
    ///   node 0: first=0, last=2   ← e0 first used at root 0, last at root 2
    ///   node 1: first=0, last=0
    ///   node 2: first=0, last=0
    ///   node 3: first=1, last=1
    ///   node 4: first=1, last=1
    ///   node 5: first=1, last=1
    ///   node 6: first=2, last=2
    ///   node 7: first=2, last=2
    ///
    /// Sweep — live counts:
    ///   root_idx=0: {0,1,2} = 3
    ///   root_idx=1: {0,3,4,5} = 4  ← node 0 is the "carry" (first=0 ≤ 1 ≤ last=2)
    ///   root_idx=2: {0,6,7} = 3
    ///   max = 4
    ///
    /// Without carry the per-root max would be 3 (3 nodes per subtree);
    /// carry (node 0 live at root 1 even though root 1 doesn't use it) raises it to 4.
    #[test]
    fn distinct_live_values_counts_carry_across_roots() {
        use cs::gkr_compiler::dag_ir::{
            BatchingOrder, Expr, ExprId, FieldKind, ReadPlace, Root, SinkId, SinkInfo, SinkKind,
            SourceId, SourceInfo, SourceKind,
        };
        use std::collections::BTreeMap;

        // Five base-field reads, no cross-layer entries needed.
        let make_read = |col: usize| SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::BaseLayerWitness { column: col },
            },
        };

        let layer = DagLayer {
            sources: vec![
                make_read(0), // src 0 → e0 (shared)
                make_read(1), // src 1 → e1
                make_read(2), // src 2 → e2
                make_read(3), // src 3 → e3
                make_read(4), // src 4 → e4
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),             // e0
                Expr::Source(SourceId(1)),             // e1
                Expr::Source(SourceId(2)),             // e2
                Expr::Source(SourceId(3)),             // e3
                Expr::Source(SourceId(4)),             // e4
                Expr::Add(vec![ExprId(0), ExprId(1)]), // e5 = root 0
                Expr::Add(vec![ExprId(2), ExprId(3)]), // e6 = root 1
                Expr::Add(vec![ExprId(0), ExprId(4)]), // e7 = root 2
            ],
            roots: vec![
                Root::Output {
                    expr: ExprId(5),
                    sink: SinkId(0),
                },
                Root::Output {
                    expr: ExprId(6),
                    sink: SinkId(1),
                },
                Root::Output {
                    expr: ExprId(7),
                    sink: SinkId(2),
                },
            ],
            sinks: vec![
                SinkInfo {
                    kind: SinkKind::Inner {
                        layer: 0,
                        offset: 0,
                    },
                    field: FieldKind::Base,
                },
                SinkInfo {
                    kind: SinkKind::Inner {
                        layer: 0,
                        offset: 1,
                    },
                    field: FieldKind::Base,
                },
                SinkInfo {
                    kind: SinkKind::Inner {
                        layer: 0,
                        offset: 2,
                    },
                    field: FieldKind::Base,
                },
            ],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        };

        let cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
        let inst = extract_instance(&layer, &cross, 16);

        // Sanity: three roots, eight nodes (5 leaves + 3 Add nodes).
        assert_eq!(inst.roots.len(), 3, "expected 3 roots");
        assert_eq!(inst.nodes.len(), 8, "expected 8 nodes (5 leaves + 3 Add)");

        // Hand-derived expected value: 4 (at root_idx=1, carry node e0 is live).
        // Per-root subtree size is 3 for every root; without carry the max would be 3.
        // Carry raises it to 4.
        assert_eq!(
            distinct_live_values(&inst),
            4,
            // Derivation: node 0 (e0) has first_use=0, last_use=2, so it is live at \
            // root_idx=1 (0 ≤ 1 ≤ 2) even though root 1 does not reference e0. \
            // live@root_idx=1: {{0, 3, 4, 5}} = 4 > per-root-subtree max of 3.
        );
    }

    #[test]
    fn resolution_pruned_expr_yields_special_terminal() {
        // Build a layer with one resolution-pruned expr:
        //   expr 0: Source(SourceId(0)) = Read{LayerOutput{layer:0,offset:0}}
        //   expr 1: Mul([ExprId(0)]) — PRUNED via resolutions → Special terminal
        //   root:   Output { expr: ExprId(1) }
        //
        // Because expr 1 is pruned, we do NOT descend into its children.
        // Only ONE node is emitted: the Special terminal for expr 1.
        use cs::gkr_compiler::dag_ir::{
            BatchingOrder, Expr, ExprId, RangeWidth, ResolutionStrategy, Root, SinkId, SinkInfo,
            SinkKind, SourceId, SourceInfo, SourceKind,
        };
        use std::collections::BTreeMap;

        let src = SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::LayerOutput {
                    layer: 0,
                    offset: 0,
                },
            },
        };
        let e_src = Expr::Source(SourceId(0));
        let e_mul = Expr::Mul(vec![ExprId(0)]);

        let mut resolutions = BTreeMap::new();
        resolutions.insert(
            ExprId(1),
            ResolutionStrategy::PeekSingleColumn {
                set_index: 0,
                width: RangeWidth::Bits16,
            },
        );

        let layer = DagLayer {
            sources: vec![src],
            exprs: vec![e_src, e_mul],
            roots: vec![Root::Output {
                expr: ExprId(1),
                sink: SinkId(0),
            }],
            sinks: vec![SinkInfo {
                kind: SinkKind::Inner {
                    layer: 0,
                    offset: 0,
                },
                field: FieldKind::Base,
            }],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions,
        };

        let cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
        let inst = extract_instance(&layer, &cross, 8);

        // The pruned expr (eid=1) is the root. We do NOT descend → only 1 node.
        assert_eq!(
            inst.nodes.len(),
            1,
            "only the Special terminal node should be emitted"
        );
        let node = &inst.nodes[0];
        assert!(
            matches!(node.kind, NodeKind::Special),
            "pruned expr must yield NodeKind::Special, got {:?}",
            node.kind
        );
        assert!(
            node.children.is_empty(),
            "Special terminal must have children: vec![]"
        );
        assert!(!node.real_dram, "Special must not be real_dram");
    }

    #[test]
    fn materialized_cache_excludes_cache_roots_keeps_reads() {
        // tests_support_two_roots_one_prior: root0 = Cache(Add(e0,e1)), root1 =
        // Inner(Add(Prior(root0), e3)). The cache value (e2) feeds root1 via Prior.
        let (layer, cross) = tests_support_two_roots_one_prior();

        // Cache-as-root (current default): the cache value is its own scheduling root.
        let base = extract_instance(&layer, &cross, 16);
        assert_eq!(base.roots.len(), 2, "default: cache value is a separate root");

        // Cache-materialized: the cache value is NOT a root — only its consuming relation
        // (root1) is. It is still reachable inline (root1's cone routes through it).
        let mat = extract_instance_materialized_cache(&layer, &cross, 16);
        assert_eq!(mat.roots.len(), 1, "materialized: cache value is not a root");

        // Reads are IDENTICAL — materialization adds no reads (the intermediate is computed
        // for the consumer's num/den anyway; the write is free).
        let read_cells = |inst: &OracleInstance| -> u64 {
            inst.nodes
                .iter()
                .filter(|n| n.real_dram)
                .map(|n| n.width as u64)
                .sum()
        };
        assert_eq!(
            read_cells(&base),
            read_cells(&mat),
            "cache materialization must not change the read-leaf set"
        );
        // The cache value's cone is present in the materialized instance (not dropped).
        assert!(
            mat.nodes.len() >= base.nodes.len() - 1,
            "the cache value's cone must remain (folded into the consumer), not be dropped"
        );
    }

    #[test]
    fn relation_units_groups_pair_roots_and_singletons_cache() {
        use cs::gkr_compiler::dag_ir::{
            BatchingOrder, Expr, ExprId, RootGroup, RootId, RootOrigin, RootSlot, SinkId, SinkInfo,
            SinkKind, SourceId, SourceInfo, SourceKind,
        };
        use std::collections::BTreeMap;

        // 5 layer roots in visitation order (expr bodies are irrelevant to grouping):
        //   r0 Output  origin (Gates, rel 0, Output(0))  ─┐ num/den of relation 0
        //   r1 Output  origin (Gates, rel 0, Output(1))  ─┘ → SAME unit
        //   r2 Output  NO origin (cache / materialization-only) → singleton
        //   r3 Constraint                                  → skipped (not an occurrence)
        //   r4 Output  origin (Gates, rel 1, Output(0))    → distinct unit
        // Output occurrences (matching extract_instance) are [r0, r1, r2, r4].
        // Units assigned in encounter order: rel0→0, cache→1, rel1→2 ⇒ [0, 0, 1, 2].
        let src = SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::BaseLayerWitness { column: 0 },
            },
        };
        let out = |s: u32| Root::Output {
            expr: ExprId(0),
            sink: SinkId(s),
        };
        let mut origins = BTreeMap::new();
        origins.insert(
            RootId(0),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Output(0),
            },
        );
        origins.insert(
            RootId(1),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Output(1),
            },
        );
        origins.insert(
            RootId(4),
            RootOrigin {
                group: RootGroup::Gates,
                relation_index: 1,
                slot: RootSlot::Output(0),
            },
        );
        let layer = DagLayer {
            sources: vec![src],
            exprs: vec![Expr::Source(SourceId(0))],
            roots: vec![out(0), out(0), out(0), Root::Constraint { expr: ExprId(0) }, out(0)],
            sinks: vec![SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset: 0 },
                field: FieldKind::Base,
            }],
            batching: BatchingOrder { roots: vec![] },
            origins,
            resolutions: BTreeMap::new(),
        };

        assert_eq!(relation_units(&layer), vec![0, 0, 1, 2]);
    }
}
