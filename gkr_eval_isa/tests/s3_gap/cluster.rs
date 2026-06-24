//! `connected_root_cluster` — a `validate()`-preserving downscale of a real GKR
//! `DagLayer` to the Prior-connected cluster of a seed root.
//!
//! ## Why this exists (S3 gap experiment, Task 8b)
//!
//! Task 8a found the scheduling oracle is OVER-STRICT at the real budget (16) on
//! full 146-node layers: the MILP cannot prove optimality at that scale. The
//! decision was to DOWNSCALE — run the J-vs-E gate on SMALL connected
//! sub-instances that solve to OPTIMAL. The gate is robust to a *shared*
//! over-strictness (J and E use the identical model, so the systematic component
//! cancels), so the qualitative J-vs-E direction stays valid on a downscaled
//! instance — provided that instance still exhibits the order-sensitivity driver,
//! i.e. it preserves Prior-edge density.
//!
//! `connected_root_cluster` is THE tool that produces those small instances. It
//! shrinks a real layer while preserving (a) validity and (b) the Prior edges
//! that drive order sensitivity.
//!
//! ## What "Prior-connected cluster" means
//!
//! A `SourceKind::Prior { id }` in a root's expr cone references ANOTHER root (a
//! materialization-only *cache* root) by `RootId`. The cluster is the transitive
//! closure over Prior edges from the seed:
//!   start = {seed_root};
//!   for every root in the set, scan its expr cone for `Prior{id}` sources and
//!   add each target `id`; repeat to a fixpoint.
//! This yields a self-contained set of roots whose Prior references all stay
//! inside the set (no dangling Prior).
//!
//! ## Re-indexing the 7 cross-referencing `DagLayer` fields
//!
//! `DagLayer { sources, exprs, roots, sinks, batching, origins, resolutions }`.
//! Subsetting requires four consistent remaps (`old -> new` id maps) for exprs,
//! sources, sinks, and roots, then a rewrite of every cross-reference:
//! `Expr::Source(SourceId)`, `Expr::Add/Mul(Vec<ExprId>)`,
//! `Root::Output { expr, sink }`, `Root::Constraint { expr }`, and crucially
//! every `SourceKind::Prior { id: RootId }`. `batching.roots`, `origins`
//! (keyed by `RootId`), and `resolutions` (keyed by `ExprId`) are carried over
//! for the SURVIVING ids only, remapped; entries for excluded ids are dropped.
//!
//! ## validate() requirements satisfied here (validate.rs)
//!
//! - **F1**: a `Prior{id}` must reference an Output root whose sink is a `Cache`
//!   sink. The transitive closure pulls in exactly those cache-producer roots,
//!   and the sink-remap keeps their `Cache` sinks. We never break a Prior edge.
//! - **F2 caches-lead**: all cache roots must occupy LEADING indices. We emit
//!   surviving cache roots first (in original relative order), then the rest, so
//!   the new root order satisfies caches-lead.
//! - **batching membership**: cache roots must NOT appear in the batching order;
//!   every claim-bearing root must appear exactly once. We rebuild `batching`
//!   from the surviving claim-bearing roots in their new index order.
//! - **acyclicity / sink-written-once / field inference**: preserved because the
//!   expr/source subtrees are copied verbatim (only ids are renumbered) and each
//!   surviving sink is written by exactly one surviving root.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use cs::gkr_compiler::dag_ir::{
    BatchingOrder, DagLayer, Expr, ExprId, Root, RootId, SinkId, SinkInfo, SinkKind, SourceId,
    SourceInfo, SourceKind,
};

/// Keep only the roots in the Prior-connected cluster of `seed_root`, re-indexed
/// into a self-contained, `validate()`-passing `DagLayer`.
///
/// See the module docs for the closure + re-indexing algorithm and the
/// validate() requirements satisfied.
pub fn connected_root_cluster(layer: &DagLayer, seed_root: RootId) -> DagLayer {
    // ── 1. Transitive Prior closure over roots ───────────────────────────────
    // Start from the seed; for each root in the set, walk its expr cone and add
    // every `Prior{id}` target root; repeat to a fixpoint.
    let mut cluster: BTreeSet<RootId> = BTreeSet::new();
    let mut frontier: Vec<RootId> = vec![seed_root];
    while let Some(rid) = frontier.pop() {
        if !cluster.insert(rid) {
            continue;
        }
        // Walk the cone of this root, collecting Prior targets.
        for prior_target in prior_targets_in_cone(layer, rid) {
            if !cluster.contains(&prior_target) {
                frontier.push(prior_target);
            }
        }
    }

    // ── 2. Collect surviving exprs + sources reachable from cluster roots ─────
    // Reachability follows the SAME edges validate() uses: Add/Mul operands,
    // LookupValue.query, and Prior -> Root -> expr (but Prior stays inside the
    // cluster by construction, so we never escape the cluster).
    let mut keep_exprs: BTreeSet<u32> = BTreeSet::new();
    let mut keep_sources: BTreeSet<u32> = BTreeSet::new();
    for &rid in &cluster {
        let top = root_expr(layer, rid);
        collect_expr_cone(layer, top, &mut keep_exprs, &mut keep_sources, &cluster);
    }

    // Surviving sinks: exactly the sinks written by surviving Output roots.
    let mut keep_sinks: BTreeSet<u32> = BTreeSet::new();
    for &rid in &cluster {
        if let Root::Output { sink, .. } = &layer.roots[rid.0 as usize] {
            keep_sinks.insert(sink.0);
        }
    }

    // ── 3. Build the four old -> new id remaps ────────────────────────────────
    // Roots: cache (Cache-sink Output) roots LEAD, then the rest — F2 caches-lead.
    let mut cache_roots: Vec<RootId> = Vec::new();
    let mut other_roots: Vec<RootId> = Vec::new();
    for &rid in &cluster {
        if is_cache_root(layer, rid) {
            cache_roots.push(rid);
        } else {
            other_roots.push(rid);
        }
    }
    let ordered_roots: Vec<RootId> =
        cache_roots.into_iter().chain(other_roots.into_iter()).collect();
    let root_remap: HashMap<RootId, RootId> = ordered_roots
        .iter()
        .enumerate()
        .map(|(new, &old)| (old, RootId(new as u32)))
        .collect();

    let expr_remap: HashMap<ExprId, ExprId> = keep_exprs
        .iter()
        .enumerate()
        .map(|(new, &old)| (ExprId(old), ExprId(new as u32)))
        .collect();
    let source_remap: HashMap<SourceId, SourceId> = keep_sources
        .iter()
        .enumerate()
        .map(|(new, &old)| (SourceId(old), SourceId(new as u32)))
        .collect();
    let sink_remap: HashMap<SinkId, SinkId> = keep_sinks
        .iter()
        .enumerate()
        .map(|(new, &old)| (SinkId(old), SinkId(new as u32)))
        .collect();

    // ── 4. Emit the new field vectors in new-id order ─────────────────────────
    // Sources (rewrite Prior id + LookupValue.query).
    let mut new_sources: Vec<SourceInfo> = Vec::with_capacity(keep_sources.len());
    for &old in &keep_sources {
        let src = &layer.sources[old as usize];
        let kind = match &src.kind {
            SourceKind::Prior { id } => SourceKind::Prior {
                id: root_remap[id],
            },
            SourceKind::LookupValue {
                kind,
                set_index,
                query,
            } => SourceKind::LookupValue {
                kind: kind.clone(),
                set_index: *set_index,
                query: expr_remap[query],
            },
            other => other.clone(),
        };
        new_sources.push(SourceInfo { kind });
    }

    // Exprs (rewrite Source id + Add/Mul operand ids).
    let mut new_exprs: Vec<Expr> = Vec::with_capacity(keep_exprs.len());
    for &old in &keep_exprs {
        let expr = match &layer.exprs[old as usize] {
            Expr::Source(sid) => Expr::Source(source_remap[sid]),
            Expr::Add(args) => Expr::Add(args.iter().map(|a| expr_remap[a]).collect()),
            Expr::Mul(args) => Expr::Mul(args.iter().map(|a| expr_remap[a]).collect()),
        };
        new_exprs.push(expr);
    }

    // Sinks (carried verbatim — kind/field unchanged, only re-indexed).
    let mut new_sinks: Vec<SinkInfo> = Vec::with_capacity(keep_sinks.len());
    for &old in &keep_sinks {
        new_sinks.push(layer.sinks[old as usize].clone());
    }

    // Roots (rewrite expr + sink ids), in caches-lead order.
    let mut new_roots: Vec<Root> = Vec::with_capacity(ordered_roots.len());
    for &old in &ordered_roots {
        let root = match &layer.roots[old.0 as usize] {
            Root::Output { expr, sink } => Root::Output {
                expr: expr_remap[expr],
                sink: sink_remap[sink],
            },
            Root::Constraint { expr } => Root::Constraint {
                expr: expr_remap[expr],
            },
        };
        new_roots.push(root);
    }

    // ── 5. Rebuild batching, origins, resolutions for survivors only ──────────
    // Batching = surviving claim-bearing roots, in their NEW index order.
    let mut new_batching: Vec<RootId> = Vec::new();
    for (new_idx, _root) in new_roots.iter().enumerate() {
        let new_rid = RootId(new_idx as u32);
        // A root is claim-bearing iff it is NOT a cache (Cache-sink Output) root.
        // Determine via the original root (we have the new->old via ordered_roots).
        let old_rid = ordered_roots[new_idx];
        if !is_cache_root(layer, old_rid) {
            new_batching.push(new_rid);
        }
    }

    // Origins: keyed by RootId; carry surviving roots only, remapped.
    let mut new_origins: BTreeMap<RootId, _> = BTreeMap::new();
    for (&old_rid, origin) in &layer.origins {
        if let Some(&new_rid) = root_remap.get(&old_rid) {
            new_origins.insert(new_rid, origin.clone());
        }
    }

    // Resolutions: keyed by ExprId; carry surviving leaves only, remapped.
    // The expr subtree is copied verbatim (only re-indexed), so the structural
    // shape that check_resolutions enforces is preserved.
    let mut new_resolutions: BTreeMap<ExprId, _> = BTreeMap::new();
    for (&old_leaf, strat) in &layer.resolutions {
        if let Some(&new_leaf) = expr_remap.get(&old_leaf) {
            new_resolutions.insert(new_leaf, strat.clone());
        }
    }

    DagLayer {
        sources: new_sources,
        exprs: new_exprs,
        roots: new_roots,
        sinks: new_sinks,
        batching: BatchingOrder { roots: new_batching },
        origins: new_origins,
        resolutions: new_resolutions,
    }
}

// ── Helpers ───────────────────────────────────────────────────────────────────

/// The top `ExprId` of a root.
fn root_expr(layer: &DagLayer, rid: RootId) -> ExprId {
    match &layer.roots[rid.0 as usize] {
        Root::Output { expr, .. } => *expr,
        Root::Constraint { expr } => *expr,
    }
}

/// Is `rid` a materialization-only cache root (Cache-sink Output)?
fn is_cache_root(layer: &DagLayer, rid: RootId) -> bool {
    matches!(&layer.roots[rid.0 as usize], Root::Output { sink, .. }
        if matches!(layer.sinks[sink.0 as usize].kind, SinkKind::Cache { .. }))
}

/// Walk the expr cone of `rid`'s top expr and return every `Prior{id}` target
/// root reachable WITHOUT crossing into another root's cone (Prior edges stop at
/// the target root; we record the target but do not descend through it here —
/// the closure loop handles that root separately).
fn prior_targets_in_cone(layer: &DagLayer, rid: RootId) -> Vec<RootId> {
    let mut targets = Vec::new();
    let mut visited: BTreeSet<u32> = BTreeSet::new();
    let mut stack: Vec<ExprId> = vec![root_expr(layer, rid)];
    while let Some(eid) = stack.pop() {
        if !visited.insert(eid.0) {
            continue;
        }
        match &layer.exprs[eid.0 as usize] {
            Expr::Source(sid) => match &layer.sources[sid.0 as usize].kind {
                SourceKind::Prior { id } => targets.push(*id),
                SourceKind::LookupValue { query, .. } => stack.push(*query),
                _ => {}
            },
            Expr::Add(args) | Expr::Mul(args) => stack.extend(args.iter().copied()),
        }
    }
    targets
}

/// Collect every `ExprId` (into `keep_exprs`) and every `SourceId` (into
/// `keep_sources`) reachable from `top`, following Add/Mul operands and
/// LookupValue.query. A `Prior{id}` source is kept (it is a real source in the
/// cone), but we do NOT descend through it — the target root is handled by the
/// closure loop, and `id` is guaranteed in `cluster`.
fn collect_expr_cone(
    layer: &DagLayer,
    top: ExprId,
    keep_exprs: &mut BTreeSet<u32>,
    keep_sources: &mut BTreeSet<u32>,
    cluster: &BTreeSet<RootId>,
) {
    let mut stack: Vec<ExprId> = vec![top];
    while let Some(eid) = stack.pop() {
        if !keep_exprs.insert(eid.0) {
            continue;
        }
        match &layer.exprs[eid.0 as usize] {
            Expr::Source(sid) => {
                keep_sources.insert(sid.0);
                match &layer.sources[sid.0 as usize].kind {
                    SourceKind::Prior { id } => {
                        debug_assert!(
                            cluster.contains(id),
                            "Prior target {id:?} escaped the cluster closure"
                        );
                    }
                    SourceKind::LookupValue { query, .. } => stack.push(*query),
                    _ => {}
                }
            }
            Expr::Add(args) | Expr::Mul(args) => stack.extend(args.iter().copied()),
        }
    }
}

// ── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{validate, DagCircuit, DagGlobals};

    /// Count the `SourceKind::Prior` sources actually reachable from the layer's
    /// roots (the order-sensitivity driver). Reachability uses the validate()
    /// edge set so the count matches what the oracle would see.
    fn reachable_prior_sources(layer: &DagLayer) -> usize {
        let mut keep_exprs: BTreeSet<u32> = BTreeSet::new();
        let mut keep_sources: BTreeSet<u32> = BTreeSet::new();
        let cluster: BTreeSet<RootId> =
            (0..layer.roots.len() as u32).map(RootId).collect();
        for rid in 0..layer.roots.len() as u32 {
            let top = root_expr(layer, RootId(rid));
            collect_expr_cone(layer, top, &mut keep_exprs, &mut keep_sources, &cluster);
        }
        keep_sources
            .iter()
            .filter(|&&s| matches!(layer.sources[s as usize].kind, SourceKind::Prior { .. }))
            .count()
    }

    /// Pick a seed root whose cone transitively reaches at least one `Prior`
    /// source — the smallest such cluster keeps the test fast while still
    /// exercising the Prior remap. Returns `(seed, cluster_root_count)`.
    fn pick_prior_seed(layer: &DagLayer) -> RootId {
        let mut best: Option<(usize, RootId)> = None;
        for rid in 0..layer.roots.len() as u32 {
            let seed = RootId(rid);
            // Does the seed's cluster contain at least one Prior?
            let cluster = connected_root_cluster(layer, seed);
            if reachable_prior_sources(&cluster) == 0 {
                continue;
            }
            let size = cluster.roots.len();
            match best {
                Some((b, _)) if b <= size => {}
                _ => best = Some((size, seed)),
            }
        }
        best.expect("at least one root must have a Prior in its cluster (add_sub L0 has caches)")
            .1
    }

    fn wrap(layer: DagLayer) -> DagCircuit {
        DagCircuit {
            layers: vec![layer],
            globals: DagGlobals::default(),
        }
    }

    /// Load `add_sub_lui_auipc_mop_layout_gkr.json` layer 0 directly (same path
    /// the 8a `load_layer_source` uses), pick a Prior-bearing seed, build the
    /// cluster, and assert validate() passes, the cluster is strictly smaller,
    /// and Prior edges are preserved with no dangling Prior.
    #[test]
    fn connected_root_cluster_preserves_validity_and_prior_edges() {
        use cs::gkr_compiler::dag_ir::lower_dag;
        use cs::gkr_compiler::GKRCircuitArtifact;
        use field::baby_bear::base::BabyBearField;
        use std::path::PathBuf;

        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../cs/compiled_circuits")
            .join("add_sub_lui_auipc_mop_layout_gkr.json");
        let artifact: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&std::fs::read(&path).expect("read fixture"))
                .expect("deserialize fixture");
        let dag = lower_dag(&artifact).expect("lower_dag");
        validate(&dag).expect("source layer must validate");
        let layer = &dag.layers[0];

        // The source layer must have Prior edges (decision-bearing precondition).
        let src_priors = reachable_prior_sources(layer);
        assert!(
            src_priors > 0,
            "add_sub L0 must have Prior edges to exercise the cluster (got {src_priors})"
        );

        let seed = pick_prior_seed(layer);
        let cluster = connected_root_cluster(layer, seed);

        eprintln!(
            "[CLUSTER] seed={seed:?} -> cluster roots={} exprs={} sources={} priors={} \
             (full: roots={} exprs={} sources={} priors={})",
            cluster.roots.len(),
            cluster.exprs.len(),
            cluster.sources.len(),
            reachable_prior_sources(&cluster),
            layer.roots.len(),
            layer.exprs.len(),
            layer.sources.len(),
            src_priors,
        );

        // (1) validate() PASSES on the cluster.
        validate(&wrap(cluster.clone())).expect("cluster must validate()");

        // (2) Cluster is STRICTLY SMALLER (fewer roots and/or exprs).
        assert!(
            cluster.roots.len() < layer.roots.len() || cluster.exprs.len() < layer.exprs.len(),
            "cluster must be strictly smaller than the source layer"
        );

        // (3) Prior edges PRESERVED: at least one Prior, and every Prior points
        //     to a valid in-cluster root (closure complete — no dangling Prior).
        let cluster_priors = reachable_prior_sources(&cluster);
        assert!(
            cluster_priors >= 1,
            "cluster must preserve at least one Prior source (got {cluster_priors})"
        );
        for (si, src) in cluster.sources.iter().enumerate() {
            if let SourceKind::Prior { id } = &src.kind {
                assert!(
                    (id.0 as usize) < cluster.roots.len(),
                    "dangling Prior at source {si}: {id:?} >= {} roots",
                    cluster.roots.len()
                );
                // The target must itself be a Cache-sink Output root (F1) — this
                // is also enforced by validate(), but assert it for clarity.
                assert!(
                    is_cache_root(&cluster, *id),
                    "Prior target {id:?} must be a Cache-sink Output root"
                );
            }
        }
    }
}
