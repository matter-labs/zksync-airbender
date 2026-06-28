//! `connected_root_cluster` — a `validate()`-preserving downscale of a real GKR
//! `DagLayer` to the shared-cache cluster of a seed root.
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
//! i.e. it preserves the shared-cache reuse density.
//!
//! `connected_root_cluster` is THE tool that produces those small instances. It
//! shrinks a real layer while preserving (a) validity and (b) the shared-cache
//! reuse that drives order sensitivity.
//!
//! ## What "shared-cache cluster" means (attribute model)
//!
//! Stage 1 removed `SourceKind::Prior`: same-layer cache reuse is now expressed
//! as a SHARED `ExprId`. A *cache root* (`materialize: Some(Cache), claim: None`)
//! commits an intermediate value; another root REUSES that value when the cache
//! root's `expr` also appears inside that other root's expr cone. The cluster is
//! the transitive closure over this shared-expr reuse from the seed:
//!   start = {seed_root};
//!   for every root in the set, walk its expr cone collecting `ExprId`s; for each
//!   cache root whose `expr` appears in the cone, add that cache root; repeat to a
//!   fixpoint.
//! This yields a self-contained set of roots: because the cone walk traverses the
//! whole shared subtree (it never stops at a cache root — see `cache_roots_in_cone`),
//! every expr a survivor references stays inside the kept-expr set, so no
//! dangling references survive into the downscaled layer.
//!
//! ## Re-indexing the 5 cross-referencing `DagLayer` fields
//!
//! `DagLayer { sources, exprs, roots, batching, resolutions }`. Subsetting
//! requires three consistent remaps (`old -> new` id maps) for exprs, sources,
//! and roots, then a rewrite of every cross-reference: `Expr::Source(SourceId)`,
//! `Expr::Add/Mul(Vec<ExprId>)`, and `Root { expr, materialize, claim }` (its
//! `expr` is remapped; `materialize`/`claim` are inline structs cloned verbatim —
//! there is no separate sink/origin table to remap). `batching.roots` (claim-
//! bearing roots) and `resolutions` (keyed by `ExprId`) are carried over for the
//! SURVIVING ids only, remapped; entries for excluded ids are dropped.
//!
//! ## validate() requirements satisfied here (validate.rs)
//!
//! - **No Prior / no caches-lead ordering** (Step 1 finding): the new validator
//!   (`cs/src/gkr_compiler/dag_ir/validate.rs:672-677`) explicitly dropped the
//!   old Prior/caches-lead (F1/F2) invariants — "The expr DAG is acyclic by
//!   construction … so there is no Prior/caches-lead ordering to enforce." So we
//!   keep the cluster's roots in their ORIGINAL relative order (no cache-first
//!   re-ordering); the `BTreeSet` already iterates in ascending `RootId`.
//! - **batching membership**: cache roots (`claim.is_none()`) must NOT appear in
//!   the batching order; every claim-bearing root (`claim.is_some()`) must appear
//!   exactly once. We rebuild `batching` from the surviving claim-bearing roots
//!   in their new index order.
//! - **acyclicity / field inference / reference-range**: preserved because the
//!   expr/source subtrees are copied verbatim (only ids are renumbered) and the
//!   cone walk keeps every transitively referenced expr/source, so no reference
//!   escapes the kept set.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use cs::gkr_compiler::dag_ir::{
    BatchingOrder, DagLayer, Expr, ExprId, Root, RootId, SinkInfo, SinkKind, SourceId, SourceInfo,
    SourceKind,
};

/// Keep only the roots in the shared-cache cluster of `seed_root`, re-indexed
/// into a self-contained, `validate()`-passing `DagLayer`.
///
/// See the module docs for the closure + re-indexing algorithm and the
/// validate() requirements satisfied.
pub fn connected_root_cluster(layer: &DagLayer, seed_root: RootId) -> DagLayer {
    // Precompute cache-value-expr -> cache-root once: a shared cache value is
    // reached in a cone iff its `expr` appears in that cone.
    let cache_expr_to_root: HashMap<ExprId, RootId> = (0..layer.roots.len() as u32)
        .map(RootId)
        .filter(|&rid| is_cache_root(layer, rid))
        .map(|rid| (layer.roots[rid.0 as usize].expr, rid))
        .collect();

    // ── 1. Transitive shared-cache closure over roots ────────────────────────
    // Start from the seed; for each root in the set, walk its expr cone and add
    // every cache root whose `expr` appears in the cone; repeat to a fixpoint.
    let mut cluster: BTreeSet<RootId> = BTreeSet::new();
    let mut frontier: Vec<RootId> = vec![seed_root];
    while let Some(rid) = frontier.pop() {
        if !cluster.insert(rid) {
            continue;
        }
        // Walk the cone of this root, collecting reached cache roots.
        for cache_target in cache_roots_in_cone(layer, rid, &cache_expr_to_root) {
            if !cluster.contains(&cache_target) {
                frontier.push(cache_target);
            }
        }
    }

    // ── 2. Collect surviving exprs + sources reachable from cluster roots ─────
    // Reachability follows the SAME edges validate() uses: Add/Mul operands and
    // LookupValue.query. A cache value's subtree is reached through whichever
    // cluster root's cone contains its shared `expr`, so it is kept here.
    let mut keep_exprs: BTreeSet<u32> = BTreeSet::new();
    let mut keep_sources: BTreeSet<u32> = BTreeSet::new();
    for &rid in &cluster {
        let top = root_expr(layer, rid);
        collect_expr_cone(layer, top, &mut keep_exprs, &mut keep_sources);
    }

    // ── 3. Build the expr/source old -> new id remaps ─────────────────────────
    // Roots: caches-lead is gone (Step 1), so keep the cluster's ORIGINAL
    // relative order — the `BTreeSet` already yields ascending `RootId`. Roots
    // are rebuilt directly from `ordered_roots` (no separate root-id remap is
    // needed: nothing references a root by id except `batching`, rebuilt below).
    let ordered_roots: Vec<RootId> = cluster.iter().copied().collect();

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

    // ── 4. Emit the new field vectors in new-id order ─────────────────────────
    // Sources (rewrite LookupValue.query; no Prior source exists any more).
    let mut new_sources: Vec<SourceInfo> = Vec::with_capacity(keep_sources.len());
    for &old in &keep_sources {
        let src = &layer.sources[old as usize];
        let kind = match &src.kind {
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

    // Roots become structs: remap `expr`; clone inline `materialize`/`claim`
    // (SinkInfo/ClaimInfo are inline — no sink-id or origin-table remap needed).
    let mut new_roots: Vec<Root> = Vec::with_capacity(ordered_roots.len());
    for &old in &ordered_roots {
        let r = &layer.roots[old.0 as usize];
        new_roots.push(Root {
            expr: expr_remap[&r.expr],
            materialize: r.materialize.clone(),
            claim: r.claim.clone(),
        });
    }

    // ── 5. Rebuild batching + resolutions for survivors only ──────────────────
    // Batching = surviving claim-bearing roots (`claim.is_some()`), in NEW order.
    let mut new_batching: Vec<RootId> = Vec::new();
    for (new_idx, _root) in new_roots.iter().enumerate() {
        let old_rid = ordered_roots[new_idx];
        if layer.roots[old_rid.0 as usize].claim.is_some() {
            new_batching.push(RootId(new_idx as u32));
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
        batching: BatchingOrder { roots: new_batching },
        resolutions: new_resolutions,
    }
}

// ── Public helpers (reused by the 8c harness) ───────────────────────────────

/// Count the distinct shared cache values reachable from a layer's roots — the
/// order-sensitivity driver. A cache value is "shared" when its `expr` is reached
/// by ≥2 distinct claim-bearing root cones; such a value is a residency decision
/// (hold-and-reuse vs recompute), so a cluster with one or more shared cache
/// values is where an order gap can actually manifest.
///
/// Reachability uses the same edge set as `connected_root_cluster`/`validate()`,
/// so the count matches what the oracle would see.
pub fn reachable_shared_cache_values(layer: &DagLayer) -> usize {
    // cache value `expr` -> set of distinct claim-bearing roots that reach it.
    let cache_expr_to_root: HashMap<ExprId, RootId> = (0..layer.roots.len() as u32)
        .map(RootId)
        .filter(|&rid| is_cache_root(layer, rid))
        .map(|rid| (layer.roots[rid.0 as usize].expr, rid))
        .collect();

    let mut reach_count: HashMap<ExprId, BTreeSet<RootId>> = HashMap::new();
    for rid in (0..layer.roots.len() as u32).map(RootId) {
        // Only claim-bearing root cones drive order sensitivity (a cache root's
        // own expr trivially reaches itself; that is not "sharing").
        if layer.roots[rid.0 as usize].claim.is_none() {
            continue;
        }
        for cache_rid in cache_roots_in_cone(layer, rid, &cache_expr_to_root) {
            let cache_expr = layer.roots[cache_rid.0 as usize].expr;
            reach_count.entry(cache_expr).or_default().insert(rid);
        }
    }

    reach_count.values().filter(|s| s.len() >= 2).count()
}

// ── Helpers ───────────────────────────────────────────────────────────────────

/// The top `ExprId` of a root.
fn root_expr(layer: &DagLayer, rid: RootId) -> ExprId {
    layer.roots[rid.0 as usize].expr
}

/// Is `rid` a materialization-only cache root? Attribute-model identity
/// (Stage-1 lowering): a `Cache` materialize with no claim.
fn is_cache_root(layer: &DagLayer, rid: RootId) -> bool {
    let r = &layer.roots[rid.0 as usize];
    matches!(
        &r.materialize,
        Some(SinkInfo {
            kind: SinkKind::Cache { .. },
            ..
        })
    ) && r.claim.is_none()
}

/// Walk the expr cone of `rid`'s top expr and return every cache root whose
/// `expr` appears in the cone. We descend through a reached cache `expr` anyway:
/// a cache value's cone may itself reach further cache values (shared chains).
fn cache_roots_in_cone(
    layer: &DagLayer,
    rid: RootId,
    cache_expr_to_root: &HashMap<ExprId, RootId>,
) -> Vec<RootId> {
    let mut targets = Vec::new();
    let mut visited: BTreeSet<u32> = BTreeSet::new();
    let mut stack: Vec<ExprId> = vec![root_expr(layer, rid)];
    while let Some(eid) = stack.pop() {
        if !visited.insert(eid.0) {
            continue;
        }
        if let Some(&cache_rid) = cache_expr_to_root.get(&eid) {
            targets.push(cache_rid); // a shared cache value reached in this cone
            // descend anyway: a cache value's cone may reach further cache values
        }
        match &layer.exprs[eid.0 as usize] {
            Expr::Source(sid) => {
                if let SourceKind::LookupValue { query, .. } = &layer.sources[sid.0 as usize].kind {
                    stack.push(*query);
                }
            }
            Expr::Add(args) | Expr::Mul(args) => stack.extend(args.iter().copied()),
        }
    }
    targets
}

/// Collect every `ExprId` (into `keep_exprs`) and every `SourceId` (into
/// `keep_sources`) reachable from `top`, following Add/Mul operands and
/// LookupValue.query. There is no Prior source to special-case any more: a shared
/// cache value's subtree is reached transitively through the cone that contains
/// its `expr`, so the kept-expr set is self-contained with no dangling refs.
fn collect_expr_cone(
    layer: &DagLayer,
    top: ExprId,
    keep_exprs: &mut BTreeSet<u32>,
    keep_sources: &mut BTreeSet<u32>,
) {
    let mut stack: Vec<ExprId> = vec![top];
    while let Some(eid) = stack.pop() {
        if !keep_exprs.insert(eid.0) {
            continue;
        }
        match &layer.exprs[eid.0 as usize] {
            Expr::Source(sid) => {
                keep_sources.insert(sid.0);
                if let SourceKind::LookupValue { query, .. } = &layer.sources[sid.0 as usize].kind {
                    stack.push(*query);
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

    use super::reachable_shared_cache_values;

    /// Pick a seed root whose cluster contains at least one shared cache value —
    /// the smallest such cluster keeps the test fast while still exercising the
    /// shared-cache remap. Returns the seed.
    fn pick_shared_cache_seed(layer: &DagLayer) -> RootId {
        let mut best: Option<(usize, RootId)> = None;
        for rid in 0..layer.roots.len() as u32 {
            let seed = RootId(rid);
            let cluster = connected_root_cluster(layer, seed);
            // Need at least 2 roots sharing a cache value for an order gap to show.
            if reachable_shared_cache_values(&cluster) == 0 {
                continue;
            }
            let size = cluster.roots.len();
            match best {
                Some((b, _)) if b <= size => {}
                _ => best = Some((size, seed)),
            }
        }
        best.expect("at least one root must share a cache value in its cluster (add_sub L0 has caches)")
            .1
    }

    fn wrap(layer: DagLayer) -> DagCircuit {
        DagCircuit {
            layers: vec![layer],
            globals: DagGlobals::default(),
        }
    }

    /// Load `add_sub_lui_auipc_mop_layout_gkr.json` layer 0 directly (same path
    /// the 8a `load_layer_source` uses), pick a shared-cache seed, build the
    /// cluster, and assert validate() passes, the cluster is strictly smaller,
    /// and the shared-cache reuse is preserved with no dangling references.
    #[test]
    fn connected_root_cluster_preserves_validity_and_shared_cache() {
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

        // The source layer must have shared cache values (decision-bearing
        // precondition).
        let src_shared = reachable_shared_cache_values(layer);
        assert!(
            src_shared > 0,
            "add_sub L0 must have shared cache values to exercise the cluster (got {src_shared})"
        );

        let seed = pick_shared_cache_seed(layer);
        let cluster = connected_root_cluster(layer, seed);

        eprintln!(
            "[CLUSTER] seed={seed:?} -> cluster roots={} exprs={} sources={} shared_cache={} \
             (full: roots={} exprs={} sources={} shared_cache={})",
            cluster.roots.len(),
            cluster.exprs.len(),
            cluster.sources.len(),
            reachable_shared_cache_values(&cluster),
            layer.roots.len(),
            layer.exprs.len(),
            layer.sources.len(),
            src_shared,
        );

        // (1) validate() PASSES on the cluster.
        validate(&wrap(cluster.clone())).expect("cluster must validate()");

        // (2) Cluster is STRICTLY SMALLER (fewer roots and/or exprs).
        assert!(
            cluster.roots.len() < layer.roots.len() || cluster.exprs.len() < layer.exprs.len(),
            "cluster must be strictly smaller than the source layer"
        );

        // (3) Shared-cache reuse PRESERVED: at least one shared cache value, and
        //     every cache root's `expr` stays in range as a valid in-cluster expr
        //     (closure complete — no dangling references).
        let cluster_shared = reachable_shared_cache_values(&cluster);
        assert!(
            cluster_shared >= 1,
            "cluster must preserve at least one shared cache value (got {cluster_shared})"
        );
        for rid in 0..cluster.roots.len() as u32 {
            let rid = RootId(rid);
            if is_cache_root(&cluster, rid) {
                let expr = cluster.roots[rid.0 as usize].expr;
                assert!(
                    (expr.0 as usize) < cluster.exprs.len(),
                    "cache root {rid:?} expr {expr:?} out of range ({} exprs)",
                    cluster.exprs.len()
                );
            }
        }
    }
}
