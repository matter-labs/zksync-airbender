//! Read-only BACKWARD schedule view over the canonical per-layer DAG.
//!
//! This module is the sumcheck (backward) counterpart of [`schedule`]'s forward
//! site enumeration. It is a pure **view**: it never mutates a [`DagLayer`] and
//! never changes any forward behaviour. Where the forward walk
//! ([`enumerate_site_domain`](super::schedule::enumerate_site_domain),
//! `schedule.rs:120`) iterates the whole arena deliberately loosely and fences
//! resolution cones, the backward walk here is a **strict two-pass traversal**
//! restricted to the reachable cones of the layer's CLAIM-bearing roots
//! (`root.claim.is_some()`), it descends `LookupValue.query` edges, and it
//! DISABLES the resolution fences (the sumcheck pass consumes the authoritative
//! `expr`, never the forward peek hint).
//!
//! Three REV2-pinned mechanics distinguish this from the forward walk:
//!   (i)   two-pass traversal restricted to the reachable claim cones — the first
//!         pass counts consumers (counting `LookupValue.query` edges only when the
//!         `LookupValue` itself is reachable), the second emits sites;
//!   (ii)  resolution fences are DISABLED;
//!   (iii) admission = compound/root values with fan-out >= 2, PLUS `Read` leaves
//!         with fan-out >= 2 in BOTH regimes (R0: real Global DRAM reads; Ext:
//!         they become FoldSources), PLUS `VirtualSetup` leaves with fan-out >= 2
//!         in the `Ext` regime ONLY.
//!
//! REV2 IDENTITY CAVEAT: a [`SiteKey`] embeds root/consumer/value `ExprId`s of the
//! CANONICAL layer. The sites enumerated here are for tests and floor reporting
//! ONLY; the sites that feed compilation are enumerated on the DISTILLED layer
//! (a later task's output), whose arena/root ids differ.

use std::collections::{BTreeSet, HashMap, HashSet};

use gkr_eval_ir::{
    DagLayer, Expr, ExprId, FieldKind, ReadPlace, RootGroup, RootId, SinkKind, SourceKind,
    source_field,
};

use crate::schedule::{SiteConsumer, SiteKey};

/// A same-layer cache boundary: the backward pass folds the forward-materialized
/// cache column instead of descending into the defining cone (mirrors production,
/// where gates fold `GKRAddress::Cached` inputs and cache relations are opened
/// post-loop — `prover/src/gkr/prover/sumcheck_loop/mod.rs:391-502`).
#[derive(Clone, Debug, PartialEq)]
pub struct CacheFence {
    /// Always `ReadPlace::CacheOutput { layer, offset }`.
    pub place: ReadPlace,
    /// The cache sink's field (`SinkInfo.field`).
    pub field: FieldKind,
}

/// `ExprId -> fence` for every same-layer cache root of `layer`. Same-layer cache
/// consumption is plain DAG sharing (`lower/util.rs` `read_expr` returns the cache
/// value's ExprId, no edge marker), so the fence key is the cache root's own expr
/// id. First sink wins on shared exprs.
pub fn bwd_cache_fences(layer: &DagLayer) -> HashMap<ExprId, CacheFence> {
    let mut m = HashMap::new();
    for root in layer.roots.iter() {
        // Only fence CLAIM-LESS cache roots. A claim-bearing root with a Cache sink
        // would otherwise have its entire spine term replaced by a
        // `Read(CacheOutput)` leaf — folding the output column instead of the gate
        // cone, diverging from production. Cache relations are linear but gate
        // cones need not be. Production lowering permits the combination
        // (`emit_output` attaches both materialize and claim), even though today
        // only `emit_cache` (claim: None) produces Cache sinks.
        if root.claim.is_some() {
            continue;
        }
        if let Some(sink) = &root.materialize {
            if let SinkKind::Cache { layer: l, offset } = sink.kind {
                m.entry(root.expr).or_insert(CacheFence {
                    place: ReadPlace::CacheOutput { layer: l, offset },
                    field: sink.field,
                });
            }
        }
    }
    m
}

/// Which backward regime the domain/floor is computed for.
///
/// `R0` is the base (round-0) pass — `Read` leaves are real Global DRAM reads and
/// keep their native field width. `Ext` is the extension-folded pass — every leaf
/// is an Ext-width FoldSource, and `VirtualSetup` leaves join the admissible set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BwdRegime {
    R0,
    Ext,
}

/// The layer's backward (claim-bearing) roots, in batching order.
///
/// Returns `layer.batching.roots` verbatim after asserting it is exactly the set
/// of `claim.is_some()` roots with each appearing exactly once. Layer validation
/// is a precondition of this view, so this asserts (a debug contract) rather than
/// re-validating.
pub fn claim_roots(layer: &DagLayer) -> &[RootId] {
    let claim_roots: Vec<RootId> = layer
        .roots
        .iter()
        .enumerate()
        .filter(|(_, r)| r.claim.is_some())
        .map(|(i, _)| RootId(i as u32))
        .collect();
    assert_eq!(
        layer.batching.roots.len(),
        claim_roots.len(),
        "batching.roots ({}) must have one entry per claim-bearing root ({})",
        layer.batching.roots.len(),
        claim_roots.len()
    );
    let batching_set: BTreeSet<RootId> = layer.batching.roots.iter().copied().collect();
    assert_eq!(
        batching_set.len(),
        layer.batching.roots.len(),
        "batching.roots must not contain duplicates"
    );
    for rid in &claim_roots {
        assert!(
            batching_set.contains(rid),
            "claim-bearing root {} is missing from the batching order",
            rid.0
        );
    }
    &layer.batching.roots
}

/// The backward roots grouped by `(claim.origin.group, claim.origin.relation_index)`.
///
/// Batching order is preserved within each group and across groups (a group is
/// positioned by the first backward root that belongs to it). Unlike the forward
/// [`relation_units_with_caches`](super::schedule::relation_units_with_caches),
/// this includes claim-ONLY Constraint roots (`materialize: None`), which the
/// forward decomposition omits.
pub fn claim_relation_units(layer: &DagLayer) -> Vec<Vec<RootId>> {
    let mut groups: Vec<Vec<RootId>> = Vec::new();
    let mut key_to_idx: HashMap<(RootGroup, usize), usize> = HashMap::new();
    for &rid in claim_roots(layer) {
        let claim = layer.roots[rid.0 as usize]
            .claim
            .as_ref()
            .expect("a backward root is claim-bearing by construction");
        let key = (claim.origin.group.clone(), claim.origin.relation_index);
        let idx = *key_to_idx.entry(key).or_insert_with(|| {
            groups.push(Vec::new());
            groups.len() - 1
        });
        groups[idx].push(rid);
    }
    groups
}

// ─────────────────────────────────────────────────────────────────────────────
// Backward site enumeration (two-pass, claim-cone-restricted, fence-free).
// ─────────────────────────────────────────────────────────────────────────────

/// Every backward structural demand site in `layer` for `regime`.
///
/// Parallel of [`enumerate_site_domain`](super::schedule::enumerate_site_domain)
/// with the three REV2 mechanics documented at the module top. The walk is
/// restricted to the reachable cones of the claim-bearing roots, descends
/// `LookupValue.query` edges, and applies NO resolution fence. A value is a site
/// when its (cone-restricted) consumer count is >= 2 AND it is backward-cacheable
/// for `regime` (see [`is_cacheable_bwd`]).
pub fn enumerate_bwd_site_domain(layer: &DagLayer, regime: BwdRegime) -> BTreeSet<SiteKey> {
    let fences = bwd_cache_fences(layer);
    let reachable = reachable_exprs_bwd(layer);
    let consumers = consumer_counts_bwd(layer, &reachable, &fences);

    let mut out: BTreeSet<SiteKey> = BTreeSet::new();
    let mut visited: HashSet<(RootId, ExprId)> = HashSet::new();
    for (i, root) in layer.roots.iter().enumerate() {
        if root.claim.is_none() {
            continue;
        }
        let rid = RootId(i as u32);
        if is_site(layer, regime, &consumers, &fences, root.expr) {
            out.insert(SiteKey {
                root: rid,
                consumer: SiteConsumer::RootOutput,
                value: root.expr,
            });
        }
        walk_demand(
            layer,
            regime,
            &consumers,
            &fences,
            rid,
            root.expr,
            /* descend_query */ true,
            &mut visited,
            &mut out,
        );
    }
    out
}

/// The set of exprs reachable from the claim-bearing roots over Add/Mul operand
/// edges and `LookupValue.query` edges. NO resolution fence (mechanic (ii)), but
/// a same-layer CACHE fence: a cache-root expr stays in the set as a folded leaf,
/// its defining cone is never descended (mirrors production folding a
/// `GKRAddress::Cached` input instead of the cache relation).
fn reachable_exprs_bwd(layer: &DagLayer) -> HashSet<ExprId> {
    let fences = bwd_cache_fences(layer);
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut stack: Vec<ExprId> = layer
        .roots
        .iter()
        .filter(|r| r.claim.is_some())
        .map(|r| r.expr)
        .collect();
    while let Some(e) = stack.pop() {
        if !seen.insert(e) {
            continue;
        }
        // Cache fence: keep `e` in the reachable set (it is a folded leaf) but do
        // not descend its defining cone.
        if fences.contains_key(&e) {
            continue;
        }
        match &layer.exprs[e.0 as usize] {
            Expr::Source(src_id) => {
                if let SourceKind::LookupValue { query, .. } =
                    &layer.sources[src_id.0 as usize].kind
                {
                    stack.push(*query);
                }
            }
            Expr::Add(children) | Expr::Mul(children) => stack.extend(children.iter().copied()),
        }
    }
    seen
}

/// Consumer counts, tallied ONLY over the reachable claim cones (mechanic (i)):
/// each Add/Mul operand edge of a reachable expr, each `LookupValue.query` edge of
/// a reachable `LookupValue` source, and each claim-bearing root's demand of its
/// own output. Edges outside the reachable cones do not contribute.
fn consumer_counts_bwd(
    layer: &DagLayer,
    reachable: &HashSet<ExprId>,
    fences: &HashMap<ExprId, CacheFence>,
) -> Vec<u32> {
    let mut consumers = vec![0u32; layer.exprs.len()];
    for &e in reachable {
        // Fenced cache leaf: its defining cone is folded, not walked — do not count
        // its child/query edges as backward demands.
        if fences.contains_key(&e) {
            continue;
        }
        match &layer.exprs[e.0 as usize] {
            Expr::Source(src_id) => {
                // Count a query edge only when its LookupValue source is reachable
                // — guaranteed here since `e` ranges over the reachable set only.
                if let SourceKind::LookupValue { query, .. } =
                    &layer.sources[src_id.0 as usize].kind
                {
                    consumers[query.0 as usize] += 1;
                }
            }
            Expr::Add(children) | Expr::Mul(children) => {
                for &c in children {
                    consumers[c.0 as usize] += 1;
                }
            }
        }
    }
    // Each claim-bearing root is a backward consumer of its own output expr (the
    // polynomial the sumcheck runs on) — mirrors the forward walk counting
    // materialize-bearing root occurrences, but keyed on `claim` not `materialize`.
    for root in &layer.roots {
        if root.claim.is_some() {
            consumers[root.expr.0 as usize] += 1;
        }
    }
    consumers
}

/// Recurse into `value`'s demanded children (memoized per `(root, value)`),
/// pushing a [`SiteKey`] for each demanded child that qualifies. Mirrors the
/// forward `walk_demand` but with NO resolution fence and a `descend_query` seam
/// (always `true` for the backward pass) in place of the forward fence checks.
#[allow(clippy::too_many_arguments)]
fn walk_demand(
    layer: &DagLayer,
    regime: BwdRegime,
    consumers: &[u32],
    fences: &HashMap<ExprId, CacheFence>,
    root: RootId,
    value: ExprId,
    descend_query: bool,
    visited: &mut HashSet<(RootId, ExprId)>,
    out: &mut BTreeSet<SiteKey>,
) {
    if !visited.insert((root, value)) {
        return;
    }
    // Fenced cache leaf: the folded cache column terminates the walk — its defining
    // cone is never a backward demand (mirrors the forward resolution fence).
    if fences.contains_key(&value) {
        return;
    }
    match &layer.exprs[value.0 as usize] {
        Expr::Source(src_id) => {
            if let SourceKind::LookupValue { query, .. } = &layer.sources[src_id.0 as usize].kind {
                if descend_query {
                    let q = *query;
                    push_if_site(layer, regime, consumers, fences, root, value, 0, q, out);
                    walk_demand(
                        layer,
                        regime,
                        consumers,
                        fences,
                        root,
                        q,
                        descend_query,
                        visited,
                        out,
                    );
                }
            }
        }
        Expr::Add(children) | Expr::Mul(children) => {
            for (idx, &c) in children.iter().enumerate() {
                push_if_site(
                    layer, regime, consumers, fences, root, value, idx as u32, c, out,
                );
                walk_demand(
                    layer,
                    regime,
                    consumers,
                    fences,
                    root,
                    c,
                    descend_query,
                    visited,
                    out,
                );
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn push_if_site(
    layer: &DagLayer,
    regime: BwdRegime,
    consumers: &[u32],
    fences: &HashMap<ExprId, CacheFence>,
    root: RootId,
    consumer_expr: ExprId,
    input_index: u32,
    value: ExprId,
    out: &mut BTreeSet<SiteKey>,
) {
    if is_site(layer, regime, consumers, fences, value) {
        out.insert(SiteKey {
            root,
            consumer: SiteConsumer::Expr {
                expr: consumer_expr,
                input_index,
            },
            value,
        });
    }
}

/// A demanded value is a backward site iff its (cone-restricted) consumer count is
/// >= 2 AND it is backward-cacheable for `regime`.
fn is_site(
    layer: &DagLayer,
    regime: BwdRegime,
    consumers: &[u32],
    fences: &HashMap<ExprId, CacheFence>,
    value: ExprId,
) -> bool {
    consumers[value.0 as usize] >= 2 && is_cacheable_bwd(layer, regime, fences, value)
}

/// Backward-cacheable value classes (mechanic (iii)): any root's output expr, any
/// compound intermediate (`Add`/`Mul`), a `Read` source leaf (BOTH regimes), and a
/// `VirtualSetup` source leaf in the `Ext` regime ONLY. `Constant`, `Challenge`,
/// and `LookupValue` source leaves are never backward-cacheable. A fenced cache
/// root is a folded `Read(CacheOutput)` LEAF, not a recompute site: it is never
/// admitted as a compound site (checked first, before the root-output class, since
/// a cache root's expr is itself a `Root`).
fn is_cacheable_bwd(
    layer: &DagLayer,
    regime: BwdRegime,
    fences: &HashMap<ExprId, CacheFence>,
    value: ExprId,
) -> bool {
    if fences.contains_key(&value) {
        return false;
    }
    if layer.roots.iter().any(|r| r.expr == value) {
        return true;
    }
    match &layer.exprs[value.0 as usize] {
        Expr::Add(_) | Expr::Mul(_) => true,
        Expr::Source(src_id) => match &layer.sources[src_id.0 as usize].kind {
            SourceKind::Read { .. } => true,
            SourceKind::VirtualSetup { .. } => regime == BwdRegime::Ext,
            SourceKind::Constant { .. }
            | SourceKind::Challenge { .. }
            | SourceKind::LookupValue { .. } => false,
        },
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Backward DRAM traffic floor (reporting-only lower bound).
// ─────────────────────────────────────────────────────────────────────────────

/// Width-weighted count of the distinct `Read` source leaves reachable through the
/// backward rewrite-aware walk (query-edge-descending, fence-free) from the
/// claim-bearing roots.
///
/// In the `Ext` regime every leaf weighs 4 (Ext width). In the `R0` regime each
/// leaf weighs its native field width, resolved via the cross-layer field map
/// (`cross`) for `ReadPlace::{LayerOutput,CacheOutput}` reads, which cannot be
/// typed from one layer alone (see `field_infer`).
///
/// This is a REPORTING-ONLY lower bound: it is role/policy-blind — it ignores the
/// fan-out >= 2 site gate, the R0-vs-Ext leaf role, and the forward materialize
/// policy — and only counts distinct `Read` leaves, so it can undercount the real
/// backward traffic. It is never used as a compile-time budget.
pub fn bwd_traffic_floor(
    layer: &DagLayer,
    regime: BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
) -> usize {
    let fences = bwd_cache_fences(layer);
    let reachable = reachable_exprs_bwd(layer);
    let mut distinct_reads: HashSet<u32> = HashSet::new();
    let mut total = 0usize;
    for &e in &reachable {
        // A fenced cache root is a folded `Read(CacheOutput)` leaf: count it at the
        // cache field's width (Ext regime flattens every leaf to 4). Its own
        // defining cone is behind the fence and never reachable, so no base leaf it
        // depends on is tallied. Keyed by ExprId, so it is naturally distinct from
        // the `Read`-source leaves below.
        if let Some(fence) = fences.get(&e) {
            total += match regime {
                BwdRegime::Ext => 4,
                BwdRegime::R0 => match fence.field {
                    FieldKind::Ext => 4,
                    FieldKind::Base => 1,
                },
            };
            continue;
        }
        if let Expr::Source(src_id) = &layer.exprs[e.0 as usize] {
            let kind = &layer.sources[src_id.0 as usize].kind;
            if let SourceKind::Read { .. } = kind {
                if distinct_reads.insert(src_id.0) {
                    total += match regime {
                        BwdRegime::Ext => 4,
                        BwdRegime::R0 => read_leaf_width_r0(kind, cross),
                    };
                }
            }
        }
    }
    total
}

/// Native R0 width (in cells) of a `Read` source leaf: base storage is width 1;
/// `LayerOutput`/`CacheOutput` reads are resolved via the cross-layer field map
/// (Ext = 4, Base = 1), defaulting to 1 when unresolved (a lower bound never
/// over-counts).
fn read_leaf_width_r0(kind: &SourceKind, cross: &HashMap<ReadPlace, FieldKind>) -> usize {
    match source_field(kind) {
        Ok(FieldKind::Base) => 1,
        Ok(FieldKind::Ext) => 4,
        Err(place) => match cross.get(&place) {
            Some(FieldKind::Ext) => 4,
            _ => 1,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fwd::compile::build_cross_layer_field_map;
    use crate::schedule::{enumerate_site_domain, relation_units_with_caches};
    use cs::gkr_compiler::test_support::build_add_sub_artifact;
    use gkr_eval_ir::{
        BatchingOrder, ClaimInfo, DagLayer, Expr, ExprId, Root, RootGroup, RootId, RootOrigin,
        RootSlot, SinkInfo, SinkKind, SourceId, SourceInfo, SourceKind, VirtualSetupKind,
        lower_dag,
    };
    use std::collections::BTreeMap;

    /// The lowered canonical DAG for the `add_sub_lui_auipc_mop` fixture, the same
    /// artifact the other `dag_ir` tests load (`validate.rs`, `lower/mod.rs`).
    fn add_sub_dag() -> gkr_eval_ir::DagCircuit {
        lower_dag(&build_add_sub_artifact()).expect("lower_dag must succeed")
    }

    /// Layer index of the base layer, which carries the claim-only Constraint roots
    /// and lookup cones the backward-only tests exercise.
    fn layer_with_claim_only(dag: &gkr_eval_ir::DagCircuit) -> usize {
        dag.layers
            .iter()
            .position(|l| {
                l.roots
                    .iter()
                    .any(|r| r.claim.is_some() && r.materialize.is_none())
            })
            .expect("fixture must have a layer with claim-only Constraint roots")
    }

    fn is_read_leaf(layer: &DagLayer, value: ExprId) -> bool {
        matches!(&layer.exprs[value.0 as usize], Expr::Source(s)
            if matches!(layer.sources[s.0 as usize].kind, SourceKind::Read { .. }))
    }

    // (a) ───────────────────────────────────────────────────────────────────────
    #[test]
    fn bwd_roots_covers_all_claims() {
        let dag = add_sub_dag();
        for layer in &dag.layers {
            let claims: BTreeSet<RootId> = layer
                .roots
                .iter()
                .enumerate()
                .filter(|(_, r)| r.claim.is_some())
                .map(|(i, _)| RootId(i as u32))
                .collect();
            let bwd: Vec<RootId> = claim_roots(layer).to_vec();
            let bwd_set: BTreeSet<RootId> = bwd.iter().copied().collect();
            assert_eq!(bwd.len(), bwd_set.len(), "claim_roots has no duplicates");
            assert_eq!(
                bwd_set, claims,
                "claim_roots set == claim-bearing roots set"
            );
            assert_eq!(bwd.len(), claims.len(), "claim_roots count == claim count");
        }
    }

    // (b) ───────────────────────────────────────────────────────────────────────
    #[test]
    fn bwd_units_superset_of_fwd_units() {
        let dag = add_sub_dag();
        let li = layer_with_claim_only(&dag);
        let layer = &dag.layers[li];

        // Every forward relation unit (materialize ∧ claim) must appear as a
        // backward group, keyed by (group, relation_index).
        let fwd_units = relation_units_with_caches(layer).expect("fwd units");
        let bwd_groups = claim_relation_units(layer);
        // RootGroup is Hash+Eq but NOT Ord (model.rs) — use HashSet, not BTreeSet.
        let bwd_keys: std::collections::HashSet<(RootGroup, usize)> = bwd_groups
            .iter()
            .map(|g| {
                let origin = &layer.roots[g[0].0 as usize].claim.as_ref().unwrap().origin;
                (origin.group.clone(), origin.relation_index)
            })
            .collect();
        for u in &fwd_units {
            assert!(
                bwd_keys.contains(&(u.group.clone(), u.relation_index)),
                "fwd unit {:?}/{} must appear in bwd relation units",
                u.group,
                u.relation_index
            );
        }

        // At least one claim-only Constraint root appears in the backward units but
        // in NO forward unit (forward units omit claim-only roots entirely).
        let fwd_members: BTreeSet<RootId> = fwd_units
            .iter()
            .flat_map(|u| u.atom_roots.iter().chain(u.cache_roots.iter()).copied())
            .collect();
        let bwd_members: BTreeSet<RootId> = bwd_groups.iter().flatten().copied().collect();
        let claim_only: Vec<RootId> = layer
            .roots
            .iter()
            .enumerate()
            .filter(|(_, r)| r.claim.is_some() && r.materialize.is_none())
            .map(|(i, _)| RootId(i as u32))
            .collect();
        assert!(
            !claim_only.is_empty(),
            "fixture layer must have claim-only roots"
        );
        let extra = claim_only
            .iter()
            .find(|rid| bwd_members.contains(rid) && !fwd_members.contains(rid));
        assert!(
            extra.is_some(),
            "a claim-only Constraint root must appear in bwd units but no fwd unit"
        );
    }

    // (c) ───────────────────────────────────────────────────────────────────────
    #[test]
    fn bwd_site_domain_covers_constraint_cones() {
        let dag = add_sub_dag();
        let li = layer_with_claim_only(&dag);
        let layer = &dag.layers[li];

        let claim_only: BTreeSet<RootId> = layer
            .roots
            .iter()
            .enumerate()
            .filter(|(_, r)| r.claim.is_some() && r.materialize.is_none())
            .map(|(i, _)| RootId(i as u32))
            .collect();

        let bwd = enumerate_bwd_site_domain(layer, BwdRegime::R0);
        let fwd = enumerate_site_domain(layer);

        // The backward domain has at least one fanout>=2 site attributed to a
        // claim-only Constraint root's cone ...
        assert!(
            bwd.iter().any(|k| claim_only.contains(&k.root)),
            "backward R0 domain must contain a site rooted at a claim-only Constraint root"
        );
        // ... and the forward domain has NONE (it never walks claim-only roots).
        assert!(
            !fwd.iter().any(|k| claim_only.contains(&k.root)),
            "forward domain must not contain any site rooted at a claim-only root"
        );
    }

    // (d) ───────────────────────────────────────────────────────────────────────
    #[test]
    fn read_leaves_admitted_both_regimes() {
        let dag = add_sub_dag();
        let li = layer_with_claim_only(&dag);
        let layer = &dag.layers[li];
        let r0 = enumerate_bwd_site_domain(layer, BwdRegime::R0);
        let ext = enumerate_bwd_site_domain(layer, BwdRegime::Ext);

        // A fanout>=2 Read leaf is a real Global DRAM read in R0 and a FoldSource in
        // Ext: it must have a leaf-site in BOTH regimes.
        let read_site = r0.iter().find(|k| is_read_leaf(layer, k.value));
        assert!(read_site.is_some(), "fixture must have a Read-leaf site");
        let read_site = *read_site.unwrap();
        assert!(r0.contains(&read_site), "Read-leaf site present in R0");
        assert!(
            ext.contains(&read_site),
            "the same Read-leaf site present in Ext"
        );
    }

    #[test]
    fn virtual_setup_leaves_ext_only() {
        // The `add_sub` fixture carries no reused VirtualSetup leaf, so this
        // regime-specific admission rule is exercised on a minimal hand-built layer
        // (matching the in-file hand-built layer style of `schedule.rs`'s tests):
        // a VirtualSetup source reused by two Mul operands, plus a Read leaf so the
        // Ext-only VirtualSetup admission is isolated from the always-on Read rule.
        let layer = DagLayer {
            sources: vec![
                SourceInfo {
                    kind: SourceKind::VirtualSetup {
                        kind: VirtualSetupKind::RangeCheck16Bits,
                    },
                },
                SourceInfo {
                    kind: SourceKind::Read {
                        place: gkr_eval_ir::ReadPlace::BaseLayerWitness { column: 0 },
                    },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = vs (VirtualSetup)
                Expr::Source(SourceId(1)),             // 1 = w  (Read)
                Expr::Mul(vec![ExprId(0), ExprId(1)]), // 2 = vs * w
                Expr::Mul(vec![ExprId(0), ExprId(1)]), // 3 = vs * w (reuses vs and w)
                Expr::Add(vec![ExprId(2), ExprId(3)]), // 4 = root
            ],
            roots: vec![Root {
                expr: ExprId(4),
                materialize: Some(SinkInfo {
                    kind: SinkKind::Export { slot: 0 },
                    field: FieldKind::Ext,
                }),
                claim: Some(ClaimInfo {
                    origin: RootOrigin {
                        group: RootGroup::Gates,
                        relation_index: 0,
                        slot: RootSlot::Output(0),
                    },
                }),
            }],
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            resolutions: BTreeMap::new(),
        };
        let vs = ExprId(0);
        let r0 = enumerate_bwd_site_domain(&layer, BwdRegime::R0);
        let ext = enumerate_bwd_site_domain(&layer, BwdRegime::Ext);
        assert!(
            ext.iter().any(|k| k.value == vs),
            "a fanout>=2 VirtualSetup leaf must have a site in Ext: {ext:?}"
        );
        assert!(
            !r0.iter().any(|k| k.value == vs),
            "a VirtualSetup leaf must NOT have a site in R0: {r0:?}"
        );
        // Sanity: the Read leaf (ExprId(1)) IS admitted in both regimes, so the
        // difference above is genuinely the VirtualSetup rule, not an empty domain.
        assert!(
            r0.iter().any(|k| k.value == ExprId(1)),
            "Read leaf is a site in R0"
        );
    }

    /// A minimal layer with a same-layer cache root `c = a + b` (Ext-field Cache
    /// sink at layer 3 / offset 7, claim `None`) consumed by a claim-bearing output
    /// root `Mul(c, b)`. `a` is reachable ONLY through the cache cone, `b` is also a
    /// direct operand of the output root.
    fn cache_fence_layer() -> DagLayer {
        DagLayer {
            sources: vec![
                SourceInfo {
                    kind: SourceKind::Read {
                        place: gkr_eval_ir::ReadPlace::BaseLayerWitness { column: 0 },
                    },
                },
                SourceInfo {
                    kind: SourceKind::Read {
                        place: gkr_eval_ir::ReadPlace::BaseLayerWitness { column: 1 },
                    },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = a (Read)
                Expr::Source(SourceId(1)),             // 1 = b (Read)
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 2 = c = a + b (cache root)
                Expr::Mul(vec![ExprId(2), ExprId(1)]), // 3 = c * b (output root)
            ],
            roots: vec![
                // Cache root: materialize-only (claim None).
                Root {
                    expr: ExprId(2),
                    materialize: Some(SinkInfo {
                        kind: SinkKind::Cache {
                            layer: 3,
                            offset: 7,
                        },
                        field: FieldKind::Ext,
                    }),
                    claim: None,
                },
                // Claim-bearing output root.
                Root {
                    expr: ExprId(3),
                    materialize: None,
                    claim: Some(ClaimInfo {
                        origin: RootOrigin {
                            group: RootGroup::Gates,
                            relation_index: 0,
                            slot: RootSlot::Output(0),
                        },
                    }),
                },
            ],
            batching: BatchingOrder {
                roots: vec![RootId(1)],
            },
            resolutions: BTreeMap::new(),
        }
    }

    /// A layer with TWO Cache-sink roots: `c = a + b` is claim-less (the ordinary
    /// `emit_cache` shape) and `d = a * b` is claim-BEARING (the `emit_output`
    /// shape, which attaches both `materialize` and `claim` to the same root).
    /// Only the claim-less root should be fenced.
    fn mixed_claim_cache_layer() -> DagLayer {
        DagLayer {
            sources: vec![
                SourceInfo {
                    kind: SourceKind::Read {
                        place: gkr_eval_ir::ReadPlace::BaseLayerWitness { column: 0 },
                    },
                },
                SourceInfo {
                    kind: SourceKind::Read {
                        place: gkr_eval_ir::ReadPlace::BaseLayerWitness { column: 1 },
                    },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = a (Read)
                Expr::Source(SourceId(1)),             // 1 = b (Read)
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 2 = c = a + b (claim-less cache root)
                Expr::Mul(vec![ExprId(0), ExprId(1)]), // 3 = d = a * b (claim-bearing cache root)
            ],
            roots: vec![
                // Claim-less cache root: MUST be fenced.
                Root {
                    expr: ExprId(2),
                    materialize: Some(SinkInfo {
                        kind: SinkKind::Cache {
                            layer: 3,
                            offset: 7,
                        },
                        field: FieldKind::Ext,
                    }),
                    claim: None,
                },
                // Claim-bearing cache root (`emit_output` shape): must NOT be
                // fenced — its gate cone must still be walked, not folded.
                Root {
                    expr: ExprId(3),
                    materialize: Some(SinkInfo {
                        kind: SinkKind::Cache {
                            layer: 3,
                            offset: 8,
                        },
                        field: FieldKind::Ext,
                    }),
                    claim: Some(ClaimInfo {
                        origin: RootOrigin {
                            group: RootGroup::Gates,
                            relation_index: 0,
                            slot: RootSlot::Output(0),
                        },
                    }),
                },
            ],
            batching: BatchingOrder {
                roots: vec![RootId(1)],
            },
            resolutions: BTreeMap::new(),
        }
    }

    #[test]
    fn bwd_cache_fences_only_claim_less_roots() {
        let layer = mixed_claim_cache_layer();
        let fences = bwd_cache_fences(&layer);
        assert!(
            fences.contains_key(&ExprId(2)),
            "claim-less cache root must be fenced: {fences:?}"
        );
        assert!(
            !fences.contains_key(&ExprId(3)),
            "claim-bearing cache root must NOT be fenced (gate cone, not output column): {fences:?}"
        );
    }

    #[test]
    fn cache_fence_map_classifies_cache_roots() {
        let layer = cache_fence_layer();
        let c_expr = ExprId(2);
        let fences = bwd_cache_fences(&layer);
        assert_eq!(fences.len(), 1);
        let f = fences.get(&c_expr).expect("cache expr fenced");
        assert_eq!(
            f.place,
            ReadPlace::CacheOutput {
                layer: 3,
                offset: 7
            }
        );
        assert_eq!(f.field, FieldKind::Ext);
    }

    #[test]
    fn bwd_walk_stops_at_cache_fence() {
        let layer = cache_fence_layer();
        let a_expr = ExprId(0);
        let c_expr = ExprId(2);
        let reach = reachable_exprs_bwd(&layer);
        assert!(!reach.contains(&a_expr), "descended through a cache fence");
        assert!(
            reach.contains(&c_expr),
            "cache expr must stay in the reachable set as a leaf"
        );
    }

    #[test]
    fn bwd_floor_counts_fenced_cache_leaf_ext_width() {
        let layer = cache_fence_layer();
        let cross = HashMap::new();
        let floor = bwd_traffic_floor(&layer, BwdRegime::Ext, &cross);
        // Reachable leaves: the direct Read `b` (4) + the fenced Ext cache leaf `c`
        // (4). The base leaf `a` sits behind the fence and is unreachable (0).
        assert_eq!(floor, 8);
    }

    // (e) ───────────────────────────────────────────────────────────────────────
    #[test]
    fn bwd_floor_ext_ge_4x_distinct_leaves() {
        let dag = add_sub_dag();
        for (li, layer) in dag.layers.iter().enumerate() {
            let cross = build_cross_layer_field_map(&dag);

            // Independently count the backward floor leaves reachable from the
            // claim-bearing roots, mirroring the (cache-fenced) walk: distinct Read
            // source leaves PLUS folded cache leaves (a fenced cache root is a
            // `Read(CacheOutput)` leaf, not a Read source in the arena).
            let fences = super::bwd_cache_fences(layer);
            let reachable = super::reachable_exprs_bwd(layer);
            let mut distinct: BTreeSet<u32> = BTreeSet::new();
            let mut fenced_leaves = 0usize;
            for &e in &reachable {
                if fences.contains_key(&e) {
                    fenced_leaves += 1;
                    continue;
                }
                if let Expr::Source(s) = &layer.exprs[e.0 as usize] {
                    if matches!(layer.sources[s.0 as usize].kind, SourceKind::Read { .. }) {
                        distinct.insert(s.0);
                    }
                }
            }
            let leaves = distinct.len() + fenced_leaves;
            let floor_ext = bwd_traffic_floor(layer, BwdRegime::Ext, &cross);
            let floor_r0 = bwd_traffic_floor(layer, BwdRegime::R0, &cross);
            assert_eq!(
                floor_ext,
                4 * leaves,
                "layer {li}: Ext floor weighs every distinct Read/cache leaf as 4"
            );
            assert!(
                floor_ext >= 4 * leaves,
                "layer {li}: Ext floor >= 4 * distinct leaves"
            );
            // Native R0 widths are 1 (Base) or 4 (Ext), so R0 floor is within
            // [leaves, floor_ext].
            assert!(floor_r0 <= floor_ext, "layer {li}: R0 floor <= Ext floor");
            assert!(floor_r0 >= leaves, "layer {li}: each R0 leaf weighs >= 1");
        }
        // The fixture's base layer must actually have reachable Read leaves, so the
        // floor is a non-trivial positive bound (not vacuously satisfied).
        let li = 0;
        let cross = build_cross_layer_field_map(&dag);
        assert!(bwd_traffic_floor(&dag.layers[li], BwdRegime::Ext, &cross) > 0);
    }
}
