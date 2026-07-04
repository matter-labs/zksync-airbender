//! Persisted, decoded schedule for the forward pass (GKR Stage 2b) — schema v2.
//!
//! v2 replaces the v1 event-replay schema (`StepPlan`/`ReplayEvent`/`DemandKind`,
//! deleted) with a **genome + provenance** shape: `order` (the searched root
//! execution order) and `sites` (a per-site scorer-assigned priority gene, keyed by
//! [`SiteKey`]). The emitter (`gkr_eval_isa`'s `MaterializePolicy::Decisions`) OWNS
//! residency at compile time — it replays `order` and, for each demand, decides
//! admit/evict from the site's priority (see `gkr_eval_isa::fwd::compile::decisions`).
//! There is no persisted step-by-step residency replay anymore: the schedule records
//! WHAT the search decided (order + priorities), not HOW the emitter got there.
//!
//! [`enumerate_site_domain`] is the cs-owned, purely structural site enumerator: it
//! walks a `DagLayer`'s demand graph (Add/Mul operand edges + `LookupValue.query`
//! edges) and returns every value the emitter could plausibly want to cache — the
//! validator uses it to catch a schedule gone stale under DAG drift (§ check b).

use crate::gkr_compiler::dag_ir::{ExprId, FieldKind, RootId};

/// One scheduled circuit at one budget. `layers` is index-aligned with `DagCircuit.layers`.
///
/// No `Eq`/`Hash`: `LayerSchedule.sites` carries an `f64` priority gene.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct CircuitSchedule {
    pub circuit: String,
    /// Cache budget in CELLS (not entry count). The optimizer input, recorded.
    pub budget: usize,
    pub layers: Vec<LayerSchedule>,
}

/// Schedule for one layer. Empty (`order: []`) when the layer has no atom roots.
///
/// No `Eq`/`Hash`: `sites` carries an `f64` priority gene.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct LayerSchedule {
    /// Atom roots (`materialize.is_some() && claim.is_some()`) in execution order;
    /// a permutation of exactly this layer's atom-root set.
    pub order: Vec<RootId>,
    /// Every structural demand site (see [`enumerate_site_domain`]) paired with the
    /// scorer-assigned priority gene the emitter reads at admit/evict time. The
    /// stored key set must equal `enumerate_site_domain(layer)` exactly (validator
    /// check b) — this is provenance, not a cache the validator merely spot-checks.
    pub sites: Vec<(SiteKey, f64)>,
    /// The optimizer's achieved DRAM read traffic (validation/provenance).
    pub predicted_traffic: usize,
    /// `dag_traffic_floor` for this layer (lower bound; validation).
    pub floor: usize,
}

/// Identity of one demand site: a specific consumer's specific operand slot (or a
/// root's own output) demanding `value`. Mirrors `gkr_eval_isa`'s `decisions.rs`
/// copy exactly (Task 6 unifies them; cs is the source of truth going forward).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub struct SiteKey {
    pub root: RootId,
    pub consumer: SiteConsumer,
    pub value: ExprId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub enum SiteConsumer {
    Expr { expr: ExprId, input_index: u32 },
    RootOutput,
}

/// Cell width of a value by field: Ext = 4 (BabyBearExt4 degree), Base = 1.
pub fn field_cells(field: FieldKind) -> usize {
    match field {
        FieldKind::Base => 1,
        FieldKind::Ext => 4,
    }
}

// ─────────────────────────────────────────────────────────────────────────────────
// Structural site enumeration (cs-owned; no gkr_eval_isa dependency — cs is a
// lower-level crate). Task 5's `schedule_search::structure::enumerate_sites` wraps
// this with search-only ordering/grouping rather than duplicating it.
// ─────────────────────────────────────────────────────────────────────────────────

use crate::gkr_compiler::dag_ir::{DagCircuit, DagLayer, Expr, SourceKind};
use std::collections::{BTreeSet, HashSet};

/// Every structural demand site in `layer`: per atom-root occurrence, walk Add/Mul
/// operand edges and `LookupValue.query` edges (deterministic child-position order),
/// and record a site wherever the demanded value has total consumer count >= 2
/// (operand edges + root occurrences + query edges, counted layer-wide) AND is
/// cacheable — a cached-root-output (some root's `expr`), a compound intermediate
/// (`Add`/`Mul`), or a DRAM-`Read` source leaf. Constants, challenges, virtual-setup
/// leaves, and `LookupValue` leaves themselves are never cacheable (zero DRAM traffic
/// / not a real backing read), so they are never sites regardless of fan-out.
///
/// Purely structural — no search/scoring/schedule state. `BTreeSet` + a fixed child
/// walk order make the result independent of any hash-iteration order.
pub fn enumerate_site_domain(layer: &DagLayer) -> BTreeSet<SiteKey> {
    let n = layer.exprs.len();
    let mut consumers = vec![0u32; n];
    for (idx, e) in layer.exprs.iter().enumerate() {
        // A resolution-pruned fold-leaf is fenced by the real emitter (`lower.rs`'s
        // `layer.resolutions.contains_key` gate, checked before ever matching on the
        // expr kind): its children are peeked, never walked. Its own child edges are
        // therefore not real forward demands — skip them so a value ONLY "consumed"
        // under a fenced fold-leaf doesn't spuriously reach the >=2 fan-out gate.
        if layer.resolutions.contains_key(&ExprId(idx as u32)) {
            continue;
        }
        if let Expr::Add(children) | Expr::Mul(children) = e {
            for &c in children {
                consumers[c.0 as usize] += 1;
            }
        }
    }
    for root in &layer.roots {
        // Claim-only Constraint roots (`materialize: None`) are backward-only: they
        // are never in `order` and the forward lowerer never demands their expr
        // through a root-output slot (`lower.rs:1008` skips them — no materialize
        // sink). Only count a root occurrence as a forward consumer when it carries
        // a materialize sink (Output or Cache) — mirrors `floor.rs`'s
        // `r.materialize.is_some()` root filter.
        if root.materialize.is_some() {
            consumers[root.expr.0 as usize] += 1;
        }
    }
    for src in &layer.sources {
        if let SourceKind::LookupValue { query, .. } = &src.kind {
            consumers[query.0 as usize] += 1;
        }
    }

    let mut out: BTreeSet<SiteKey> = BTreeSet::new();
    let mut visited: HashSet<(RootId, ExprId)> = HashSet::new();
    for (i, root) in layer.roots.iter().enumerate() {
        if !(root.materialize.is_some() && root.claim.is_some()) {
            continue;
        }
        let rid = RootId(i as u32);
        if is_site(layer, &consumers, root.expr) {
            out.insert(SiteKey { root: rid, consumer: SiteConsumer::RootOutput, value: root.expr });
        }
        walk_demand(layer, &consumers, rid, root.expr, &mut visited, &mut out);
    }
    out
}

/// Recurse into `value`'s demanded children (memoized per `(root, value)` so shared
/// sub-DAGs are not re-walked exponentially), pushing a `SiteKey` for each demanded
/// child that qualifies as a site.
fn walk_demand(
    layer: &DagLayer,
    consumers: &[u32],
    root: RootId,
    value: ExprId,
    visited: &mut HashSet<(RootId, ExprId)>,
    out: &mut BTreeSet<SiteKey>,
) {
    if !visited.insert((root, value)) {
        return;
    }
    // Resolution-pruned leaf: the real emitter fences it as a terminal Special
    // (`lower.rs:484,517` — `layer.resolutions.contains_key` gate, checked before any
    // Source/Add/Mul match) and never walks the cone underneath. `value` itself may
    // still be demanded and thus a site (already handled by the caller's
    // `push_if_site` before this call, or by the root-output push above) — only the
    // walk BELOW it is fenced here, mirroring `floor.rs`'s identical guard.
    if layer.resolutions.contains_key(&value) {
        return;
    }
    match &layer.exprs[value.0 as usize] {
        Expr::Source(src_id) => {
            // A LookupValue source's `query` is NOT an `Expr` child edge but IS a
            // demand: treat it as one synthetic child at `input_index: 0`.
            if let SourceKind::LookupValue { query, .. } = &layer.sources[src_id.0 as usize].kind {
                let q = *query;
                push_if_site(layer, consumers, root, value, 0, q, out);
                walk_demand(layer, consumers, root, q, visited, out);
            }
        }
        Expr::Add(children) | Expr::Mul(children) => {
            for (idx, &c) in children.iter().enumerate() {
                push_if_site(layer, consumers, root, value, idx as u32, c, out);
                walk_demand(layer, consumers, root, c, visited, out);
            }
        }
    }
}

fn push_if_site(
    layer: &DagLayer,
    consumers: &[u32],
    root: RootId,
    consumer_expr: ExprId,
    input_index: u32,
    value: ExprId,
    out: &mut BTreeSet<SiteKey>,
) {
    if is_site(layer, consumers, value) {
        out.insert(SiteKey {
            root,
            consumer: SiteConsumer::Expr { expr: consumer_expr, input_index },
            value,
        });
    }
}

/// A demanded value is a site iff it is cacheable AND its layer-wide consumer count
/// is >= 2 (a single-use value has no reuse to cache for).
fn is_site(layer: &DagLayer, consumers: &[u32], value: ExprId) -> bool {
    consumers[value.0 as usize] >= 2 && is_cacheable(layer, value)
}

/// Cacheable value classes: a cached-root-output (any root's `expr`), a compound
/// intermediate (`Add`/`Mul`), or a DRAM-`Read` source leaf. Constants, challenges,
/// virtual-setup, and `LookupValue` leaves carry zero DRAM traffic and are never
/// cacheable (mirrors `gkr_eval_isa`'s test-tier `classify_values`/`NodeKind::Literal`
/// classification, translated to `DagLayer` terms).
fn is_cacheable(layer: &DagLayer, value: ExprId) -> bool {
    if layer.roots.iter().any(|r| r.expr == value) {
        return true;
    }
    match &layer.exprs[value.0 as usize] {
        Expr::Add(_) | Expr::Mul(_) => true,
        Expr::Source(src_id) => {
            matches!(layer.sources[src_id.0 as usize].kind, SourceKind::Read { .. })
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────────
// Validator. Public signature unchanged from v1.
// ─────────────────────────────────────────────────────────────────────────────────

/// Pure structural validation of a persisted schedule against its circuit:
/// (a) `order` is a permutation of the layer's atom-root set;
/// (b) the stored site-key set equals `enumerate_site_domain(layer)` exactly (loud
///     staleness `Err` in both directions);
/// (c) every stored priority is finite;
/// (d) `floor <= predicted_traffic`.
pub fn validate_circuit_schedule(circuit: &DagCircuit, sched: &CircuitSchedule) -> Result<(), String> {
    if sched.layers.len() != circuit.layers.len() {
        return Err(format!(
            "schedule has {} layers, circuit has {}",
            sched.layers.len(),
            circuit.layers.len()
        ));
    }
    for (li, (layer, ls)) in circuit.layers.iter().zip(&sched.layers).enumerate() {
        validate_layer_schedule(layer, ls).map_err(|e| format!("layer {li}: {e}"))?;
    }
    Ok(())
}

fn validate_layer_schedule(layer: &DagLayer, ls: &LayerSchedule) -> Result<(), String> {
    // (a) order is a permutation of exactly the atom-root set.
    let atoms: BTreeSet<RootId> = layer
        .roots
        .iter()
        .enumerate()
        .filter(|(_, r)| r.materialize.is_some() && r.claim.is_some())
        .map(|(i, _)| RootId(i as u32))
        .collect();
    let mut seen: HashSet<RootId> = HashSet::new();
    for &r in &ls.order {
        if !seen.insert(r) {
            return Err(format!("order has duplicate root {}", r.0));
        }
    }
    let order_set: BTreeSet<RootId> = ls.order.iter().copied().collect();
    if order_set != atoms {
        return Err(format!(
            "order ({} roots) is not a permutation of the atom-root set ({} roots)",
            ls.order.len(),
            atoms.len()
        ));
    }

    // (b) stored site-key set == enumerate_site_domain(layer) exactly.
    let mut stored: BTreeSet<SiteKey> = BTreeSet::new();
    for (k, _) in &ls.sites {
        if !stored.insert(*k) {
            return Err(format!("sites has a duplicate SiteKey for value {}", k.value.0));
        }
    }
    let domain = enumerate_site_domain(layer);
    check_site_domain_match(&stored, &domain)?;

    // (c) every priority is finite.
    for (k, p) in &ls.sites {
        if !p.is_finite() {
            return Err(format!(
                "site priority for root {} value {} is not finite ({p})",
                k.root.0, k.value.0
            ));
        }
    }

    // (d) floor <= predicted_traffic.
    if ls.floor > ls.predicted_traffic {
        return Err(format!("floor {} > predicted_traffic {}", ls.floor, ls.predicted_traffic));
    }
    Ok(())
}

/// Isolated (and independently testable — see the brief's Step 1) site-set-equality
/// check: `stored` must equal `domain` exactly. Reports whichever side has an extra
/// entry (both directions are real staleness, not just one).
fn check_site_domain_match(stored: &BTreeSet<SiteKey>, domain: &BTreeSet<SiteKey>) -> Result<(), String> {
    if let Some(extra) = stored.difference(domain).next() {
        return Err(format!(
            "stale schedule: stored site (root {}, value {}) is not in the structural domain",
            extra.root.0, extra.value.0
        ));
    }
    if let Some(missing) = domain.difference(stored).next() {
        return Err(format!(
            "stale schedule: structural site (root {}, value {}) is missing from the stored set",
            missing.root.0, missing.value.0
        ));
    }
    Ok(())
}

#[cfg(test)]
mod validator_tests {
    use super::*;
    use crate::gkr_compiler::dag_ir::*;
    use std::collections::BTreeMap;

    // A 1-layer circuit: one atom root (Output+claim) over an Ext add, plus one Base source.
    // exprs: [Source(0)=Base read, Source(1)=Base read, Add([0,1])=Base]; root.expr = ExprId(2).
    fn demo_circuit() -> DagCircuit {
        let layer = DagLayer {
            sources: vec![
                SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 0 } } },
                SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 1 } } },
            ],
            exprs: vec![Expr::Source(SourceId(0)), Expr::Source(SourceId(1)), Expr::Add(vec![ExprId(0), ExprId(1)])],
            roots: vec![Root {
                expr: ExprId(2),
                materialize: Some(SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Base }),
                claim: Some(ClaimInfo { origin: RootOrigin {
                    group: RootGroup::Gates, relation_index: 0, slot: RootSlot::Output(0),
                } }),
            }],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        DagCircuit { layers: vec![layer], globals: DagGlobals::default() }
    }

    fn ok_schedule() -> CircuitSchedule {
        CircuitSchedule {
            circuit: "demo".into(),
            budget: 16,
            layers: vec![LayerSchedule {
                order: vec![RootId(0)],
                sites: vec![],
                predicted_traffic: 1,
                floor: 1,
            }],
        }
    }

    #[test]
    fn accepts_valid_schedule() {
        assert!(validate_circuit_schedule(&demo_circuit(), &ok_schedule()).is_ok());
    }

    #[test]
    fn rejects_layer_count_mismatch() {
        let mut s = ok_schedule();
        s.layers.push(LayerSchedule { order: vec![], sites: vec![], predicted_traffic: 0, floor: 0 });
        assert!(validate_circuit_schedule(&demo_circuit(), &s).is_err());
    }

    #[test]
    fn rejects_order_out_of_range_root() {
        // RootId(1) does not exist (demo_circuit has 1 root) — covers the range case.
        let mut s = ok_schedule();
        s.layers[0].order = vec![RootId(1)];
        let err = validate_circuit_schedule(&demo_circuit(), &s).unwrap_err();
        assert!(err.contains("order"), "error must name the order check, got: {err}");
    }

    #[test]
    fn rejects_non_atom_root_in_order() {
        // An IN-RANGE root that is not an atom (claim: None) must be rejected — isolates the
        // atom-set check from the out-of-range case above.
        let mut c = demo_circuit();
        c.layers[0].roots.push(Root {
            expr: ExprId(2),
            materialize: Some(SinkInfo { kind: SinkKind::Export { slot: 1 }, field: FieldKind::Base }),
            claim: None,
        });
        let mut s = ok_schedule();
        s.layers[0].order = vec![RootId(1)]; // in range now (2 roots), but not an atom root
        let err = validate_circuit_schedule(&c, &s).unwrap_err();
        assert!(err.contains("order"), "error must name the order check, got: {err}");
    }

    #[test]
    fn rejects_duplicate_root_in_order() {
        let mut c = demo_circuit();
        // A second atom root sharing relation_index/slot is irrelevant here — we only need
        // `order` to contain a duplicate of an existing root id.
        c.layers[0].roots[0].claim = Some(ClaimInfo {
            origin: RootOrigin { group: RootGroup::Gates, relation_index: 0, slot: RootSlot::Output(0) },
        });
        let mut s = ok_schedule();
        s.layers[0].order = vec![RootId(0), RootId(0)];
        let err = validate_circuit_schedule(&c, &s).unwrap_err();
        assert!(err.contains("order"), "error must name the order check, got: {err}");
    }

    #[test]
    fn rejects_stale_stored_site_not_in_domain() {
        // demo_circuit's single Add has no reused operand (x, y each consumed once) so its
        // structural site domain is EMPTY. A stored site is therefore stale.
        let mut s = ok_schedule();
        s.layers[0].sites = vec![(
            SiteKey { root: RootId(0), consumer: SiteConsumer::RootOutput, value: ExprId(2) },
            1.0,
        )];
        let err = validate_circuit_schedule(&demo_circuit(), &s).unwrap_err();
        assert!(err.contains("stale"), "error must name the staleness check, got: {err}");
    }

    #[test]
    fn rejects_stale_domain_site_missing_from_stored() {
        // x = Source(0) reused as Add(x, x) — x is a DRAM-Read leaf consumed twice, so it is
        // a genuine structural site the schedule must record.
        let layer = DagLayer {
            sources: vec![SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 0 } } }],
            exprs: vec![Expr::Source(SourceId(0)), Expr::Add(vec![ExprId(0), ExprId(0)])],
            roots: vec![Root {
                expr: ExprId(1),
                materialize: Some(SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Base }),
                claim: Some(ClaimInfo { origin: RootOrigin {
                    group: RootGroup::Gates, relation_index: 0, slot: RootSlot::Output(0),
                } }),
            }],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        let c = DagCircuit { layers: vec![layer], globals: DagGlobals::default() };
        let s = CircuitSchedule {
            circuit: "demo".into(),
            budget: 16,
            layers: vec![LayerSchedule { order: vec![RootId(0)], sites: vec![], predicted_traffic: 1, floor: 1 }],
        };
        let err = validate_circuit_schedule(&c, &s).unwrap_err();
        assert!(err.contains("stale"), "error must name the staleness check, got: {err}");
    }

    #[test]
    fn rejects_nan_priority() {
        let mut s = ok_schedule();
        s.layers[0].sites = vec![(
            SiteKey { root: RootId(0), consumer: SiteConsumer::RootOutput, value: ExprId(2) },
            f64::NAN,
        )];
        // NaN would also fail the domain-match check (stale), so pair it with a matching
        // domain site: use the reused-leaf layer instead, where the domain is non-empty.
        let layer = DagLayer {
            sources: vec![SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 0 } } }],
            exprs: vec![Expr::Source(SourceId(0)), Expr::Add(vec![ExprId(0), ExprId(0)])],
            roots: vec![Root {
                expr: ExprId(1),
                materialize: Some(SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Base }),
                claim: Some(ClaimInfo { origin: RootOrigin {
                    group: RootGroup::Gates, relation_index: 0, slot: RootSlot::Output(0),
                } }),
            }],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        let c = DagCircuit { layers: vec![layer.clone()], globals: DagGlobals::default() };
        let domain = enumerate_site_domain(&layer);
        assert!(!domain.is_empty(), "test setup: expected a non-empty structural site domain");
        // Supply the FULL domain (so check (b) passes) with one entry's priority set to NaN.
        s.layers[0].sites =
            domain.iter().enumerate().map(|(i, &k)| (k, if i == 0 { f64::NAN } else { 0.0 })).collect();
        s.layers[0].order = vec![RootId(0)];
        let err = validate_circuit_schedule(&c, &s).unwrap_err();
        assert!(err.contains("finite"), "error must name the finiteness check, got: {err}");
    }

    #[test]
    fn rejects_infinite_priority() {
        let layer = DagLayer {
            sources: vec![SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 0 } } }],
            exprs: vec![Expr::Source(SourceId(0)), Expr::Add(vec![ExprId(0), ExprId(0)])],
            roots: vec![Root {
                expr: ExprId(1),
                materialize: Some(SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Base }),
                claim: Some(ClaimInfo { origin: RootOrigin {
                    group: RootGroup::Gates, relation_index: 0, slot: RootSlot::Output(0),
                } }),
            }],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        let c = DagCircuit { layers: vec![layer.clone()], globals: DagGlobals::default() };
        let domain = enumerate_site_domain(&layer);
        assert!(!domain.is_empty(), "test setup: expected a non-empty structural site domain");
        let sites: Vec<(SiteKey, f64)> = domain
            .iter()
            .enumerate()
            .map(|(i, &k)| (k, if i == 0 { f64::INFINITY } else { 0.0 }))
            .collect();
        let s = CircuitSchedule {
            circuit: "demo".into(),
            budget: 16,
            layers: vec![LayerSchedule { order: vec![RootId(0)], sites, predicted_traffic: 1, floor: 1 }],
        };
        let err = validate_circuit_schedule(&c, &s).unwrap_err();
        assert!(err.contains("finite"), "error must name the finiteness check, got: {err}");
    }

    #[test]
    fn rejects_floor_above_traffic() {
        let mut s = ok_schedule();
        s.layers[0].floor = 100;
        let err = validate_circuit_schedule(&demo_circuit(), &s).unwrap_err();
        assert!(err.contains("floor"), "error must name the floor check, got: {err}");
    }

    #[test]
    fn check_site_domain_match_hand_supplied_stored_extra() {
        let a = SiteKey { root: RootId(0), consumer: SiteConsumer::RootOutput, value: ExprId(1) };
        let stored: BTreeSet<SiteKey> = [a].into_iter().collect();
        let domain: BTreeSet<SiteKey> = BTreeSet::new();
        let err = check_site_domain_match(&stored, &domain).unwrap_err();
        assert!(err.contains("stale"), "error must name the staleness check, got: {err}");
    }

    #[test]
    fn check_site_domain_match_hand_supplied_domain_extra() {
        let a = SiteKey { root: RootId(0), consumer: SiteConsumer::RootOutput, value: ExprId(1) };
        let stored: BTreeSet<SiteKey> = BTreeSet::new();
        let domain: BTreeSet<SiteKey> = [a].into_iter().collect();
        let err = check_site_domain_match(&stored, &domain).unwrap_err();
        assert!(err.contains("stale"), "error must name the staleness check, got: {err}");
    }

    #[test]
    fn check_site_domain_match_equal_sets_ok() {
        let a = SiteKey { root: RootId(0), consumer: SiteConsumer::RootOutput, value: ExprId(1) };
        let stored: BTreeSet<SiteKey> = [a].into_iter().collect();
        let domain: BTreeSet<SiteKey> = [a].into_iter().collect();
        assert!(check_site_domain_match(&stored, &domain).is_ok());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr_compiler::dag_ir::{ExprId, RootId};

    #[test]
    fn circuit_schedule_serde_roundtrip() {
        let sched = CircuitSchedule {
            circuit: "demo".to_string(),
            budget: 16,
            layers: vec![
                LayerSchedule {
                    order: vec![RootId(0), RootId(2)],
                    sites: vec![
                        (
                            SiteKey {
                                root: RootId(0),
                                consumer: SiteConsumer::Expr { expr: ExprId(5), input_index: 1 },
                                value: ExprId(3),
                            },
                            0.5,
                        ),
                        (
                            SiteKey { root: RootId(2), consumer: SiteConsumer::RootOutput, value: ExprId(7) },
                            -2.25,
                        ),
                    ],
                    predicted_traffic: 12,
                    floor: 9,
                },
                LayerSchedule { order: vec![], sites: vec![], predicted_traffic: 0, floor: 0 },
            ],
        };
        let json = serde_json::to_string(&sched).expect("serialize");
        let back: CircuitSchedule = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back, sched);
    }

    #[test]
    fn field_cells_widths() {
        assert_eq!(field_cells(FieldKind::Base), 1);
        assert_eq!(field_cells(FieldKind::Ext), 4);
    }

    // ── enumerate_site_domain ──────────────────────────────────────────────────

    use crate::gkr_compiler::dag_ir::*;
    use std::collections::BTreeMap;

    fn atom_root(expr: ExprId, slot: usize) -> Root {
        Root {
            expr,
            materialize: Some(SinkInfo { kind: SinkKind::Export { slot }, field: FieldKind::Base }),
            claim: Some(ClaimInfo { origin: RootOrigin {
                group: RootGroup::Gates, relation_index: 0, slot: RootSlot::Output(slot),
            } }),
        }
    }

    fn witness(col: usize) -> SourceInfo {
        SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: col } } }
    }

    #[test]
    fn single_use_leaf_is_not_a_site() {
        // x + y, each used exactly once: no reuse, no sites.
        let layer = DagLayer {
            sources: vec![witness(0), witness(1)],
            exprs: vec![Expr::Source(SourceId(0)), Expr::Source(SourceId(1)), Expr::Add(vec![ExprId(0), ExprId(1)])],
            roots: vec![atom_root(ExprId(2), 0)],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        assert!(enumerate_site_domain(&layer).is_empty());
    }

    #[test]
    fn reused_dram_leaf_is_a_site() {
        // x reused: Add(x, x).
        let layer = DagLayer {
            sources: vec![witness(0)],
            exprs: vec![Expr::Source(SourceId(0)), Expr::Add(vec![ExprId(0), ExprId(0)])],
            roots: vec![atom_root(ExprId(1), 0)],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        let domain = enumerate_site_domain(&layer);
        assert_eq!(domain.len(), 2, "both operand edges to x are sites (input_index 0 and 1)");
        for key in &domain {
            assert_eq!(key.value, ExprId(0));
            assert_eq!(key.root, RootId(0));
        }
    }

    #[test]
    fn constant_and_challenge_leaves_are_never_sites_even_when_reused() {
        let layer = DagLayer {
            sources: vec![
                SourceInfo { kind: SourceKind::Constant { value: 7 } },
                SourceInfo {
                    kind: SourceKind::Challenge {
                        reference: ChallengeRef { key: ChallengeKey::ConstraintAggregation, power: ChallengePower::One },
                    },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Add(vec![ExprId(0), ExprId(0), ExprId(1), ExprId(1)]),
            ],
            roots: vec![atom_root(ExprId(2), 0)],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        assert!(enumerate_site_domain(&layer).is_empty());
    }

    #[test]
    fn compound_intermediate_reused_across_two_roots_is_a_site() {
        // s = Add(x, y), shared by two atom roots: Mul(s, s) and Mul(s, z).
        let layer = DagLayer {
            sources: vec![witness(0), witness(1), witness(2)],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 3 = s
                Expr::Mul(vec![ExprId(3), ExprId(3)]), // 4 = rootA
                Expr::Mul(vec![ExprId(3), ExprId(2)]), // 5 = rootB
            ],
            roots: vec![atom_root(ExprId(4), 0), atom_root(ExprId(5), 1)],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
            resolutions: BTreeMap::new(),
        };
        let domain = enumerate_site_domain(&layer);
        // s (ExprId(3)) is demanded 3 times total (twice by rootA, once by rootB); each
        // demand edge is its own SiteKey (distinct consumer/input_index or root).
        assert!(domain.iter().all(|k| k.value == ExprId(3)));
        assert_eq!(domain.len(), 3);
    }

    #[test]
    fn cached_root_output_reused_elsewhere_is_a_site() {
        // p = Add(x, y) is BOTH an atom root's own expr AND reused by a second atom root.
        let layer = DagLayer {
            sources: vec![witness(0), witness(1)],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 2 = p
                Expr::Mul(vec![ExprId(2), ExprId(2)]), // 3 = q = p * p
            ],
            roots: vec![atom_root(ExprId(2), 0), atom_root(ExprId(3), 1)],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
            resolutions: BTreeMap::new(),
        };
        let domain = enumerate_site_domain(&layer);
        // p's RootOutput occurrence (root 0) is a site (consumers = 1 root reg + 2 operand
        // edges from q = 3 >= 2); the two operand edges into q are sites too.
        assert!(domain.contains(&SiteKey { root: RootId(0), consumer: SiteConsumer::RootOutput, value: ExprId(2) }));
        assert_eq!(domain.len(), 3);
    }

    fn constraint_root(expr: ExprId, relation_index: usize) -> Root {
        // Claim-only Constraint root: backward-only, never in `order`, never a
        // forward demand (`materialize: None`).
        Root {
            expr,
            materialize: None,
            claim: Some(ClaimInfo { origin: RootOrigin {
                group: RootGroup::Gates, relation_index, slot: RootSlot::Constraint(0),
            } }),
        }
    }

    fn cache_root(expr: ExprId, layer_idx: usize, offset: usize) -> Root {
        // Materialize-only Cache root: not an atom root (no claim), but its inline
        // materialize write IS a genuine forward demand — must still count.
        Root { expr, materialize: Some(SinkInfo { kind: SinkKind::Cache { layer: layer_idx, offset }, field: FieldKind::Base }), claim: None }
    }

    #[test]
    fn constraint_root_occurrence_does_not_count_as_forward_consumer() {
        // s = Add(x, y) is an atom root's own output AND ALSO a claim-only Constraint
        // root's expr sharing the same value. Before the fix this double-counted s's
        // consumers (1 atom-root reg + 1 constraint-root reg = 2), wrongly making it
        // a RootOutput site; the Constraint occurrence is backward-only and must not
        // count, leaving consumers[s] = 1 -> no site.
        let layer = DagLayer {
            sources: vec![witness(0), witness(1)],
            exprs: vec![Expr::Source(SourceId(0)), Expr::Source(SourceId(1)), Expr::Add(vec![ExprId(0), ExprId(1)])],
            roots: vec![atom_root(ExprId(2), 0), constraint_root(ExprId(2), 1)],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        assert!(enumerate_site_domain(&layer).is_empty());
    }

    #[test]
    fn cache_root_occurrence_still_counts_as_forward_consumer() {
        // s = Add(x, y) is reused: one operand edge (into q = Mul(s, z)) plus a
        // materialize-only Cache root sharing the same expr. The Cache root's inline
        // materialize write is a genuine forward demand, so it must still count
        // toward the >=2 fan-out gate (unlike the Constraint case above).
        let layer = DagLayer {
            sources: vec![witness(0), witness(1), witness(2)],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 3 = s
                Expr::Mul(vec![ExprId(3), ExprId(2)]), // 4 = q = s * z
            ],
            roots: vec![atom_root(ExprId(4), 0), cache_root(ExprId(3), 0, 0)],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        let domain = enumerate_site_domain(&layer);
        assert!(domain.iter().any(|k| k.value == ExprId(3)), "s must still be a site: domain {domain:?}");
    }

    #[test]
    fn resolution_cone_is_fenced_but_real_edges_outside_it_still_produce_sites() {
        // w = Add(x, y) sits BOTH (a) genuinely reused, twice, as rootA's Mul operands
        // (real forward demand) AND (b) as a child of a resolution-pruned fold-leaf
        // (rootB's own expr) that the real emitter fences as a terminal Special
        // (`lower.rs:484/517`) and never descends into. Before the fix, the counting
        // pass and the walk both ignored `layer.resolutions`, so w's fan-out would be
        // inflated (4, not 2) and phantom SiteKeys attributing demands to the fenced
        // fold-leaf would appear alongside the two genuine ones.
        let layer = DagLayer {
            sources: vec![witness(0), witness(1)],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = x
                Expr::Source(SourceId(1)),             // 1 = y
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 2 = w
                Expr::Add(vec![ExprId(2), ExprId(2)]), // 3 = fold-leaf = w + w (RESOLUTION-PRUNED)
                Expr::Mul(vec![ExprId(2), ExprId(2)]), // 4 = rootA = w * w (real, unfenced)
            ],
            roots: vec![atom_root(ExprId(4), 0), atom_root(ExprId(3), 1)],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
            resolutions: [(ExprId(3), ResolutionStrategy::PeekSetup)].into_iter().collect(),
        };
        let domain = enumerate_site_domain(&layer);
        // w's two REAL operand edges (from rootA's Mul) are sites.
        assert!(domain.contains(&SiteKey {
            root: RootId(0),
            consumer: SiteConsumer::Expr { expr: ExprId(4), input_index: 0 },
            value: ExprId(2),
        }));
        assert!(domain.contains(&SiteKey {
            root: RootId(0),
            consumer: SiteConsumer::Expr { expr: ExprId(4), input_index: 1 },
            value: ExprId(2),
        }));
        // No site is ever attributed to the fenced fold-leaf as a consumer: its cone
        // is never walked, so w's two occurrences as ITS children contribute nothing.
        assert!(domain
            .iter()
            .all(|k| !matches!(k.consumer, SiteConsumer::Expr { expr, .. } if expr == ExprId(3))));
        // Exactly the two real sites for w (no phantom extras).
        assert_eq!(domain.iter().filter(|k| k.value == ExprId(2)).count(), 2, "domain: {domain:?}");
    }

    #[test]
    fn lookup_value_query_edge_is_a_demand_site_when_reused() {
        // query = Add(x, x) (itself reused so it's a site), consumed by a LookupValue
        // source. The LookupValue's `query` field is a demand edge onto `query`.
        let layer = DagLayer {
            sources: vec![
                witness(0),
                SourceInfo {
                    kind: SourceKind::LookupValue {
                        kind: LookupValueKind::RangeCheck16Index,
                        set_index: 0,
                        query: ExprId(1),
                    },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Add(vec![ExprId(0), ExprId(0)]), // 1 = query, reused (2 operand edges)
                Expr::Source(SourceId(1)),             // 2 = lv
                Expr::Add(vec![ExprId(2), ExprId(1)]), // 3 = root, ALSO reuses query directly
            ],
            roots: vec![atom_root(ExprId(3), 0)],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };
        let domain = enumerate_site_domain(&layer);
        // query (ExprId(1)) is demanded twice: once by the LookupValue source's query edge,
        // once by the root's Add — consumers = 2 >= 2, so both demand edges are sites. (x,
        // ExprId(0), is separately reused by query's own Add — a different value's sites.)
        let query_sites: Vec<_> = domain.iter().filter(|k| k.value == ExprId(1)).collect();
        assert_eq!(query_sites.len(), 2, "domain: {domain:?}");
        assert!(query_sites.iter().any(|k| k.consumer == SiteConsumer::Expr { expr: ExprId(2), input_index: 0 }),
            "the LookupValue source's query edge must appear as a demand site at input_index 0");
    }

    #[test]
    fn enumerate_site_domain_is_deterministic_across_calls() {
        let layer = DagLayer {
            sources: vec![witness(0), witness(1), witness(2)],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Add(vec![ExprId(0), ExprId(1)]),
                Expr::Mul(vec![ExprId(3), ExprId(3)]),
                Expr::Mul(vec![ExprId(3), ExprId(2)]),
            ],
            roots: vec![atom_root(ExprId(4), 0), atom_root(ExprId(5), 1)],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1)] },
            resolutions: BTreeMap::new(),
        };
        let a = enumerate_site_domain(&layer);
        let b = enumerate_site_domain(&layer);
        assert_eq!(a, b);
    }
}
