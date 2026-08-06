//! Persisted offline-search result for the forward pass.
//!
//! The artifact stores the searched relation order and per-site priority genes
//! keyed by [`SiteKey`]. The compiler owns residency decisions; the artifact
//! does not persist a step-by-step execution replay.
//!
//! [`enumerate_site_domain`] is the purely structural site enumerator: it
//! walks a `DagLayer`'s demand graph (Add/Mul operand edges + `LookupValue.query`
//! edges) and returns every value the emitter could plausibly want to cache — the
//! validator uses it to catch a schedule gone stale under DAG drift (§ check b).

use gkr_eval_ir::{ExprId, FieldKind, RootId};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForwardArtifactError {
    Malformed { origin: String, message: String },
    SiteDomainMismatch(String),
    NonFinitePriority(String),
    StructuralMismatch(String),
}

impl fmt::Display for ForwardArtifactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed { origin, message } => {
                write!(f, "malformed forward artifact {origin}: {message}")
            }
            Self::SiteDomainMismatch(message)
            | Self::NonFinitePriority(message)
            | Self::StructuralMismatch(message) => f.write_str(message),
        }
    }
}

impl std::error::Error for ForwardArtifactError {}

pub fn parse_forward_artifact(
    bytes: &[u8],
    origin: &str,
) -> Result<ForwardSearchArtifact, ForwardArtifactError> {
    serde_json::from_slice(bytes).map_err(|error| ForwardArtifactError::Malformed {
        origin: origin.to_owned(),
        message: error.to_string(),
    })
}

/// One scheduled circuit at one budget. `layers` is index-aligned with `DagCircuit.layers`.
///
/// No `Eq`/`Hash`: `ForwardLayerArtifact.sites` carries an `f64` priority gene.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ForwardSearchArtifact {
    pub circuit: String,
    /// Shared-memory cache budget in E4 buckets. The optimizer input, recorded.
    pub budget_buckets: usize,
    pub layers: Vec<ForwardLayerArtifact>,
}

/// Schedule for one layer. Empty (`units: []`) when the layer has no atom roots.
///
/// No `Eq`/`Hash`: `sites` carries an `f64` priority gene.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ForwardLayerArtifact {
    /// The GKR relations (gates) of this layer as self-describing scheduling units,
    /// in execution order. Each [`RelationUnit`] carries its atom roots (the
    /// sumcheck-claim-bearing outputs) plus the Cache intermediate roots it owns
    /// 1:1. The set of units, and each unit's atom/cache roots, must match the
    /// canonical [`relation_units_with_caches`] decomposition exactly (validator
    /// check a). Flat atom execution order = [`ForwardLayerArtifact::atom_order`].
    pub units: Vec<RelationUnit>,
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

/// One GKR relation (gate) as a scheduling unit: its atom roots (claim+materialize,
/// the sumcheck-claim-bearing outputs) plus the Cache-sink intermediate roots it
/// owns 1:1. Identity `(group, relation_index)` mirrors `claim.origin`. Execution
/// order = the enclosing `ForwardLayerArtifact.units` vec order; atom/cache roots within a
/// unit are in canonical `layer.roots` order.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct RelationUnit {
    pub group: RootGroup,
    pub relation_index: usize,
    pub atom_roots: Vec<RootId>,
    pub cache_roots: Vec<RootId>,
}

impl ForwardLayerArtifact {
    /// Flattened atom-root execution order: concatenate each unit's `atom_roots`
    /// in unit (execution) order. This is exactly the sequence the emitter
    /// consumes.
    pub fn atom_order(&self) -> Vec<RootId> {
        self.units
            .iter()
            .flat_map(|u| u.atom_roots.iter().copied())
            .collect()
    }
}

/// Identity of one demand site: a specific consumer's specific operand slot (or a
/// root's own output) demanding `value`. Mirrors `gpu_gkr_compiler`'s `decisions.rs`
/// copy exactly (Task 6 unifies them; cs is the source of truth going forward).
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct SiteKey {
    pub root: RootId,
    pub consumer: SiteConsumer,
    pub value: ExprId,
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
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
// Structural site enumeration (cs-owned; no gpu_gkr_compiler dependency — cs is a
// lower-level crate). Task 5's `schedule_search::structure::enumerate_sites` wraps
// this with search-only ordering/grouping rather than duplicating it.
// ─────────────────────────────────────────────────────────────────────────────────

use gkr_eval_ir::{DagCircuit, DagLayer, Expr, RootGroup, SinkKind, SourceKind};
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
    // KNOWN LOOSENESS (Task-5 review, carried forward): this query-edge fan-out tally
    // is unconditional over `layer.sources` — a `LookupValue` source reachable ONLY
    // under a fenced resolution cone still bumps its query's consumer count, even
    // though the emitter never walks that cone (the fences above only stop the
    // expr-edge counting/walk, not this source-table sweep). Domain-side only: it can
    // classify a value as a site (>= 2 fan-out) that the forward emitter demands less
    // often, never the reverse — so a stored schedule stays validator-compatible; the
    // extra site is just a decision the emitter may never consult.
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
            out.insert(SiteKey {
                root: rid,
                consumer: SiteConsumer::RootOutput,
                value: root.expr,
            });
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
            consumer: SiteConsumer::Expr {
                expr: consumer_expr,
                input_index,
            },
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
/// cacheable (mirrors `gpu_gkr_compiler`'s test-tier `classify_values`/`NodeKind::Literal`
/// classification, translated to `DagLayer` terms).
fn is_cacheable(layer: &DagLayer, value: ExprId) -> bool {
    if layer.roots.iter().any(|r| r.expr == value) {
        return true;
    }
    match &layer.exprs[value.0 as usize] {
        Expr::Add(_) | Expr::Mul(_) => true,
        Expr::Source(src_id) => {
            matches!(
                layer.sources[src_id.0 as usize].kind,
                SourceKind::Read { .. }
            )
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────────
// Canonical relation-unit decomposition (cs-owned; no gpu_gkr_compiler dependency).
// The search (`gpu_gkr_compiler::schedule_search::structure`) wraps this and the
// validator checks stored schedules against it.
// ─────────────────────────────────────────────────────────────────────────────────

/// Canonical relation units for `layer`, in first-occurrence order: atom roots
/// grouped by `claim.origin (group, relation_index)` (members in `layer.roots`
/// order), each Cache-sink+claim-None root assigned to the unique SAME-LAYER
/// relation that consumes its value.
///
/// Layer-local by design (a `&DagLayer` cannot see later layers). A Cache root
/// with no same-layer consuming relation — a cache-only layer or a cache read
/// only cross-layer via `Read{CacheOutput}` — is UNSUPPORTED in Phase 1 and
/// returns `Err`. The committed corpus never triggers this (all caches at layer
/// 0, consumed same-layer, 1:1). This is the single source of truth the search
/// (`gpu_gkr_compiler::schedule_search::structure`) wraps and the validator checks
/// against.
pub fn relation_units_with_caches(layer: &DagLayer) -> Result<Vec<RelationUnit>, String> {
    use std::collections::HashMap;

    // Atom-root grouping (mirrors gpu_gkr_compiler::schedule_search::structure::relation_units).
    let mut units: Vec<RelationUnit> = Vec::new();
    let mut key_to_unit: HashMap<(RootGroup, usize), usize> = HashMap::new();
    for (i, root) in layer.roots.iter().enumerate() {
        if root.materialize.is_none() {
            continue;
        }
        let Some(claim) = root.claim.as_ref() else {
            continue;
        };
        let key = (claim.origin.group.clone(), claim.origin.relation_index);
        let idx = *key_to_unit.entry(key.clone()).or_insert_with(|| {
            units.push(RelationUnit {
                group: key.0.clone(),
                relation_index: key.1,
                atom_roots: Vec::new(),
                cache_roots: Vec::new(),
            });
            units.len() - 1
        });
        units[idx].atom_roots.push(RootId(i as u32));
    }

    // Per-unit reachable expr set (transitive Add/Mul children + LookupValue.query
    // from each atom root's expr). Plain closure — matches the validated probe;
    // NOT resolution-fenced. Models AUTHORITATIVE relation ownership ("which
    // relation's authoritative expr contains this cache expr"), NOT fwd-VM
    // forward-demand consumption (which would
    // fence resolution cones like enumerate_site_domain, schedule.rs:166-173). A
    // cache reachable only under a resolution-fenced cone is still owned by that
    // relation for provenance.
    let reach: Vec<HashSet<ExprId>> = units
        .iter()
        .map(|u| relation_reachable_exprs(layer, &u.atom_roots))
        .collect();

    // Assign each Cache root to its unique same-layer consuming relation.
    for (i, root) in layer.roots.iter().enumerate() {
        let is_cache = matches!(
            root.materialize.as_ref().map(|s| &s.kind),
            Some(SinkKind::Cache { .. })
        ) && root.claim.is_none();
        if !is_cache {
            continue;
        }
        let e = root.expr;
        let owners: Vec<usize> = (0..units.len())
            .filter(|&u| reach[u].contains(&e))
            .collect();
        match owners.as_slice() {
            [u] => units[*u].cache_roots.push(RootId(i as u32)),
            [] => {
                return Err(format!(
                    "unsupported: cache root {} (expr {}) has no same-layer consuming relation \
                     (cache-only or cross-layer ownership is not representable in Phase 1)",
                    i, e.0
                ));
            }
            many => {
                return Err(format!(
                    "cache root {} (expr {}) is consumed by {} relations; expected exactly 1 \
                     (shared-across-relations caches are not representable)",
                    i,
                    e.0,
                    many.len()
                ));
            }
        }
    }
    Ok(units)
}

/// Transitive dependency closure of a relation's atom-root exprs over `Expr::Add`/
/// `Expr::Mul` child edges and `SourceKind::LookupValue.query` edges. Includes the
/// atom-root exprs themselves. Deterministic; no scoring/schedule state.
fn relation_reachable_exprs(layer: &DagLayer, atom_roots: &[RootId]) -> HashSet<ExprId> {
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut stack: Vec<ExprId> = atom_roots
        .iter()
        .map(|&r| layer.roots[r.0 as usize].expr)
        .collect();
    while let Some(e) = stack.pop() {
        if !seen.insert(e) {
            continue;
        }
        match &layer.exprs[e.0 as usize] {
            Expr::Add(children) | Expr::Mul(children) => {
                for &c in children {
                    stack.push(c);
                }
            }
            Expr::Source(src_id) => {
                if let SourceKind::LookupValue { query, .. } =
                    &layer.sources[src_id.0 as usize].kind
                {
                    stack.push(*query);
                }
            }
        }
    }
    seen
}

// ─────────────────────────────────────────────────────────────────────────────────
// Validator.
// ─────────────────────────────────────────────────────────────────────────────────

/// Pure structural validation of a persisted schedule against its circuit:
/// (a) `units` matches `relation_units_with_caches(layer)` exactly — same relation
///     identities (no dup, full coverage) and, per relation, byte-identical ordered
///     `atom_roots` and `cache_roots` (a within-unit swap is rejected);
/// (b) the stored site-key set equals `enumerate_site_domain(layer)` exactly (loud
///     staleness `Err` in both directions);
/// (c) every stored priority is finite;
/// (d) `floor <= predicted_traffic`.
pub(crate) fn validate_forward_artifact_inner(
    circuit: &DagCircuit,
    sched: &ForwardSearchArtifact,
) -> Result<(), String> {
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

pub fn validate_forward_artifact(
    circuit: &DagCircuit,
    artifact: &ForwardSearchArtifact,
) -> Result<(), ForwardArtifactError> {
    validate_forward_artifact_inner(circuit, artifact).map_err(|message| {
        if message.contains("not finite") {
            ForwardArtifactError::NonFinitePriority(message)
        } else if message.contains("site") {
            ForwardArtifactError::SiteDomainMismatch(message)
        } else {
            ForwardArtifactError::StructuralMismatch(message)
        }
    })
}

fn validate_layer_schedule(layer: &DagLayer, ls: &ForwardLayerArtifact) -> Result<(), String> {
    // (a) units match the canonical relation-unit decomposition exactly.
    let canonical = relation_units_with_caches(layer)?; // propagates a4 unsupported-cache Err
    // (a4 also fires here if a stored schedule references an unsupported cache class.)
    // NOTE: RootGroup is Hash+Eq but NOT Ord (model.rs:176-180) — use HashMap, not BTreeMap.
    use std::collections::HashMap;
    let canon_by_id: HashMap<(RootGroup, usize), &RelationUnit> = canonical
        .iter()
        .map(|u| ((u.group.clone(), u.relation_index), u))
        .collect();

    // (a1) identity coverage: stored unit identities == canonical identities, no dup.
    let mut seen_ids: HashMap<(RootGroup, usize), ()> = HashMap::new();
    for u in &ls.units {
        let id = (u.group.clone(), u.relation_index);
        if seen_ids.insert(id.clone(), ()).is_some() {
            return Err(format!("units has duplicate relation {:?}/{}", id.0, id.1));
        }
        // (a2/a3) exact-ordered atom_roots + cache_roots against canonical.
        let Some(c) = canon_by_id.get(&id) else {
            return Err(format!(
                "stale schedule: unit {:?}/{} is not a relation of this layer",
                id.0, id.1
            ));
        };
        if u.atom_roots != c.atom_roots {
            return Err(format!(
                "unit {:?}/{}: atom_roots {:?} != canonical {:?} (order-exact)",
                id.0, id.1, u.atom_roots, c.atom_roots
            ));
        }
        if u.cache_roots != c.cache_roots {
            return Err(format!(
                "unit {:?}/{}: cache_roots {:?} != canonical {:?} (order-exact)",
                id.0, id.1, u.cache_roots, c.cache_roots
            ));
        }
    }
    if seen_ids.len() != canonical.len() {
        return Err(format!(
            "units cover {} relations, layer has {}",
            seen_ids.len(),
            canonical.len()
        ));
    }

    // (b) stored site-key set == enumerate_site_domain(layer) exactly.
    let mut stored: BTreeSet<SiteKey> = BTreeSet::new();
    for (k, _) in &ls.sites {
        if !stored.insert(*k) {
            return Err(format!(
                "sites has a duplicate SiteKey for value {}",
                k.value.0
            ));
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
        return Err(format!(
            "floor {} > predicted_traffic {}",
            ls.floor, ls.predicted_traffic
        ));
    }
    Ok(())
}

/// Isolated (and independently testable — see the brief's Step 1) site-set-equality
/// check: `stored` must equal `domain` exactly. Reports whichever side has an extra
/// entry (both directions are real staleness, not just one).
fn check_site_domain_match(
    stored: &BTreeSet<SiteKey>,
    domain: &BTreeSet<SiteKey>,
) -> Result<(), String> {
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
