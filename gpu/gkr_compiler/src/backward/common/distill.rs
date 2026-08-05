//! Backward distillation (spec §2.2): rebuild a canonical layer's claim cones
//! into a single alpha-combined backward root.
//!
//! `distill` re-interns the reachable claim cones of a canonical [`DagLayer`]
//! into a FRESH [`ArenaBuilder`] (there is no clone-extension constructor),
//! applying the four REV2-pinned rules:
//!   1. Alpha spine: the distilled root expr is
//!      `expr(root_0) + Σ_{i>=1} beta^i · expr(root_i)` over the canonical
//!      [`claim_roots`] (batching) order; `beta^i` is a `Challenge` leaf keyed
//!      [`ChallengeKey::ClaimBatching`] with power `One` (i == 1) or
//!      `Static(i)` (i >= 2). Root 0 is UNSCALED; claim-only constraint roots
//!      consume a power slot like any other backward root.
//!   2. `LookupValue` leaves are replaced by their `query` expr during the
//!      rebuild (the backward pass consumes the authoritative expr, never the
//!      forward peek).
//!   3. In the continuation regime, every origin `Read` and `VirtualSetup`
//!      leaf has `field_overrides[leaf] = Ext`. R0 leaves retain their canonical
//!      field.
//!   4. Field inference is NOT forced: only fold leaves carry an Ext override;
//!      joins recompute via the existing `arith` machinery at compile time.
//!
use std::collections::{BTreeMap, HashMap};

use gkr_eval_ir::{
    ArenaBuilder, BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef, ClaimCone, ClaimInfo,
    DagLayer, Expr, ExprId, FieldKind, ReadPlace, Root, RootGroup, RootId, RootOrigin, RootSlot,
    SourceKind, analyze_claim_cone, claim_relation_units, claim_roots,
};

use super::fragment::{FragmentTable, decompose_spine};

// ── DistilledLayer ────────────────────────────────────────────────────────────

/// The output of backward distillation for one canonical layer + regime.
pub struct DistilledLayer {
    /// REBUILT layer: reachable claim cones re-interned into a FRESH
    /// ArenaBuilder (no clone-extension constructor exists), alpha spine
    /// appended, `resolutions` CLEARED (copied fences would make the fwd
    /// lowerer emit fwd SpecialDescriptors before the bwd hook fires,
    /// lower.rs:769-783). Canonical input layer is NEVER mutated.
    pub layer: DagLayer,
    pub regime: crate::BwdRegime,
    /// Continuation fold leaves carry a forced extension-field type.
    pub field_overrides: BTreeMap<ExprId, FieldKind>,
    /// Cross-layer field map threaded through to compile/floor.
    pub cross_fields: HashMap<ReadPlace, FieldKind>,
    /// Full-decomposition (CS-M5a) view of the alpha spine: each addend split
    /// into fragments (`acc = c_init + Σ recipe_i · value(fragment_i)`). Built
    /// unconditionally from the rebuilt root's Add children; order-dependent
    /// distilled `ExprId`s inside are only cross-run comparable through
    /// [`FragmentTable::stable_view`] / [`FragmentTable::stable_c_init`].
    pub fragments: FragmentTable,
    /// Per-root provenance of the alpha spine, in canonical [`claim_roots`]
    /// (batching) order — one entry per claim-bearing canonical root. Unlike
    /// [`fragments`](Self::fragments), which deliberately MERGES occurrences
    /// across roots (and so loses root identity), this table keeps each root's
    /// own rebuilt cone and batching factor. It is the seam the R0 `acc_c0`
    /// lowering needs to read a materialized root's output column instead of
    /// re-evaluating its cone.
    ///
    /// Construction order (the relation-unit permutation) does NOT affect this
    /// table: entries are recorded by canonical [`RootId`] and then assembled in
    /// `claim_roots` order.
    pub root_terms: Vec<DistilledRootTerm>,
}

/// One canonical root's contribution to the distilled alpha spine.
///
/// `batched_expr` is what the spine actually adds; `value_expr` is the same root
/// UNSCALED. For the first root in canonical [`claim_roots`] order the two are the
/// same `ExprId` and `batching_factor` is `None` (root zero is unscaled by
/// construction, rule 1); for every later root `batched_expr` is
/// `Mul(batching_factor, value_expr)` where the factor is the `ClaimBatching`
/// beta power of that root's canonical batching position.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DistilledRootTerm {
    /// The canonical (pre-distillation) root this term came from.
    pub canonical_root: RootId,
    /// The rebuilt UNSCALED root cone.
    pub value_expr: ExprId,
    /// The rebuilt `Challenge` leaf carrying this root's beta power; `None` for
    /// the first root in canonical batching order.
    pub batching_factor: Option<ExprId>,
    /// The spine addend: `value_expr` for root zero, else
    /// `Mul(batching_factor, value_expr)`.
    pub batched_expr: ExprId,
}

// ── distill ───────────────────────────────────────────────────────────────────

/// Distill `layer` for one backward family in canonical batching order.
pub fn distill(
    layer: &DagLayer,
    regime: crate::BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
) -> DistilledLayer {
    let units = claim_relation_units(layer);
    let order = claim_roots(layer);
    // Fixed beta exponent per backward root = its position in batching order.
    let exponent: HashMap<RootId, usize> = order.iter().enumerate().map(|(i, &r)| (r, i)).collect();

    // Same-layer cache fence: cache-root exprs become `Read(CacheOutput)` fold
    // leaves during the rebuild (mirrors production folding `GKRAddress::Cached`
    // columns), replacing the inlined defining cone. Subsumes cached lookups
    // (their shared expr id IS the fence key).
    let cone = analyze_claim_cone(layer);

    let mut cx = Reintern {
        layer,
        regime,
        arena: ArenaBuilder::new(),
        field_overrides: BTreeMap::new(),
        cone: &cone,
        cross_fields: HashMap::new(),
        memo: HashMap::new(),
    };

    // Alpha spine terms, built in the (possibly permuted) unit order. Exponents
    // stay pinned to the canonical batching position regardless of permutation.
    let mut terms: Vec<ExprId> = Vec::new();
    // Per-root provenance, keyed by CANONICAL root so the permuted construction
    // order below cannot leak into `root_terms` (assembled in `order` after).
    let mut by_root: BTreeMap<RootId, DistilledRootTerm> = BTreeMap::new();
    for unit in &units {
        for &rid in unit {
            let cone = cx.reintern(layer.roots[rid.0 as usize].expr);
            let i = exponent[&rid];
            let (term, batching_factor) = if i == 0 {
                (cone, None)
            } else {
                let power = if i == 1 {
                    ChallengePower::One
                } else {
                    ChallengePower::Static(i as u32)
                };
                let beta_src = cx.arena.intern_source(SourceKind::Challenge {
                    reference: ChallengeRef {
                        key: ChallengeKey::ClaimBatching,
                        power,
                    },
                });
                let beta = cx.arena.source_expr(beta_src);
                (cx.arena.mul(vec![beta, cone]), Some(beta))
            };
            let prev = by_root.insert(
                rid,
                DistilledRootTerm {
                    canonical_root: rid,
                    value_expr: cone,
                    batching_factor,
                    batched_expr: term,
                },
            );
            assert!(
                prev.is_none(),
                "backward root {} appears twice in the relation-unit decomposition",
                rid.0
            );
            terms.push(term);
        }
    }
    assert!(
        !terms.is_empty(),
        "distill requires >= 1 claim-bearing root"
    );
    // Canonical table: `claim_roots` order is the single source of truth, and every
    // backward root must have contributed a spine term (units partition the roots).
    let root_terms: Vec<DistilledRootTerm> = order
        .iter()
        .map(|rid| {
            *by_root
                .get(rid)
                .unwrap_or_else(|| panic!("backward root {} contributed no spine term", rid.0))
        })
        .collect();
    assert_eq!(
        root_terms.len(),
        terms.len(),
        "root_terms must have exactly one entry per spine term"
    );
    let spine = match terms.len() {
        1 => terms[0],
        _ => cx.arena.add(terms),
    };

    // Claim-only synthetic root; the origin is a placeholder (the distilled
    // layer has exactly one backward root, batching is trivial).
    let root = Root {
        expr: spine,
        materialize: None,
        claim: Some(ClaimInfo {
            origin: RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Constraint(0),
            },
        }),
    };

    let rebuilt = DagLayer {
        sources: cx.arena.sources().to_vec(),
        exprs: cx.arena.exprs().to_vec(),
        roots: vec![root],
        batching: BatchingOrder {
            roots: vec![RootId(0)],
        },
        // CLEARED by contract: copied fences would trigger fwd descriptor
        // emission in the shared lowerer before any bwd hook fires.
        resolutions: BTreeMap::new(),
    };

    // Merge the fenced same-layer cache fields into the cross-layer field map so
    // R0 lowering / floor see the right width for the CacheOutput fold leaves.
    // `cross` is usually built per-layer (same-layer places absent, so the merge
    // is a plain insert), but a WHOLE-CIRCUIT map may already carry the same
    // place (e.g. it is also read cross-layer elsewhere) — that is not a
    // conflict as long as the field agrees, so the `assert_eq` below is a
    // double-entry check (same place, same field), not a same-layer-absence
    // invariant.
    let mut cross_fields = cross.clone();
    for (place, field) in cx.cross_fields {
        match cross_fields.get(&place) {
            Some(prev) => assert_eq!(
                *prev, field,
                "cache fence field {field:?} conflicts with cross-layer field {prev:?} for {place:?}"
            ),
            None => {
                cross_fields.insert(place, field);
            }
        }
    }

    // Fragment full-decomposition (CS-M5a Task 2). The spine root is an Add over
    // [term_0, beta·term_1, ...] (built at :169-187); recompute its addends
    // LOCALLY from the rebuilt root (`compile::spine_terms` stays authoritative for
    // the term path — this local mirror serves only fragment decomposition).
    let root_expr = rebuilt.roots[0].expr;
    let spine_children: Vec<ExprId> = match &rebuilt.exprs[root_expr.0 as usize] {
        Expr::Add(children) if !children.is_empty() => children.clone(),
        _ => vec![root_expr],
    };
    let fragments = decompose_spine(&rebuilt, &spine_children);

    DistilledLayer {
        layer: rebuilt,
        regime,
        field_overrides: cx.field_overrides,
        cross_fields,
        fragments,
        root_terms,
    }
}

// ── Cone re-interning ─────────────────────────────────────────────────────────

/// Re-interning context: canonical layer in, fresh arena + side tables out.
struct Reintern<'a> {
    layer: &'a DagLayer,
    regime: crate::BwdRegime,
    arena: ArenaBuilder,
    field_overrides: BTreeMap<ExprId, FieldKind>,
    /// Canonical claim cone, including same-layer cache boundaries where descent stops.
    cone: &'a ClaimCone,
    /// Fenced places' fields, merged into `DistilledLayer::cross_fields`.
    cross_fields: HashMap<ReadPlace, FieldKind>,
    /// canonical ExprId -> distilled ExprId (a rewritten `LookupValue` maps to
    /// its re-interned query expr).
    memo: HashMap<ExprId, ExprId>,
}

impl Reintern<'_> {
    fn reintern(&mut self, e: ExprId) -> ExprId {
        if let Some(&n) = self.memo.get(&e) {
            return n;
        }
        // Fence: a same-layer cache root becomes a `Read(CacheOutput)` fold leaf
        // instead of its inlined defining cone. This fires before the `Expr`
        // match, so it also subsumes cached `LookupValue` leaves (their shared
        // expr id IS the fence key) — the `:LookupValue` rewrite below stays as
        // the fallback for genuinely uncached lookups.
        if let Some(f) = self.cone.cache_boundary(e) {
            let place = f.place.clone();
            let s = self.arena.intern_source(SourceKind::Read {
                place: place.clone(),
            });
            let ne = self.arena.source_expr(s);
            if self.regime == crate::BwdRegime::Ext {
                self.field_overrides.insert(ne, FieldKind::Ext);
            }
            // Record the sink's field so R0 lowering / floor see the right width;
            // same-layer fenced places are absent from the cross-layer field map.
            self.cross_fields.insert(place, f.field);
            self.memo.insert(e, ne);
            return ne;
        }
        let n = match &self.layer.exprs[e.0 as usize] {
            Expr::Source(sid) => {
                let kind = self.layer.sources[sid.0 as usize].kind.clone();
                match kind {
                    // Rule 2: the backward pass consumes the authoritative
                    // query expr; the LookupValue leaf itself is erased.
                    SourceKind::LookupValue { query, .. } => {
                        let n = self.reintern(query);
                        self.memo.insert(e, n);
                        return n;
                    }
                    SourceKind::Read { place } => {
                        let s = self.arena.intern_source(SourceKind::Read {
                            place: place.clone(),
                        });
                        let ne = self.arena.source_expr(s);
                        if self.regime == crate::BwdRegime::Ext {
                            self.field_overrides.insert(ne, FieldKind::Ext);
                        }
                        ne
                    }
                    SourceKind::VirtualSetup { kind } => {
                        let s = self
                            .arena
                            .intern_source(SourceKind::VirtualSetup { kind: kind.clone() });
                        let ne = self.arena.source_expr(s);
                        match self.regime {
                            crate::BwdRegime::Ext => {
                                self.field_overrides.insert(ne, FieldKind::Ext);
                            }
                            crate::BwdRegime::R0 => {}
                        }
                        ne
                    }
                    other @ (SourceKind::Constant { .. } | SourceKind::Challenge { .. }) => {
                        let s = self.arena.intern_source(other);
                        self.arena.source_expr(s)
                    }
                }
            }
            Expr::Add(children) => {
                let ch = children.clone();
                let nc: Vec<ExprId> = ch.iter().map(|&c| self.reintern(c)).collect();
                self.arena.add(nc)
            }
            Expr::Mul(children) => {
                let ch = children.clone();
                let nc: Vec<ExprId> = ch.iter().map(|&c| self.reintern(c)).collect();
                self.arena.mul(nc)
            }
        };
        self.memo.insert(e, n);
        n
    }
}
