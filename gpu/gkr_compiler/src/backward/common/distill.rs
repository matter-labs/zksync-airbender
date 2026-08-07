//! Rebuilds a layer's claim cones into one batching-challenge-combined root.
use std::collections::{BTreeMap, BTreeSet, HashMap};

use gkr_eval_ir::{
    analyze_claim_cone, claim_relation_units, claim_roots, ArenaBuilder, BatchingOrder,
    ChallengeKey, ChallengePower, ChallengeRef, ClaimCone, DagLayer, Expr, ExprId, FieldKind,
    ReadPlace, Root, RootGroup, RootId, RootOrigin, SourceKind,
};

use super::fragment::{decompose_spine, FragmentTable};

pub(crate) struct DistilledLayer {
    pub layer: DagLayer,
    pub regime: crate::BwdRegime,
    pub field_overrides: BTreeMap<ExprId, FieldKind>,
    pub cross_fields: HashMap<ReadPlace, FieldKind>,
    pub fragments: FragmentTable,
    /// Canonically ordered roots and their batching factors.
    pub root_terms: Vec<DistilledRootTerm>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DistilledRootTerm {
    pub canonical_root: RootId,
    pub batching_factor: Option<ExprId>,
}

pub(crate) fn distill(
    layer: &DagLayer,
    regime: crate::BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
) -> DistilledLayer {
    let units = claim_relation_units(layer);
    let order = claim_roots(layer);
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

    let mut terms: Vec<ExprId> = Vec::new();
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
                    batching_factor,
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

    let root = Root {
        expr: spine,
        materialize: None,
        claim: Some(RootOrigin {
            group: RootGroup::Gates,
            relation_index: 0,
        }),
    };

    let rebuilt = DagLayer {
        sources: cx.arena.sources().to_vec(),
        exprs: cx.arena.exprs().to_vec(),
        roots: vec![root],
        batching: BatchingOrder {
            roots: vec![RootId(0)],
        },
        resolutions: BTreeMap::new(),
        forward_skip_roots: BTreeSet::new(),
    };

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
                let kind = self.layer.sources[sid.0 as usize];
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
                    other @ (SourceKind::Constant { .. }
                    | SourceKind::Challenge { .. }
                    | SourceKind::InitsAndTeardownsTopBits { .. }) => {
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
