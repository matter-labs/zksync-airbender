//! Backward distillation (spec §2.2): rebuild a canonical layer's claim cones
//! into a single alpha-combined backward root.
//!
//! `distill` re-interns the reachable claim cones of a canonical [`DagLayer`]
//! into a FRESH [`ArenaBuilder`] (there is no clone-extension constructor),
//! applying the four REV2-pinned rules:
//!   1. Alpha spine: the distilled root expr is
//!      `expr(root_0) + Σ_{i>=1} beta^i · expr(root_i)` over the canonical
//!      [`bwd_roots`] (batching) order; `beta^i` is a `Challenge` leaf keyed
//!      [`ChallengeKey::ClaimBatching`] with power `One` (i == 1) or
//!      `Static(i)` (i >= 2). Root 0 is UNSCALED; claim-only constraint roots
//!      consume a power slot like any other backward root.
//!   2. `LookupValue` leaves are replaced by their `query` expr during the
//!      rebuild (the backward pass consumes the authoritative expr, never the
//!      forward peek). Decoder-strategy cones (a `PeekDecoder` resolution key
//!      reachable in the claim cone — directly, since same-layer cache reads
//!      are aliased to the cache expression by `lower/mod.rs`) set
//!      `skipped_decoder` and put the layer OUT of v1 in BOTH regimes; the
//!      rebuild still completes (no panic).
//!   3. `Ext` regime: every origin `Read` and `VirtualSetup` leaf becomes a
//!      special-source leaf carrying a STRUCTURAL [`BwdSpecial::FoldSource`]
//!      desc with `field_overrides[leaf] = Ext`. `R0` regime: `Read` leaves
//!      stay ordinary backings; `VirtualSetup` leaves carry a
//!      [`BwdSpecial::VirtualSetup`] desc (typed kind, no field override).
//!   4. Field inference is NOT forced: only fold leaves carry an Ext override;
//!      joins recompute via the existing `arith` machinery at compile time.
//!
//! Binding (which stored representation a fold reads at a given round) is
//! per-run: [`bind`] maps a [`MaterializationPolicy`] and a round index to a
//! [`FoldState`] per descriptor, leaving the compiled program round- and
//! policy-invariant.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use cs::gkr_compiler::dag_ir::{
    bwd_relation_units, bwd_roots, enumerate_bwd_site_domain, ArenaBuilder, BatchingOrder,
    BwdRegime, ChallengeKey, ChallengePower, ChallengeRef, ClaimInfo, DagLayer, Expr, ExprId,
    FieldKind, ReadPlace, ResolutionStrategy, Root, RootGroup, RootId, RootOrigin, RootSlot,
    SiteKey, SourceKind,
};

use super::source::{BwdSpecial, BwdSpecialTable, FoldState, MaterializationPolicy, OriginLeaf};

// ── DistilledLayer ────────────────────────────────────────────────────────────

/// The output of backward distillation for one canonical layer + regime.
pub struct DistilledLayer {
    /// REBUILT layer: reachable claim cones re-interned into a FRESH
    /// ArenaBuilder (no clone-extension constructor exists), alpha spine
    /// appended, `resolutions` CLEARED (copied fences would make the fwd
    /// lowerer emit fwd SpecialDescriptors before the bwd hook fires,
    /// lower.rs:769-783). Canonical input layer is NEVER mutated.
    pub layer: DagLayer,
    /// The single backward root (alpha-combined), claim-only shape.
    pub root: RootId,
    /// STRUCTURAL descs (origin only, REV2).
    pub specials: BwdSpecialTable,
    pub regime: BwdRegime,
    /// First-class lowering inputs (REV2 — not an overlay the canonical
    /// field inference can ignore): distilled leaf -> desc, and distilled
    /// leaf -> forced field (Ext for fold leaves).
    pub leaf_descs: BTreeMap<ExprId, u16>,
    pub field_overrides: BTreeMap<ExprId, FieldKind>,
    /// Cross-layer field map threaded through to compile/floor.
    pub cross_fields: HashMap<ReadPlace, FieldKind>,
    /// Canonical relation-unit metadata (alpha order/exponents) — kept for
    /// Task 8's order genes; NOT used for site identity.
    pub unit_order: Vec<Vec<RootId>>,
    /// Decoder-bearing cone detected: layer is OUT of v1 in BOTH regimes.
    pub skipped_decoder: bool,
}

// ── distill ───────────────────────────────────────────────────────────────────

/// Distill `layer` for `regime`. `unit_permutation` permutes the CANONICAL
/// relation units ([`bwd_relation_units`]) when rebuilding the top-level alpha
/// Add — each root KEEPS its fixed beta exponent (its position in the canonical
/// [`bwd_roots`] batching order), so any permutation is value-identical by
/// commutativity; ordering only matters for lowering (it drives the re-interning
/// order, hence the distilled `ExprId` numbering). `None` = canonical order.
pub fn distill(
    layer: &DagLayer,
    regime: BwdRegime,
    cross: &HashMap<ReadPlace, FieldKind>,
    unit_permutation: Option<&[usize]>,
) -> DistilledLayer {
    let units = bwd_relation_units(layer);
    let order = bwd_roots(layer);
    // Fixed beta exponent per backward root = its position in batching order.
    let exponent: HashMap<RootId, usize> =
        order.iter().enumerate().map(|(i, &r)| (r, i)).collect();

    let unit_indices: Vec<usize> = match unit_permutation {
        None => (0..units.len()).collect(),
        Some(p) => {
            assert_eq!(p.len(), units.len(), "unit_permutation length must match unit count");
            let seen: BTreeSet<usize> = p.iter().copied().collect();
            assert_eq!(seen.len(), p.len(), "unit_permutation must not repeat indices");
            assert!(
                seen.iter().all(|&i| i < units.len()),
                "unit_permutation indices must be in range"
            );
            p.to_vec()
        }
    };

    let skipped_decoder = claim_cone_has_decoder(layer);

    let mut cx = Reintern {
        layer,
        regime,
        arena: ArenaBuilder::new(),
        specials: BwdSpecialTable::default(),
        leaf_descs: BTreeMap::new(),
        field_overrides: BTreeMap::new(),
        memo: HashMap::new(),
    };

    // Alpha spine terms, built in the (possibly permuted) unit order. Exponents
    // stay pinned to the canonical batching position regardless of permutation.
    let mut terms: Vec<ExprId> = Vec::new();
    for &ui in &unit_indices {
        for &rid in &units[ui] {
            let cone = cx.reintern(layer.roots[rid.0 as usize].expr);
            let i = exponent[&rid];
            let term = if i == 0 {
                cone
            } else {
                let power =
                    if i == 1 { ChallengePower::One } else { ChallengePower::Static(i as u32) };
                let beta_src = cx.arena.intern_source(SourceKind::Challenge {
                    reference: ChallengeRef { key: ChallengeKey::ClaimBatching, power },
                });
                let beta = cx.arena.source_expr(beta_src);
                cx.arena.mul(vec![beta, cone])
            };
            terms.push(term);
        }
    }
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
        batching: BatchingOrder { roots: vec![RootId(0)] },
        // CLEARED by contract: copied fences would trigger fwd descriptor
        // emission in the shared lowerer before any bwd hook fires.
        resolutions: BTreeMap::new(),
    };

    DistilledLayer {
        layer: rebuilt,
        root: RootId(0),
        specials: cx.specials,
        regime,
        leaf_descs: cx.leaf_descs,
        field_overrides: cx.field_overrides,
        cross_fields: cross.clone(),
        unit_order: units,
        skipped_decoder,
    }
}

// ── Cone re-interning ─────────────────────────────────────────────────────────

/// Re-interning context: canonical layer in, fresh arena + side tables out.
struct Reintern<'a> {
    layer: &'a DagLayer,
    regime: BwdRegime,
    arena: ArenaBuilder,
    specials: BwdSpecialTable,
    leaf_descs: BTreeMap<ExprId, u16>,
    field_overrides: BTreeMap<ExprId, FieldKind>,
    /// canonical ExprId -> distilled ExprId (a rewritten `LookupValue` maps to
    /// its re-interned query expr).
    memo: HashMap<ExprId, ExprId>,
}

impl Reintern<'_> {
    fn reintern(&mut self, e: ExprId) -> ExprId {
        if let Some(&n) = self.memo.get(&e) {
            return n;
        }
        let n = match &self.layer.exprs[e.0 as usize] {
            Expr::Source(sid) => {
                let kind = self.layer.sources[sid.0 as usize].kind.clone();
                match kind {
                    // Rule 2: the backward pass consumes the authoritative
                    // query expr; the LookupValue leaf itself is erased.
                    SourceKind::LookupValue { query, .. } => self.reintern(query),
                    SourceKind::Read { place } => {
                        let s = self.arena.intern_source(SourceKind::Read { place: place.clone() });
                        let ne = self.arena.source_expr(s);
                        if self.regime == BwdRegime::Ext {
                            let d = self.specials.intern(BwdSpecial::FoldSource {
                                origin: OriginLeaf::Read(place),
                            });
                            self.leaf_descs.insert(ne, d);
                            self.field_overrides.insert(ne, FieldKind::Ext);
                        }
                        ne
                    }
                    SourceKind::VirtualSetup { kind } => {
                        let s = self
                            .arena
                            .intern_source(SourceKind::VirtualSetup { kind: kind.clone() });
                        let ne = self.arena.source_expr(s);
                        let d = match self.regime {
                            BwdRegime::Ext => {
                                self.field_overrides.insert(ne, FieldKind::Ext);
                                self.specials.intern(BwdSpecial::FoldSource {
                                    origin: OriginLeaf::VirtualSetup { kind },
                                })
                            }
                            BwdRegime::R0 => {
                                self.specials.intern(BwdSpecial::VirtualSetup { kind })
                            }
                        };
                        self.leaf_descs.insert(ne, d);
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

// ── Decoder detection ─────────────────────────────────────────────────────────

/// True iff a `PeekDecoder` resolution key is reachable in the claim cone
/// (query-edge-descending, fence-free — mirrors the private
/// `bwd_schedule::reachable_exprs_bwd` walk). Same-layer cache reads are DAG
/// sharing (`lower/mod.rs` aliases them to the cache expression), so a decoder
/// expr behind a `Cached` alias is directly reachable — no alias map needed.
fn claim_cone_has_decoder(layer: &DagLayer) -> bool {
    let decoder_keys: HashSet<ExprId> = layer
        .resolutions
        .iter()
        .filter(|(_, s)| matches!(s, ResolutionStrategy::PeekDecoder { .. }))
        .map(|(&k, _)| k)
        .collect();
    if decoder_keys.is_empty() {
        return false;
    }
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
        if decoder_keys.contains(&e) {
            return true;
        }
        match &layer.exprs[e.0 as usize] {
            Expr::Source(sid) => {
                if let SourceKind::LookupValue { query, .. } =
                    &layer.sources[sid.0 as usize].kind
                {
                    stack.push(*query);
                }
            }
            Expr::Add(children) | Expr::Mul(children) => stack.extend(children.iter().copied()),
        }
    }
    false
}

// ── Per-run binding ───────────────────────────────────────────────────────────

/// Per-run/per-round binding of structural FoldSources (REV2): the compiled
/// program is round- and policy-invariant; only bindings change.
pub struct BwdBindings {
    /// Indexed by desc (dense, parallel to `DistilledLayer::specials`).
    pub states: Vec<FoldState>,
}

/// Bind every descriptor of `d` for `round` under `policy`.
///
/// `FoldSource`: round 0 has no previous-round buffer, so it always binds
/// `LazyFromOriginals { depth: 0 }`; for round >= 1, `AlwaysMaterialize` binds
/// `Materialized`, and `LazyUpTo(k)` binds `LazyFromOriginals { depth: round }`
/// while `round <= k`, `Materialized` past it. `VirtualSetup` descs (R0-only —
/// in Ext the leaf is a FoldSource) are procedurally generated, never a
/// materialized fold buffer: always `LazyFromOriginals { depth: round }`.
pub fn bind(d: &DistilledLayer, policy: MaterializationPolicy, round: u8) -> BwdBindings {
    let states = (0..d.specials.len())
        .map(|i| match d.specials.get(i as u16).expect("dense desc index") {
            BwdSpecial::VirtualSetup { .. } => FoldState::LazyFromOriginals { depth: round },
            BwdSpecial::FoldSource { .. } => {
                if round == 0 {
                    FoldState::LazyFromOriginals { depth: 0 }
                } else {
                    match policy {
                        MaterializationPolicy::AlwaysMaterialize => FoldState::Materialized,
                        MaterializationPolicy::LazyUpTo(k) => {
                            if round <= k {
                                FoldState::LazyFromOriginals { depth: round }
                            } else {
                                FoldState::Materialized
                            }
                        }
                    }
                }
            }
        })
        .collect();
    BwdBindings { states }
}

// ── Site domain over the rebuilt layer ────────────────────────────────────────

/// The backward site domain of the REBUILT layer (Task 1's walk applied to
/// `d.layer` / `d.regime`) — the identity space compilation actually uses; the
/// canonical-layer enumeration is tests/reporting only (its ExprIds differ).
pub fn distilled_site_domain(d: &DistilledLayer) -> BTreeSet<SiteKey> {
    enumerate_bwd_site_domain(&d.layer, d.regime)
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{
        eval_layer_root, Bf, ChallengeResolver, Ext, FillSource, LookupResolver, LookupValueKind,
        ReadResolver, Resolvers, SinkInfo, SinkKind, SourceId, SourceInfo, VirtualSetupKind,
        VirtualSetupResolver,
    };
    use field::{Field, FieldExtension, PrimeField};

    fn lift(b: Bf) -> Ext {
        <Ext as FieldExtension<Bf>>::from_base(b)
    }

    fn pow(base: Ext, n: u32) -> Ext {
        let mut acc = Ext::ONE;
        for _ in 0..n {
            acc.mul_assign(&base);
        }
        acc
    }

    // ── Stub resolvers ────────────────────────────────────────────────────────

    /// `BaseLayerWitness{column}` -> lift(7·column + row + 1); other places panic.
    struct WitnessRead;
    impl ReadResolver for WitnessRead {
        fn read(&self, place: &ReadPlace, row: usize) -> Ext {
            match place {
                ReadPlace::BaseLayerWitness { column } => {
                    lift(Bf::from_u32_with_reduction(7 * *column as u32 + row as u32 + 1))
                }
                other => panic!("unexpected read place {other:?}"),
            }
        }
    }

    struct ConstLookup(Bf);
    impl LookupResolver for ConstLookup {
        fn lookup(&self, _: &LookupValueKind, _: usize, _: Ext, _: usize) -> Bf {
            self.0
        }
    }

    struct ConstVirtualSetup(Bf);
    impl VirtualSetupResolver for ConstVirtualSetup {
        fn virtual_setup(&self, _: &VirtualSetupKind, _: usize) -> Bf {
            self.0
        }
    }

    /// `ClaimBatching` powers of a fixed beta; any other key panics (the
    /// distilled spine must only introduce ClaimBatching challenges).
    struct BetaChallenge(Ext);
    impl ChallengeResolver for BetaChallenge {
        fn challenge(&self, r: &ChallengeRef) -> Ext {
            assert_eq!(r.key, ChallengeKey::ClaimBatching, "unexpected challenge {r:?}");
            match r.power {
                ChallengePower::One => self.0,
                ChallengePower::Static(i) => pow(self.0, i),
            }
        }
    }

    fn resolvers<'a>(read: &'a WitnessRead, ch: &'a BetaChallenge) -> Resolvers<'a> {
        static LOOKUP: ConstLookup = ConstLookup(Bf::ZERO);
        static VS: ConstVirtualSetup = ConstVirtualSetup(Bf::ZERO);
        Resolvers { read, lookup: &LOOKUP, virtual_setup: &VS, challenge: ch }
    }

    // ── Layer-building helpers ────────────────────────────────────────────────

    fn read_src(column: usize) -> SourceInfo {
        SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column } } }
    }

    fn origin(relation_index: usize, slot: RootSlot) -> RootOrigin {
        RootOrigin { group: RootGroup::Gates, relation_index, slot }
    }

    fn claim_root(expr: ExprId, relation_index: usize) -> Root {
        Root {
            expr,
            materialize: Some(SinkInfo {
                kind: SinkKind::Inner { layer: 1, offset: relation_index },
                field: FieldKind::Ext,
            }),
            claim: Some(ClaimInfo { origin: origin(relation_index, RootSlot::Output(0)) }),
        }
    }

    fn claim_only_root(expr: ExprId, relation_index: usize) -> Root {
        Root {
            expr,
            materialize: None,
            claim: Some(ClaimInfo { origin: origin(relation_index, RootSlot::Constraint(0)) }),
        }
    }

    /// Three-root micro layer: two atoms + one claim-only constraint, over three
    /// shared `Read` leaves.
    ///   r0 = w0 + w1        (Output, unit 0)
    ///   r1 = w0 * w2        (Output, unit 1)
    ///   r2 = w1 + w2        (claim-only Constraint, unit 2)
    fn three_root_layer() -> DagLayer {
        DagLayer {
            sources: vec![read_src(0), read_src(1), read_src(2)],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = w0
                Expr::Source(SourceId(1)),             // 1 = w1
                Expr::Source(SourceId(2)),             // 2 = w2
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 3 = w0 + w1
                Expr::Mul(vec![ExprId(0), ExprId(2)]), // 4 = w0 * w2
                Expr::Add(vec![ExprId(1), ExprId(2)]), // 5 = w1 + w2
            ],
            roots: vec![
                claim_root(ExprId(3), 0),
                claim_root(ExprId(4), 1),
                claim_only_root(ExprId(5), 2),
            ],
            batching: BatchingOrder { roots: vec![RootId(0), RootId(1), RootId(2)] },
            resolutions: BTreeMap::new(),
        }
    }

    // (a) ── Alpha spine: order + powers ───────────────────────────────────────
    #[test]
    fn alpha_spine_order_and_powers() {
        let layer = three_root_layer();
        let cross = HashMap::new();
        let d = distill(&layer, BwdRegime::R0, &cross, None);
        assert!(!d.skipped_decoder);
        assert_eq!(d.unit_order.len(), 3, "three units (distinct relation indices)");

        let read = WitnessRead;
        let beta = lift(Bf::from_u32_with_reduction(11));
        let ch = BetaChallenge(beta);
        let r = resolvers(&read, &ch);

        for row in 0..4 {
            // Canonical side: eval(r0) + beta·eval(r1) + beta²·eval(r2).
            let mut expected = eval_layer_root(&layer, RootId(0), row, &r);
            let mut t1 = eval_layer_root(&layer, RootId(1), row, &r);
            t1.mul_assign(&beta);
            expected.add_assign(&t1);
            let mut t2 = eval_layer_root(&layer, RootId(2), row, &r);
            t2.mul_assign(&pow(beta, 2));
            expected.add_assign(&t2);

            let got = eval_layer_root(&d.layer, d.root, row, &r);
            assert_eq!(got, expected, "alpha spine value mismatch at row {row}");

            // A unit permutation keeps every root's exponent (value-identical).
            let dp = distill(&layer, BwdRegime::R0, &cross, Some(&[2, 0, 1]));
            let got_p = eval_layer_root(&dp.layer, dp.root, row, &r);
            assert_eq!(got_p, expected, "permuted spine must be value-identical (row {row})");
        }
    }

    // (b) ── LookupValue rewrite + decoder skip ────────────────────────────────

    /// One claim root over `lv + w0`, where `lv = LookupValue{query = w0 + 5}`.
    fn lookup_layer() -> DagLayer {
        DagLayer {
            sources: vec![
                read_src(0),
                SourceInfo { kind: SourceKind::Constant { value: 5 } },
                SourceInfo {
                    kind: SourceKind::LookupValue {
                        kind: LookupValueKind::GenericColumn { column: 0 },
                        set_index: 0,
                        query: ExprId(2),
                    },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = w0
                Expr::Source(SourceId(1)),             // 1 = 5
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 2 = w0 + 5 (query)
                Expr::Source(SourceId(2)),             // 3 = lv
                Expr::Add(vec![ExprId(0), ExprId(3)]), // 4 = w0 + lv (root)
            ],
            roots: vec![claim_root(ExprId(4), 0)],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        }
    }

    #[test]
    fn lookup_value_leaf_is_rewritten_to_its_query() {
        let layer = lookup_layer();
        let d = distill(&layer, BwdRegime::R0, &HashMap::new(), None);
        assert!(!d.skipped_decoder);

        // No LookupValue source survives the rebuild.
        assert!(
            !d.layer
                .sources
                .iter()
                .any(|s| matches!(s.kind, SourceKind::LookupValue { .. })),
            "distilled layer must not contain LookupValue sources: {:?}",
            d.layer.sources
        );

        // Value: distilled root == w0 + (w0 + 5), independent of the lookup
        // resolver (which would have returned 0 for the erased lv leaf).
        let read = WitnessRead;
        let ch = BetaChallenge(Ext::ZERO);
        let r = resolvers(&read, &ch);
        for row in 0..3 {
            let w0 = lift(Bf::from_u32_with_reduction(row as u32 + 1));
            let mut expected = w0;
            expected.add_assign(&w0);
            expected.add_assign(&lift(Bf::from_u32_with_reduction(5)));
            let got = eval_layer_root(&d.layer, d.root, row, &r);
            assert_eq!(got, expected, "lookup rewrite value mismatch at row {row}");
        }
    }

    #[test]
    fn reachable_peek_decoder_sets_skipped_flag() {
        let mut layer = lookup_layer();
        // Mark the (reachable) query expr as a PeekDecoder resolution key.
        layer.resolutions.insert(
            ExprId(2),
            ResolutionStrategy::PeekDecoder {
                predicate: ReadPlace::BaseLayerMemory { column: 0 },
                fill: FillSource::DecoderLookupFill,
            },
        );
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            let d = distill(&layer, regime, &HashMap::new(), None);
            assert!(d.skipped_decoder, "reachable PeekDecoder must set skipped_decoder");
            // The rebuild still completes: the distilled layer is well-formed.
            assert_eq!(d.layer.roots.len(), 1);
        }

        // An UNREACHABLE decoder key (dangling expr outside the claim cone)
        // does not skip; a non-decoder strategy on a reachable expr does not
        // skip either.
        let mut l2 = lookup_layer();
        l2.exprs.push(Expr::Add(vec![ExprId(0), ExprId(0)])); // 5 = unreachable
        l2.resolutions.insert(
            ExprId(5),
            ResolutionStrategy::PeekDecoder {
                predicate: ReadPlace::BaseLayerMemory { column: 0 },
                fill: FillSource::DecoderLookupFill,
            },
        );
        l2.resolutions.insert(ExprId(2), ResolutionStrategy::PeekSetup);
        let d2 = distill(&l2, BwdRegime::R0, &HashMap::new(), None);
        assert!(!d2.skipped_decoder, "unreachable decoder key must not skip");
    }

    // (c) ── EXT / R0 leaf rewrite ─────────────────────────────────────────────

    /// One claim root over `(w0 + c7) * vs + w1`.
    fn ext_layer() -> DagLayer {
        DagLayer {
            sources: vec![
                read_src(0),
                read_src(1),
                SourceInfo { kind: SourceKind::Constant { value: 7 } },
                SourceInfo {
                    kind: SourceKind::VirtualSetup { kind: VirtualSetupKind::RangeCheck16Bits },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = w0
                Expr::Source(SourceId(1)),             // 1 = w1
                Expr::Source(SourceId(2)),             // 2 = 7
                Expr::Source(SourceId(3)),             // 3 = vs
                Expr::Add(vec![ExprId(0), ExprId(2)]), // 4 = w0 + 7
                Expr::Mul(vec![ExprId(3), ExprId(4)]), // 5 = (w0+7) * vs
                Expr::Add(vec![ExprId(1), ExprId(5)]), // 6 = root
            ],
            roots: vec![claim_root(ExprId(6), 0)],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        }
    }

    fn distilled_leaves_of(d: &DistilledLayer) -> Vec<(ExprId, SourceKind)> {
        d.layer
            .exprs
            .iter()
            .enumerate()
            .filter_map(|(i, e)| match e {
                Expr::Source(s) => Some((ExprId(i as u32), d.layer.sources[s.0 as usize].kind.clone())),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn ext_regime_rewrites_read_and_virtual_setup_leaves_to_fold_sources() {
        let layer = ext_layer();
        let d = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);

        for (eid, kind) in distilled_leaves_of(&d) {
            match kind {
                SourceKind::Read { place } => {
                    let desc = *d.leaf_descs.get(&eid).expect("Ext Read leaf must carry a desc");
                    assert_eq!(
                        d.specials.get(desc),
                        Some(&BwdSpecial::FoldSource { origin: OriginLeaf::Read(place) }),
                        "Read leaf desc must be a FoldSource with its own place"
                    );
                    assert_eq!(d.field_overrides.get(&eid), Some(&FieldKind::Ext));
                }
                SourceKind::VirtualSetup { kind } => {
                    let desc = *d.leaf_descs.get(&eid).expect("Ext VS leaf must carry a desc");
                    assert_eq!(
                        d.specials.get(desc),
                        Some(&BwdSpecial::FoldSource {
                            origin: OriginLeaf::VirtualSetup { kind }
                        }),
                    );
                    assert_eq!(d.field_overrides.get(&eid), Some(&FieldKind::Ext));
                }
                SourceKind::Constant { .. } => {
                    assert!(!d.leaf_descs.contains_key(&eid), "constants carry no desc");
                    assert!(!d.field_overrides.contains_key(&eid), "constants keep inference");
                }
                other => panic!("unexpected distilled leaf {other:?}"),
            }
        }
        // 2 Read leaves + 1 VirtualSetup leaf = 3 distinct structural descs.
        assert_eq!(d.specials.len(), 3);
        assert_eq!(d.leaf_descs.len(), 3);
    }

    #[test]
    fn r0_regime_keeps_reads_ordinary_and_types_virtual_setup_descs() {
        let layer = ext_layer();
        let d = distill(&layer, BwdRegime::R0, &HashMap::new(), None);

        for (eid, kind) in distilled_leaves_of(&d) {
            match kind {
                SourceKind::Read { .. } => {
                    assert!(!d.leaf_descs.contains_key(&eid), "R0 Read leaves are ordinary");
                    assert!(!d.field_overrides.contains_key(&eid));
                }
                SourceKind::VirtualSetup { kind } => {
                    let desc = *d.leaf_descs.get(&eid).expect("R0 VS leaf must carry a desc");
                    assert_eq!(
                        d.specials.get(desc),
                        Some(&BwdSpecial::VirtualSetup { kind }),
                        "R0 VirtualSetup desc is the typed kind, not a FoldSource"
                    );
                    assert!(
                        !d.field_overrides.contains_key(&eid),
                        "R0 forces no field (rule 4: inference is not forced)"
                    );
                }
                _ => {}
            }
        }
        assert_eq!(d.specials.len(), 1, "only the VirtualSetup desc in R0");
    }

    // (d) ── Canonical layer never mutated ─────────────────────────────────────
    #[test]
    fn canonical_layer_is_unmutated() {
        let layer = three_root_layer();
        let before = layer.clone();
        let _ = distill(&layer, BwdRegime::R0, &HashMap::new(), None);
        let _ = distill(&layer, BwdRegime::Ext, &HashMap::new(), Some(&[1, 2, 0]));
        assert_eq!(layer, before, "distill must never mutate the canonical layer");
    }

    // ── bind() ────────────────────────────────────────────────────────────────
    #[test]
    fn bind_maps_policy_and_round_per_desc() {
        let layer = ext_layer();
        let d = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
        assert_eq!(d.specials.len(), 3);

        // Round 0: no previous-round buffer exists — always lazy depth 0.
        let b0 = bind(&d, MaterializationPolicy::AlwaysMaterialize, 0);
        assert!(b0.states.iter().all(|s| *s == FoldState::LazyFromOriginals { depth: 0 }));

        // Round >= 1, AlwaysMaterialize: every FoldSource reads the buffer.
        let b1 = bind(&d, MaterializationPolicy::AlwaysMaterialize, 3);
        assert!(b1.states.iter().all(|s| *s == FoldState::Materialized));

        // LazyUpTo(2): round 2 recomputes at depth 2, round 3 is materialized.
        let b2 = bind(&d, MaterializationPolicy::LazyUpTo(2), 2);
        assert!(b2.states.iter().all(|s| *s == FoldState::LazyFromOriginals { depth: 2 }));
        let b3 = bind(&d, MaterializationPolicy::LazyUpTo(2), 3);
        assert!(b3.states.iter().all(|s| *s == FoldState::Materialized));

        // R0: a VirtualSetup desc is never a materialized fold buffer.
        let dr0 = distill(&layer, BwdRegime::R0, &HashMap::new(), None);
        let br0 = bind(&dr0, MaterializationPolicy::AlwaysMaterialize, 3);
        assert_eq!(br0.states, vec![FoldState::LazyFromOriginals { depth: 3 }]);
    }

    // ── distilled_site_domain ─────────────────────────────────────────────────
    #[test]
    fn distilled_site_domain_walks_the_rebuilt_layer() {
        // In three_root_layer each Read leaf is shared by two roots, so the
        // rebuilt cones keep fanout >= 2 Read leaves: sites in both regimes.
        let layer = three_root_layer();
        let d = distill(&layer, BwdRegime::R0, &HashMap::new(), None);
        let sites = distilled_site_domain(&d);
        assert!(!sites.is_empty(), "rebuilt layer must expose Read-leaf sites");
        // Every site is keyed on the SINGLE distilled root.
        assert!(sites.iter().all(|k| k.root == d.root));
    }
}
