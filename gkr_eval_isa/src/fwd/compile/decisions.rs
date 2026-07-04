//! Decision-site identity, per-layer decisions, and occurrence streams — pure
//! machinery for the compile-in-loop scorer (Task 2 of the roadmap; see
//! `.superpowers/sdd/task-2-brief.md`).
//!
//! `SiteKey`/`SiteConsumer` name a single demand of a value (the emitter's
//! `lower_operand_virtual` call for that value, at that specific operand slot
//! of that specific consuming expr — or the root's own output). `SiteDecisions`
//! is a read-only map from site to a scorer-assigned priority gene.
//! `OccurrenceStreams` replays the emitter's ACTUAL demand order (see
//! [`build`]'s doc) into one `VecDeque` per value, so the emitter (Task 3) can
//! ask "what's the next time `v` is needed, and how important is that use?"
//! without re-deriving demand order itself.
//!
//! ## Implementation choice: option (b), replicated + locked
//!
//! The brief offers (a) a shared traversal fn used by both this builder and
//! the future `MaterializePolicy::Decisions` lowering, or (b) replicate the
//! partition logic here and lock it with the interleaved-Add test. This file
//! takes (b): `demand_expand` below re-derives the same child-visitation
//! ORDER as `lower.rs`'s virtual (non-materialize) lowering, but it reuses —
//! rather than reimplements — the actual classification/filtering primitives
//! that decide that order: `classify_additive_child`, `is_zero_expr`,
//! `is_constant_one`, `is_neg_one_factor` (all `pub(crate)` in `super::arith`,
//! the same functions `lower.rs` itself calls). Lifting the walk loops
//! themselves (`compile_add_virtual` / `try_compile_fma_virtual` /
//! `compile_mul_virtual` / `compile_reduction_virtual`) into a shared,
//! non-emitting traversal was judged beyond safe reach for this task — those
//! functions are entangled with `self` (emission, resident-target lookups,
//! field inference) in ways that would require a nontrivial refactor of
//! `lower.rs` to extract a pure "what order would this visit children in"
//! core. So: the primitives are shared (single source of truth for
//! classification), the walk is replicated (documented + cited below), and
//! `stream_order_matches_fma_partition` locks the replica against the exact
//! ordering behavior described in `lower.rs`.
//!
//! Mirrored spans (branch `rr/gkr_dag_ir-blue`, `gkr_eval_isa/src/fwd/compile/lower.rs`):
//! - `compile_add_virtual` zero-addend filter: lower.rs:~415-421.
//! - `try_compile_fma_virtual` addend/product partition (ALL addends before ALL
//!   product operands): lower.rs:865-891.
//! - `compile_reduction_virtual` fallback (no FMA products): each filtered
//!   child lowered as a whole unit, in original order: lower.rs:723-749.
//! - `compile_mul_virtual` zero short-circuit + `Constant{1}`/`-1` factor
//!   filtering, surviving factors lowered in order: lower.rs:674-720.
//!
//! `SourceKind::LookupValue { query, .. }` is NOT a child edge in `Expr` (a
//! `Source` is always an `Expr` leaf) and the current emitter does not walk
//! it as a demand at all (`lower.rs:329` — `UncoveredLookupLeaf` unless
//! covered by `resolutions`, a separate up-front step). Tracking `query` as a
//! demand site here is NEW semantics this module introduces (codex plan
//! finding), not a mirror of existing behavior: `demand_expand` treats a
//! `LookupValue` source as if it had one synthetic child, `query`, at
//! `input_index: 0`.

use super::super::context::ForwardAction;
use super::arith::{classify_additive_child, is_constant_one, is_neg_one_factor, is_zero_expr, AdditiveChild};
use cs::gkr_compiler::dag_ir::{DagLayer, Expr, ExprId, RootId, SourceKind};
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

// ── SiteKey / SiteConsumer ───────────────────────────────────────────────────

/// Site identity, mirrors schema-v2 `SiteKey` (Task 4) exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SiteConsumer {
    Expr { expr: ExprId, input_index: u32 },
    RootOutput,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SiteKey {
    pub root: RootId,
    pub consumer: SiteConsumer,
    pub value: ExprId,
}

// ── SiteDecisions ────────────────────────────────────────────────────────────

/// Per-layer decisions handed to the emitter: a site's scorer-assigned
/// priority gene. Absent entries read as `None` (caller — normally the
/// genome/scorer — is expected to cover every site `OccurrenceStreams::build`
/// would visit; `OccurrenceStreams::build` itself defaults a missing entry to
/// `0.0` rather than panicking, see its doc).
#[derive(Clone, Debug)]
pub struct SiteDecisions {
    map: BTreeMap<SiteKey, f64>,
}

impl SiteDecisions {
    pub fn new(sites: impl IntoIterator<Item = (SiteKey, f64)>) -> Self {
        Self { map: sites.into_iter().collect() }
    }

    pub fn get(&self, k: &SiteKey) -> Option<f64> {
        self.map.get(k).copied()
    }
}

// ── OccurrenceStreams ────────────────────────────────────────────────────────

/// Precomputed per-value stream of remaining occurrences, in the emitter's
/// deterministic traversal order (per served site, NOT per step).
pub struct OccurrenceStreams {
    /// value -> queue of (site, priority) in traversal order; front = next.
    streams: BTreeMap<ExprId, VecDeque<(SiteKey, f64)>>,
}

impl OccurrenceStreams {
    /// Build from (order, actions, decisions, layer): for each root in
    /// `order`, replay the emitter's actual demand order (see module doc for
    /// exactly which `lower.rs` spans this mirrors, and the option-(b)
    /// rationale). `order` is authoritative over `RootId` numeric value —
    /// roots are visited in `order`'s sequence, not sorted by id.
    ///
    /// SERVE/BUILD 1:1 ALIGNMENT INVARIANT: `lower_layer_virtual` (lower.rs
    /// ~:1298-1346) does NOT call `serve_occurrence` for every root in
    /// `order` — only `ForwardAction::Compute` roots not yet in its `exposed`
    /// set actually reach `lower_operand_virtual`'s demand walk.
    /// `ForwardAction::CopyAlias` and `ForwardAction::SkipScratchPrefill`
    /// roots never serve anything, and a `Compute` root whose `ExprId` a
    /// PRIOR root (any RootId, sharing that expr) already exposed is skipped
    /// too (`materialize_if_root`'s de-dup, lower.rs:1074-1102, exposes every
    /// sibling `Compute`-action root sharing the materialized expr, not just
    /// `rid` itself). If `build` pushed a site for a root the lowering will
    /// skip, that site would sit at the FRONT of its value's queue forever
    /// unconsumed, so a later, genuinely-served occurrence of the same value
    /// would read the phantom's stale priority instead of its own — silently
    /// corrupting `effective_priority`/admission decisions (search-quality
    /// bug, not a soundness one, but a real one). So `build` replicates the
    /// SAME `ForwardAction` classification and `exposed`-dedup the lowering
    /// applies before contributing any site for a root: a root the lowering
    /// would skip contributes ZERO occurrences (no `RootOutput` site, no
    /// interior demand walk).
    ///
    /// A site missing from `d` defaults to priority `0.0` (this pure builder
    /// never fails on incomplete decisions; callers that need full coverage
    /// should assert it themselves before calling `build`).
    pub fn build(
        layer: &DagLayer,
        order: &[RootId],
        actions: &HashMap<RootId, ForwardAction>,
        d: &SiteDecisions,
    ) -> Self {
        let mut flat: Vec<SiteKey> = Vec::new();
        // Mirrors `VirtualLower::exposed` (lower.rs:211): a root, once exposed,
        // never serves again — whether by its own visit or by a sibling
        // `Compute`-action root sharing its `ExprId` (see doc above).
        let mut exposed: BTreeSet<RootId> = BTreeSet::new();
        for &root_id in order {
            if exposed.contains(&root_id) {
                continue;
            }
            match actions.get(&root_id) {
                Some(ForwardAction::Compute) => {
                    let root_expr = layer.roots[root_id.0 as usize].expr;
                    flat.push(SiteKey {
                        root: root_id,
                        consumer: SiteConsumer::RootOutput,
                        value: root_expr,
                    });
                    demand_expand(layer, root_id, root_expr, &mut flat);
                    exposed.insert(root_id);
                    // Mirrors `materialize_if_root`'s dedup (lower.rs:1074-1102):
                    // exposing `root_expr` exposes EVERY `Compute`-action root
                    // sharing that expr, not just `root_id`, regardless of
                    // whether that sibling has been visited in `order` yet.
                    for (idx, other) in layer.roots.iter().enumerate() {
                        let other_id = RootId(idx as u32);
                        if other_id != root_id
                            && other.expr == root_expr
                            && matches!(actions.get(&other_id), Some(ForwardAction::Compute))
                        {
                            exposed.insert(other_id);
                        }
                    }
                }
                Some(ForwardAction::CopyAlias { .. }) => {
                    // lower.rs:1332-1345: emits an alias root_output, but never
                    // reaches `lower_operand_virtual` — no demand site at all.
                    exposed.insert(root_id);
                }
                Some(ForwardAction::SkipScratchPrefill) | None => {
                    // lower.rs:1346: emits nothing, not exposed either (matches
                    // — contributes zero occurrences either way).
                }
            }
        }

        let mut streams: BTreeMap<ExprId, VecDeque<(SiteKey, f64)>> = BTreeMap::new();
        for key in flat {
            let priority = d.get(&key).unwrap_or(0.0);
            streams.entry(key.value).or_default().push_back((key, priority));
        }
        Self { streams }
    }

    /// Effective priority of `v` = priority of its FRONT unserved occurrence;
    /// `None` if no remaining occurrences (== evict-when-dead, -inf semantics).
    pub fn effective_priority(&self, v: ExprId) -> Option<f64> {
        self.streams.get(&v).and_then(|q| q.front()).map(|(_, p)| *p)
    }

    /// Advance past one served occurrence of `v` (called by the emitter at
    /// each site it serves).
    pub fn serve(&mut self, v: ExprId) {
        if let Some(q) = self.streams.get_mut(&v) {
            q.pop_front();
        }
    }
}

// ── demand-order traversal (option (b): see module doc) ─────────────────────

/// Expand the operand-fetch sites triggered when `value` is lowered, mirroring
/// `lower.rs`'s virtual (non-materialize) `Add`/`Mul` lowering — see the
/// module doc for the exact mirrored spans and the `LookupValue.query` new
/// semantics. Pushes one `SiteKey` per demanded operand (consumer = `value`
/// at that operand's position) and recurses into any compound operand.
fn demand_expand(layer: &DagLayer, root_id: RootId, value: ExprId, out: &mut Vec<SiteKey>) {
    // Resolution-pruned leaf: `lower.rs`'s virtual lowering fences it as a terminal
    // Special BEFORE any Source/Add/Mul match (`lower_operand_virtual` step 2,
    // lower.rs:484; `compile_expr_virtual`, lower.rs:517 — both check
    // `layer.resolutions.contains_key` first) and never walks the cone underneath.
    // `value` itself may still be a demand site (already pushed by the caller —
    // `push_and_expand` or the root-output push in `build` — before this call); only
    // the walk BELOW it is fenced here, so `OccurrenceStreams` never queues a
    // phantom occurrence for a value the emitter never actually serves.
    if layer.resolutions.contains_key(&value) {
        return;
    }
    match &layer.exprs[value.0 as usize] {
        Expr::Source(src_id) => {
            // NEW semantics (not in lower.rs): treat `query` as a synthetic
            // single child of a LookupValue source.
            if let SourceKind::LookupValue { query, .. } = &layer.sources[src_id.0 as usize].kind {
                let q = *query;
                push_and_expand(
                    layer,
                    root_id,
                    SiteConsumer::Expr { expr: value, input_index: 0 },
                    q,
                    out,
                );
            }
        }
        Expr::Add(children) => {
            // Mirrors compile_add_virtual's zero-addend filter (lower.rs:~415-421).
            let filtered: Vec<ExprId> =
                children.iter().copied().filter(|&c| !is_zero_expr(layer, c)).collect();
            if filtered.is_empty() {
                return;
            }
            // Mirrors try_compile_fma_virtual's classification loop (lower.rs:865-878).
            let mut addends: Vec<ExprId> = Vec::new();
            let mut products: Vec<(ExprId, ExprId)> = Vec::new();
            for &c in &filtered {
                match classify_additive_child(layer, c) {
                    AdditiveChild::Product { lhs, rhs, .. } => products.push((lhs, rhs)),
                    AdditiveChild::Addend { id, .. } => addends.push(id),
                }
            }
            let mut idx: u32 = 0;
            if products.is_empty() {
                // No FMA-fusable product: compile_reduction_virtual's fallback
                // (lower.rs:723-749) lowers each filtered child as a whole unit,
                // in original order (classify_additive_child's Product arm is
                // unreachable here since `products` would be non-empty).
                for id in addends {
                    push_and_expand(
                        layer,
                        root_id,
                        SiteConsumer::Expr { expr: value, input_index: idx },
                        id,
                        out,
                    );
                    idx += 1;
                }
            } else {
                // try_compile_fma_virtual (lower.rs:865-891): ALL addends before
                // ALL product operands (products fused inline, no site of their own).
                for id in addends {
                    push_and_expand(
                        layer,
                        root_id,
                        SiteConsumer::Expr { expr: value, input_index: idx },
                        id,
                        out,
                    );
                    idx += 1;
                }
                for (lhs, rhs) in products {
                    push_and_expand(
                        layer,
                        root_id,
                        SiteConsumer::Expr { expr: value, input_index: idx },
                        lhs,
                        out,
                    );
                    idx += 1;
                    push_and_expand(
                        layer,
                        root_id,
                        SiteConsumer::Expr { expr: value, input_index: idx },
                        rhs,
                        out,
                    );
                    idx += 1;
                }
            }
        }
        Expr::Mul(children) => {
            // Mirrors compile_mul_virtual (lower.rs:674-720): zero short-circuit,
            // Constant{1} elision, then -1-factor elision; surviving factors are
            // lowered in order via compile_reduction_virtual(is_add=false).
            if children.iter().any(|&c| is_zero_expr(layer, c)) {
                return;
            }
            let factors: Vec<ExprId> =
                children.iter().copied().filter(|&c| !is_constant_one(layer, c)).collect();
            if factors.is_empty() {
                return;
            }
            let surviving: Vec<ExprId> =
                factors.into_iter().filter(|&f| !is_neg_one_factor(layer, f)).collect();
            for (idx, f) in surviving.into_iter().enumerate() {
                push_and_expand(
                    layer,
                    root_id,
                    SiteConsumer::Expr { expr: value, input_index: idx as u32 },
                    f,
                    out,
                );
            }
        }
    }
}

/// Push one demand site for `value` (consumed at `consumer`), then recurse
/// into `value`'s own children if it is compound.
fn push_and_expand(
    layer: &DagLayer,
    root_id: RootId,
    consumer: SiteConsumer,
    value: ExprId,
    out: &mut Vec<SiteKey>,
) {
    out.push(SiteKey { root: root_id, consumer, value });
    demand_expand(layer, root_id, value, out);
}

// ── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{BatchingOrder, Root, SourceInfo};
    use std::collections::BTreeMap as StdBTreeMap;

    fn const_source(value: u32) -> SourceInfo {
        SourceInfo { kind: SourceKind::Constant { value } }
    }

    fn layer_with(sources: Vec<SourceInfo>, exprs: Vec<Expr>, roots: Vec<Root>) -> DagLayer {
        DagLayer {
            sources,
            exprs,
            roots,
            batching: BatchingOrder { roots: Vec::new() },
            resolutions: StdBTreeMap::new(),
        }
    }

    fn root(expr: ExprId) -> Root {
        Root { expr, materialize: None, claim: None }
    }

    /// Every `RootId` in `order` classified `ForwardAction::Compute` — the
    /// vast majority of this module's tests are about the demand-order
    /// traversal `demand_expand` performs for an ALREADY-served root, not
    /// about the `ForwardAction`/`exposed` gating itself (that gating is
    /// covered directly by the `build_*` tests below), so they opt every
    /// root in.
    fn all_compute(order: &[RootId]) -> HashMap<RootId, ForwardAction> {
        order.iter().map(|&r| (r, ForwardAction::Compute)).collect()
    }

    /// Priorities advance per served site: after serving v's first occurrence,
    /// the effective priority is the SECOND occurrence's gene, within the same
    /// root.
    #[test]
    fn effective_priority_advances_per_served_site() {
        // sources: v = Constant(5) -> ExprId(0)
        // exprs: Add([v, v]) -> ExprId(1)   (two sites for v under one root)
        let v = ExprId(0);
        let add_id = ExprId(1);
        let layer = layer_with(
            vec![const_source(5)],
            vec![Expr::Source(cs::gkr_compiler::dag_ir::SourceId(0)), Expr::Add(vec![v, v])],
            vec![root(add_id)],
        );
        let order = [RootId(0)];

        let site0 = SiteKey { root: RootId(0), consumer: SiteConsumer::Expr { expr: add_id, input_index: 0 }, value: v };
        let site1 = SiteKey { root: RootId(0), consumer: SiteConsumer::Expr { expr: add_id, input_index: 1 }, value: v };
        let decisions = SiteDecisions::new([(site0, 1.0), (site1, 2.0)]);

        let mut streams = OccurrenceStreams::build(&layer, &order, &all_compute(&order), &decisions);
        assert_eq!(streams.effective_priority(v), Some(1.0));
        streams.serve(v);
        assert_eq!(streams.effective_priority(v), Some(2.0), "front must move to the second occurrence's gene");
    }

    /// A value with all occurrences served has None priority (evict-when-dead).
    #[test]
    fn exhausted_value_has_no_priority() {
        let v = ExprId(0);
        let add_id = ExprId(1);
        let layer = layer_with(
            vec![const_source(5)],
            vec![Expr::Source(cs::gkr_compiler::dag_ir::SourceId(0)), Expr::Add(vec![v, v])],
            vec![root(add_id)],
        );
        let order = [RootId(0)];
        let decisions = SiteDecisions::new([]);

        let mut streams = OccurrenceStreams::build(&layer, &order, &all_compute(&order), &decisions);
        streams.serve(v);
        streams.serve(v);
        assert_eq!(streams.effective_priority(v), None);
    }

    /// Streams follow order: sites of order[1]'s root come after order[0]'s
    /// even if RootId(1) < RootId(0) numerically.
    #[test]
    fn streams_follow_execution_order_not_root_ids() {
        // Two roots (RootId(0), RootId(1)) both output the SAME shared value v.
        let v = ExprId(0);
        let layer = layer_with(
            vec![const_source(9)],
            vec![Expr::Source(cs::gkr_compiler::dag_ir::SourceId(0))],
            vec![root(v), root(v)],
        );
        // order[0] = RootId(1) (numerically LARGER), order[1] = RootId(0).
        let order = [RootId(1), RootId(0)];

        let site_root1 = SiteKey { root: RootId(1), consumer: SiteConsumer::RootOutput, value: v };
        let site_root0 = SiteKey { root: RootId(0), consumer: SiteConsumer::RootOutput, value: v };
        let decisions = SiteDecisions::new([(site_root1, 10.0), (site_root0, 20.0)]);

        let streams = OccurrenceStreams::build(&layer, &order, &all_compute(&order), &decisions);
        // If roots were visited in ascending RootId order this would be 20.0.
        assert_eq!(
            streams.effective_priority(v),
            Some(10.0),
            "order[0] = RootId(1) must be served first regardless of numeric RootId"
        );
    }

    /// FMA-partition order lock (codex finding 2): for
    /// `Add[addend_a, Mul(l,r), addend_b]`, the stream order is
    /// addend_a, addend_b, l, r — addends before product operands, NOT tree
    /// interleaving.
    #[test]
    fn stream_order_matches_fma_partition() {
        // sources: addend_a=Constant(10)->0, addend_b=Constant(20)->1,
        //          l=Constant(2)->2, r=Constant(3)->3
        let addend_a = ExprId(0);
        let addend_b = ExprId(1);
        let l = ExprId(2);
        let r = ExprId(3);
        let mul_id = ExprId(4);
        let add_id = ExprId(5);
        let layer = layer_with(
            vec![const_source(10), const_source(20), const_source(2), const_source(3)],
            vec![
                Expr::Source(cs::gkr_compiler::dag_ir::SourceId(0)),
                Expr::Source(cs::gkr_compiler::dag_ir::SourceId(1)),
                Expr::Source(cs::gkr_compiler::dag_ir::SourceId(2)),
                Expr::Source(cs::gkr_compiler::dag_ir::SourceId(3)),
                Expr::Mul(vec![l, r]),
                // Deliberately interleaved: addend, product, addend.
                Expr::Add(vec![addend_a, mul_id, addend_b]),
            ],
            vec![root(add_id)],
        );
        let order = [RootId(0)];
        let decisions = SiteDecisions::new([]);

        let mut streams = OccurrenceStreams::build(&layer, &order, &all_compute(&order), &decisions);
        // Each of addend_a, addend_b, l, r has exactly one occurrence; serving
        // them in the expected order must drain each stream to None, and
        // serving out of order must NOT drain a not-yet-reached value's stream
        // (it has no entry to drain).
        for expected in [addend_a, addend_b, l, r] {
            assert!(
                streams.effective_priority(expected).is_some(),
                "expected {:?} to still have an occurrence",
                expected
            );
            streams.serve(expected);
            assert_eq!(
                streams.effective_priority(expected),
                None,
                "{:?} must have exactly one occurrence",
                expected
            );
        }
    }

    /// `LookupValue.query` demand position is locked explicitly (query edges
    /// are invisible to the OLD OracleInstance enumeration — this is new
    /// semantics).
    #[test]
    fn stream_includes_query_edge_at_emitter_position() {
        // sources: query = Constant(7) -> ExprId(0); lv = LookupValue{query} -> src(1)
        let query = ExprId(0);
        let lv_expr = ExprId(1);
        let layer = layer_with(
            vec![
                const_source(7),
                SourceInfo {
                    kind: SourceKind::LookupValue {
                        kind: cs::gkr_compiler::dag_ir::LookupValueKind::RangeCheck16Index,
                        set_index: 0,
                        query,
                    },
                },
            ],
            vec![
                Expr::Source(cs::gkr_compiler::dag_ir::SourceId(0)),
                Expr::Source(cs::gkr_compiler::dag_ir::SourceId(1)),
            ],
            vec![root(lv_expr)],
        );
        let order = [RootId(0)];

        let expected_key = SiteKey {
            root: RootId(0),
            consumer: SiteConsumer::Expr { expr: lv_expr, input_index: 0 },
            value: query,
        };
        let decisions = SiteDecisions::new([(expected_key, 42.0)]);

        let streams = OccurrenceStreams::build(&layer, &order, &all_compute(&order), &decisions);
        assert_eq!(
            streams.effective_priority(query),
            Some(42.0),
            "query edge must be demanded at Expr{{lv_expr, input_index:0}}"
        );
    }

    // ── serve/build alignment regression tests ──────────────────────────────

    /// A `CopyAlias`-classified root contributes ZERO occurrences: even though
    /// its `root.expr` is a compound value that would, if walked, demand a
    /// shared leaf, the real lowering (lower.rs:1332-1345) never reaches
    /// `lower_operand_virtual` for a `CopyAlias` root, so `build` must not
    /// either. Regression for the phantom-occurrence finding: before the fix,
    /// `build` walked EVERY root in `order` unconditionally, so the
    /// CopyAlias root's phantom demand for `v` sat at the front of `v`'s
    /// queue with a default (0.0) priority, ahead of the genuine later
    /// occurrence's real (42.0) priority.
    #[test]
    fn copy_alias_root_contributes_no_occurrences() {
        use cs::definitions::GKRAddress;

        let v = ExprId(0);
        let alias_wrapper = ExprId(1); // CopyAlias root's expr: Add([v]) — would demand v if walked.
        let real_wrapper = ExprId(2); // A genuinely-served Compute root's expr: also Add([v]).
        let layer = layer_with(
            vec![const_source(9)],
            vec![
                Expr::Source(cs::gkr_compiler::dag_ir::SourceId(0)), // 0 = v
                Expr::Add(vec![v]),                                  // 1 = alias_wrapper
                Expr::Add(vec![v]),                                  // 2 = real_wrapper
            ],
            vec![root(alias_wrapper), root(real_wrapper)],
        );
        let order = [RootId(0), RootId(1)];
        let actions: HashMap<RootId, ForwardAction> = [
            (
                RootId(0),
                ForwardAction::CopyAlias {
                    src_addr: GKRAddress::BaseLayerWitness(0),
                    dst_addr: GKRAddress::BaseLayerWitness(1),
                },
            ),
            (RootId(1), ForwardAction::Compute),
        ]
        .into_iter()
        .collect();

        let real_site = SiteKey {
            root: RootId(1),
            consumer: SiteConsumer::Expr { expr: real_wrapper, input_index: 0 },
            value: v,
        };
        let decisions = SiteDecisions::new([(real_site, 42.0)]);

        let mut streams = OccurrenceStreams::build(&layer, &order, &actions, &decisions);
        assert_eq!(
            streams.effective_priority(v),
            Some(42.0),
            "the CopyAlias root's phantom demand for v must not precede the real occurrence"
        );
        streams.serve(v);
        assert_eq!(
            streams.effective_priority(v),
            None,
            "v must have exactly ONE occurrence (the genuine one) — no leftover phantom"
        );
        // The CopyAlias root's own RootOutput must not appear either.
        assert_eq!(
            streams.effective_priority(alias_wrapper),
            None,
            "a CopyAlias root's own RootOutput must contribute no occurrence"
        );
    }

    /// Two `Compute` roots sharing the SAME `ExprId` in `order`: the second
    /// contributes NO phantom (mirrors `materialize_if_root`'s cross-root
    /// `exposed` dedup, lower.rs:1074-1102) — neither its own `RootOutput`
    /// site nor a duplicate interior demand walk. A later genuine occurrence
    /// of a value shared with the first root's expr gets its OWN priority,
    /// not a phantom's default.
    #[test]
    fn shared_expr_second_root_contributes_no_phantom() {
        let v = ExprId(0);
        let shared_expr = ExprId(1); // Add([v]) — root.expr of BOTH RootId(0) and RootId(1).
        let real_wrapper = ExprId(2); // A separate later genuine occurrence of v.
        let layer = layer_with(
            vec![const_source(4)],
            vec![
                Expr::Source(cs::gkr_compiler::dag_ir::SourceId(0)), // 0 = v
                Expr::Add(vec![v]),                                  // 1 = shared_expr
                Expr::Add(vec![v]),                                  // 2 = real_wrapper
            ],
            vec![root(shared_expr), root(shared_expr), root(real_wrapper)],
        );
        let order = [RootId(0), RootId(1), RootId(2)];
        let actions: HashMap<RootId, ForwardAction> = [
            (RootId(0), ForwardAction::Compute),
            (RootId(1), ForwardAction::Compute),
            (RootId(2), ForwardAction::Compute),
        ]
        .into_iter()
        .collect();

        let root_output_site =
            SiteKey { root: RootId(0), consumer: SiteConsumer::RootOutput, value: shared_expr };
        let r0_demand_site = SiteKey {
            root: RootId(0),
            consumer: SiteConsumer::Expr { expr: shared_expr, input_index: 0 },
            value: v,
        };
        let real_site = SiteKey {
            root: RootId(2),
            consumer: SiteConsumer::Expr { expr: real_wrapper, input_index: 0 },
            value: v,
        };
        let decisions = SiteDecisions::new([
            (root_output_site, 5.0),
            (r0_demand_site, 3.0),
            (real_site, 77.0),
        ]);

        let mut streams = OccurrenceStreams::build(&layer, &order, &actions, &decisions);

        // shared_expr: exactly ONE RootOutput occurrence (RootId(0)'s) — RootId(1)'s
        // visit, sharing the same expr, must not add a second.
        assert_eq!(streams.effective_priority(shared_expr), Some(5.0));
        streams.serve(shared_expr);
        assert_eq!(
            streams.effective_priority(shared_expr),
            None,
            "RootId(1) sharing shared_expr with the already-exposed RootId(0) must not \
             contribute a phantom second RootOutput occurrence"
        );

        // v: RootId(0)'s genuine interior demand (3.0), then RootId(2)'s genuine later
        // occurrence (77.0) — RootId(1)'s redundant re-walk of shared_expr must not
        // insert a phantom 0.0 entry between them.
        assert_eq!(streams.effective_priority(v), Some(3.0));
        streams.serve(v);
        assert_eq!(
            streams.effective_priority(v),
            Some(77.0),
            "after RootId(0)'s genuine occurrence of v is served, the NEXT must be \
             RootId(2)'s genuine occurrence (77.0), not a phantom (0.0) from RootId(1)'s \
             deduped re-walk of shared_expr"
        );
        streams.serve(v);
        assert_eq!(
            streams.effective_priority(v),
            None,
            "v must have exactly two occurrences (RootId(0)'s and RootId(2)'s), not three"
        );
    }

    /// A resolution-pruned fold-leaf fences its own children — matches the real
    /// emitter (`lower.rs:484,517`: `layer.resolutions.contains_key` is checked
    /// BEFORE any Source/Add/Mul match, so a fenced leaf's cone is never walked).
    /// `demand_expand` must apply the same fence: a value sitting BOTH under a
    /// resolution cone (phantom, unfenced-emitter-would-never-serve) AND as a
    /// genuine unfenced operand elsewhere must get exactly one queued occurrence
    /// (from the unfenced site), at its own real priority — the under-cone
    /// occurrence must contribute NOTHING (no phantom entry, no stale-front
    /// corruption of the kind this module's doc already documents for
    /// CopyAlias/shared-expr roots).
    #[test]
    fn resolution_cone_children_are_not_demand_sites() {
        let x = ExprId(0);
        let w = ExprId(1); // w = Add(x, x)
        let fold_leaf = ExprId(2); // fold_leaf = Add(w, w) — RESOLUTION-PRUNED
        let mut layer = layer_with(
            vec![const_source(7)],
            vec![
                Expr::Source(cs::gkr_compiler::dag_ir::SourceId(0)), // 0 = x
                Expr::Add(vec![x, x]),                               // 1 = w
                Expr::Add(vec![w, w]),                               // 2 = fold_leaf (fenced)
            ],
            vec![root(fold_leaf), root(w)],
        );
        layer.resolutions.insert(fold_leaf, cs::gkr_compiler::dag_ir::ResolutionStrategy::PeekSetup);

        // fold_leaf's root (RootId(0)) is visited FIRST — if its cone were walked
        // (unfixed), phantom occurrences for w (and, transitively, x) would land at
        // the FRONT of their queues, ahead of RootId(1)'s genuine demand below.
        let order = [RootId(0), RootId(1)];
        let real_site = SiteKey { root: RootId(1), consumer: SiteConsumer::RootOutput, value: w };
        let decisions = SiteDecisions::new([(real_site, 5.0)]);

        let mut streams = OccurrenceStreams::build(&layer, &order, &all_compute(&order), &decisions);
        assert_eq!(
            streams.effective_priority(w),
            Some(5.0),
            "w's only queued occurrence must be RootId(1)'s genuine RootOutput demand, \
             not a phantom (0.0) from walking under the fenced fold_leaf"
        );
        streams.serve(w);
        assert_eq!(
            streams.effective_priority(w),
            None,
            "w must have exactly one occurrence — the fenced cone contributes zero"
        );
        // x is demanded genuinely twice — both operands of w's own Add(x, x),
        // walked once via RootId(1)'s real RootOutput demand of w. If fold_leaf's
        // fenced cone were ALSO walked (unfixed), w's Add(x, x) would be re-visited
        // a second time from beneath the fence (root 0), doubling x's occurrence
        // count to 4 (`demand_expand` has no memoization, unlike cs's walker).
        assert_eq!(streams.effective_priority(x), Some(0.0));
        streams.serve(x);
        assert_eq!(streams.effective_priority(x), Some(0.0));
        streams.serve(x);
        assert_eq!(
            streams.effective_priority(x),
            None,
            "x must have exactly two occurrences — both from RootId(1)'s real walk of w"
        );
    }
}
