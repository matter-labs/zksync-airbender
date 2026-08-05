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
//! the future `compile_layer`'s `decisions: Some(&SiteDecisions)` lowering, or (b) replicate the
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
//! Mirrored spans (branch `rr/gkr_dag_ir-blue`, `gpu_gkr_compiler/src/fwd/compile/lower.rs`):
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
use super::arith::{
    AdditiveChild, classify_additive_child, is_constant_one, is_neg_one_factor, is_zero_expr,
};
use crate::schedule::enumerate_site_domain;
use gkr_eval_ir::{DagLayer, Expr, ExprId, RootId, SourceKind};
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

// ── SiteKey / SiteConsumer ───────────────────────────────────────────────────
//
// Task 6 unification: these used to be a byte-for-byte mirror copy of cs's
// schema-v2 types (`gkr_eval_ir::{SiteKey, SiteConsumer}`,
// `cs/src/gkr_compiler/dag_ir/schedule.rs`). cs is now the single source of
// truth (its doc comment on `SiteKey` already said as much); re-exported here
// so every existing `decisions::{SiteKey, SiteConsumer}` call site keeps
// working unchanged.
pub use crate::forward::artifact::{SiteConsumer, SiteKey};

// ── SiteDecisions ────────────────────────────────────────────────────────────

/// Per-layer decisions handed to the emitter: a site's scorer-assigned
/// priority gene. Absent entries read as `None` (caller — normally the
/// genome/scorer — is expected to cover every site in cs's `enumerate_site_domain`).
/// `OccurrenceStreams::build` streams only site-domain values and defaults a missing
/// gene on a surviving (domain) occurrence to `0.0` rather than panicking (the
/// documented per-occurrence site↔gene looseness); a non-domain value is dropped
/// entirely and never admitted (see `build`'s doc + `is_admittable`).
#[derive(Clone, Debug)]
pub struct SiteDecisions {
    map: BTreeMap<SiteKey, f64>,
}

impl SiteDecisions {
    pub fn new(sites: impl IntoIterator<Item = (SiteKey, f64)>) -> Self {
        Self {
            map: sites.into_iter().collect(),
        }
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
    /// The genome-scored site domain (cs's `enumerate_site_domain`: cacheable ∧
    /// fan-out ≥ 2), by value. `try_admit` refuses any value NOT in this set, so a
    /// challenge / constant / virtual-setup / lookup leaf, or any fan-out-1 value, is
    /// never admitted into residency (the `streams` themselves stay unfiltered — see
    /// `build`). This is the enforcement point for RR's "any evictable value has a
    /// genome backing" invariant; read via `is_admittable`.
    admittable: BTreeSet<ExprId>,
    /// Values whose recompute cone actually READS DRAM (a `SourceKind::Read` leaf reachable
    /// through `Add`/`Mul` edges, stopping at resolution fences). Caching only pays off by
    /// avoiding a DRAM re-read; a value whose recompute is DRAM-free — a peek / special /
    /// constant / challenge cone (`RangeCheck`, `PeekSingleColumn`, `PeekSetup`, …) — saves
    /// zero traffic if cached and only squats a cell, so it must never be admitted regardless
    /// of fan-out. Read via `reaches_dram`; consulted by `try_admit` to keep free-to-recompute
    /// values out of cache (RR: "single use values should never make it into cache").
    reaches_dram: BTreeSet<ExprId>,
    /// Per-value count of OPERAND (`SiteConsumer::Expr`) demand occurrences — genuine
    /// re-reads as a fold input, EXCLUDING `RootOutput` materializes (which serve straight
    /// from the accumulator). Combined with `reaches_dram`: a value that saves no traffic
    /// (`!reaches_dram`) AND is used as an operand fewer than twice is pure waste to cache —
    /// its lone free recompute is cheaper than a spill + reload. A multi-use free value (a
    /// peek folded into several terms) still caches, so its gather runs once, not N times.
    operand_reads: BTreeMap<ExprId, usize>,
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
    ///
    /// STATE-DEPENDENT SERVE/BUILD DIVERGENCE: this `order`-classification
    /// replay (above) covers which roots serve at all; it does NOT capture
    /// two further ways the ACTUAL lowering's demand walk can diverge from
    /// `build`'s per-root site count once residency is active — both only
    /// possible when `compile_layer` is given `decisions: Some(&SiteDecisions)`, never under
    /// `decisions: None`:
    ///
    /// (a) Residency HIT short-circuit — when `lower_operand_virtual` finds a
    /// value already resident, it returns the cell immediately without
    /// recursing into that value's operand cone (lower.rs:477), so none of
    /// the interior sites `build` pushed for that cone's sub-expressions get
    /// consumed by this occurrence. The queues for those sub-values shift
    /// anyway (this occurrence's front entry is simply skipped over by the
    /// NEXT genuinely-served occurrence), so `effective_priority` reads a gene
    /// one occurrence earlier than the demand walk that produced it, and
    /// remaining-occurrence-count-driven dead-detection lags by however many
    /// hits happened.
    ///
    /// (b) Compound-miss sibling exposure — `materialize_if_root` (lower.rs
    /// ~:314) exposes every sibling `Compute`-action root sharing a
    /// just-materialized expr, not only the root being lowered. A sibling
    /// root's own later `RootOutput` serve is then skipped by the `exposed`
    /// check `build` also replicates in its top-level loop, but if that
    /// sibling's compound expression contains reads `build` still walked
    /// on the ASSUMPTION it would be independently served, the site
    /// bookkeeping for that interior read is similarly one occurrence ahead
    /// of what the lowering actually demands.
    ///
    /// This is ACCEPTABLE: the divergence is deterministic (same for `build`
    /// and the lowering on every run), it never changes emitted VALUES (the
    /// lowering's own residency/exposed state, not `build`'s streams, decides
    /// what gets materialized — `build` only estimates priorities), and the
    /// compile-in-loop scorer's fitness is the real compile's actual traffic,
    /// so GATE-D (value-exact, schedule-driven) is unaffected regardless of
    /// how stale a priority read is. The real cost is that stored
    /// `cache_priority` genes stop mapping 1:1 to the `SiteKey`s that name
    /// them once caching is active for that circuit: a gene "named" for one
    /// occurrence can end up scored against a different, nearby occurrence's
    /// admission decision. Search still converges because this is a bounded,
    /// deterministic perturbation, not noise — but any future warm-start or
    /// gene-transfer work (reusing a `SiteDecisions` across schedules/runs)
    /// MUST NOT assume site-to-gene alignment is exact once residency is on;
    /// it is only exact under `decisions: None` (no residency, no hits, no
    /// compound-miss exposure).
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

        // The `streams` (demand-order occurrences per value) are built UNFILTERED — the
        // walk order and its phantom/fence/query-edge semantics are locked by this
        // module's unit tests and consumed by `serve`. The RR-invariant (admit into
        // residency ONLY genome-scored values) is enforced at the single admission choke
        // (`try_admit`) via `admittable`, not by pruning the walk: gating admission (not
        // the walk) keeps `serve`/occurrence-counting consistent with the emitter's real
        // traversal while still refusing every non-domain value.
        //
        // `admittable` = cs's `enumerate_site_domain` (cacheable ∧ fan-out ≥ 2), by
        // VALUE. cs is the single source of truth (the same set the producer/genome
        // build from and the schedule validator checks). Keyed by value — not full
        // `SiteKey` — deliberately, so the emitter-vs-cs consumer-field divergence (FMA
        // re-parenting, elision reindex, neg-one fold) is irrelevant: `is_site` depends
        // only on the value, so every genuinely cacheable∧fan-out≥2 value stays
        // admissible with its existing per-occurrence priorities and no legitimate
        // caching is lost; only derived_e4 / constants / virtual-setup / lookup / and
        // fan-out-1 values are refused.
        let admittable: BTreeSet<ExprId> = enumerate_site_domain(layer)
            .into_iter()
            .map(|k| k.value)
            .collect();
        Self::from_flat(layer, flat, d, admittable)
    }

    /// Task 5 bwd twin of [`build`]: the occurrence replay for the ONE-ROOT bwd
    /// driver (`lower_bwd_root_virtual`). Mirrors its exact demand order — one
    /// `RootOutput` site for the distilled root's own serve, then `demand_expand`
    /// over each spine TERM in the driver's decomposition order (`terms` MUST be
    /// the same slice handed to the driver; the spine `Add` itself is decomposed
    /// by the driver, so — unlike a fwd root — its top-level children get NO
    /// per-child operand site of their own). `domain` is the DISTILLED backward
    /// site domain (`bwd::distill::distilled_site_domain`) — it, not the fwd
    /// `enumerate_site_domain`, gates admissibility (`is_admittable`), so Read
    /// fold leaves (Ext) / VirtualSetup leaves (Ext) with fan-out >= 2 admit per
    /// the REV2 backward-cacheable rule. `SiteDecisions` genes are keyed to
    /// DISTILLED `ExprId`s; the fwd consumer-field looseness (FMA re-parenting
    /// vs cs raw child indexing) applies unchanged — a missing gene reads 0.0.
    pub fn build_bwd_root(
        layer: &DagLayer,
        root_id: RootId,
        root_expr: ExprId,
        terms: &[ExprId],
        d: &SiteDecisions,
        domain: &BTreeSet<SiteKey>,
    ) -> Self {
        let mut flat: Vec<SiteKey> = vec![SiteKey {
            root: root_id,
            consumer: SiteConsumer::RootOutput,
            value: root_expr,
        }];
        for &t in terms {
            demand_expand(layer, root_id, t, &mut flat);
        }
        let admittable: BTreeSet<ExprId> = domain.iter().map(|k| k.value).collect();
        Self::from_flat(layer, flat, d, admittable)
    }

    /// Shared tail of [`build`]/[`build_bwd_root`]: fold the flat demand-order site
    /// list into per-value queues + the admission-side sets (pure code motion from
    /// `build` — byte-identical fwd behavior).
    fn from_flat(
        layer: &DagLayer,
        flat: Vec<SiteKey>,
        d: &SiteDecisions,
        admittable: BTreeSet<ExprId>,
    ) -> Self {
        let mut streams: BTreeMap<ExprId, VecDeque<(SiteKey, f64)>> = BTreeMap::new();
        let mut operand_reads: BTreeMap<ExprId, usize> = BTreeMap::new();
        for key in flat {
            if matches!(key.consumer, SiteConsumer::Expr { .. }) {
                *operand_reads.entry(key.value).or_default() += 1;
            }
            let priority = d.get(&key).unwrap_or(0.0);
            streams
                .entry(key.value)
                .or_default()
                .push_back((key, priority));
        }
        let reaches_dram = compute_reaches_dram(layer);
        Self {
            streams,
            admittable,
            reaches_dram,
            operand_reads,
        }
    }

    /// Whether `v`'s recompute cone reads DRAM (see the field doc). `false` for a peek /
    /// special / const / challenge cone whose recompute is free — caching it saves no traffic.
    pub fn reaches_dram(&self, v: ExprId) -> bool {
        self.reaches_dram.contains(&v)
    }

    /// Operand (`SiteConsumer::Expr`) demand count of `v` — fold-input re-reads, excluding
    /// `RootOutput` materializes (see the field doc).
    pub fn operand_read_count(&self, v: ExprId) -> usize {
        self.operand_reads.get(&v).copied().unwrap_or(0)
    }

    /// Effective priority of `v` = priority of its FRONT unserved occurrence;
    /// `None` if no remaining occurrences (== evict-when-dead, -inf semantics).
    pub fn effective_priority(&self, v: ExprId) -> Option<f64> {
        self.streams
            .get(&v)
            .and_then(|q| q.front())
            .map(|(_, p)| *p)
    }

    /// Advance past one served occurrence of `v` (called by the emitter at
    /// each site it serves).
    pub fn serve(&mut self, v: ExprId) {
        if let Some(q) = self.streams.get_mut(&v) {
            q.pop_front();
        }
    }

    /// RR-invariant: whether `v` is in the genome-scored site domain (cs's
    /// `enumerate_site_domain`: cacheable ∧ fan-out ≥ 2). Values outside it have no
    /// occurrence stream and must never be admitted into residency. Consulted by
    /// `try_admit`'s debug_assert to make that guarantee loud.
    pub fn is_admittable(&self, v: ExprId) -> bool {
        self.admittable.contains(&v)
    }
}

/// Per-expr set of values whose recompute cone reads DRAM: a `SourceKind::Read` leaf
/// reachable through `Add`/`Mul` operand edges, stopping at resolution fences (a fenced
/// leaf is a peek — resolved to a free special gather, no DRAM read below it). Mirrors
/// `floor.rs`'s cone walk (same `SourceKind::Read` DRAM predicate + resolution fence).
/// Memoized single pass; the DAG is acyclic so the in-progress `false` seed never masks a
/// real edge.
fn compute_reaches_dram(layer: &DagLayer) -> BTreeSet<ExprId> {
    fn visit(layer: &DagLayer, e: u32, memo: &mut [Option<bool>]) -> bool {
        if let Some(v) = memo[e as usize] {
            return v;
        }
        memo[e as usize] = Some(false); // acyclic-DAG seed (never revisited via a cycle)
        // A resolution-pruned leaf is a peek: the emitter fences it as a terminal special
        // and never walks the cone underneath, so its recompute reads no DRAM.
        let r = if layer.resolutions.contains_key(&ExprId(e)) {
            false
        } else {
            match &layer.exprs[e as usize] {
                Expr::Source(sid) => {
                    matches!(layer.sources[sid.0 as usize].kind, SourceKind::Read { .. })
                }
                Expr::Add(children) | Expr::Mul(children) => children
                    .iter()
                    .fold(false, |acc, c| visit(layer, c.0, memo) || acc),
            }
        };
        memo[e as usize] = Some(r);
        r
    }
    let mut memo: Vec<Option<bool>> = vec![None; layer.exprs.len()];
    let mut out = BTreeSet::new();
    for e in 0..layer.exprs.len() as u32 {
        if visit(layer, e, &mut memo) {
            out.insert(ExprId(e));
        }
    }
    out
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
                    SiteConsumer::Expr {
                        expr: value,
                        input_index: 0,
                    },
                    q,
                    out,
                );
            }
        }
        Expr::Add(children) => {
            // Mirrors compile_add_virtual's zero-addend filter (lower.rs:~415-421).
            let filtered: Vec<ExprId> = children
                .iter()
                .copied()
                .filter(|&c| !is_zero_expr(layer, c))
                .collect();
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
                        SiteConsumer::Expr {
                            expr: value,
                            input_index: idx,
                        },
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
                        SiteConsumer::Expr {
                            expr: value,
                            input_index: idx,
                        },
                        id,
                        out,
                    );
                    idx += 1;
                }
                for (lhs, rhs) in products {
                    push_and_expand(
                        layer,
                        root_id,
                        SiteConsumer::Expr {
                            expr: value,
                            input_index: idx,
                        },
                        lhs,
                        out,
                    );
                    idx += 1;
                    push_and_expand(
                        layer,
                        root_id,
                        SiteConsumer::Expr {
                            expr: value,
                            input_index: idx,
                        },
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
            let factors: Vec<ExprId> = children
                .iter()
                .copied()
                .filter(|&c| !is_constant_one(layer, c))
                .collect();
            if factors.is_empty() {
                return;
            }
            let surviving: Vec<ExprId> = factors
                .into_iter()
                .filter(|&f| !is_neg_one_factor(layer, f))
                .collect();
            for (idx, f) in surviving.into_iter().enumerate() {
                push_and_expand(
                    layer,
                    root_id,
                    SiteConsumer::Expr {
                        expr: value,
                        input_index: idx as u32,
                    },
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
    out.push(SiteKey {
        root: root_id,
        consumer,
        value,
    });
    demand_expand(layer, root_id, value, out);
}

// ── Tests ────────────────────────────────────────────────────────────────────
