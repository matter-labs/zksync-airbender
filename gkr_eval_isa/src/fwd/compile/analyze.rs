//! Stage-1 value graph: refcounts, next-use distances, and candidate eligibility.
//!
//! `analyze_layer` is a PURE analysis pass — it reads `&DagLayer` and
//! `&DagForwardContext` but NEVER mutates the context. It produces a `ValueGraph`
//! consumed by every downstream residency-planner task (S2+).

use super::arith::{child_operand_field, is_zero_expr};
use super::super::context::{DagForwardContext, ForwardAction};
use super::super::isa::OperandField;
use super::super::source::lower_resolution;
use cs::gkr_compiler::dag_ir::{
    DagLayer, Expr, ExprId, RootId, SinkInfo, SinkKind, SourceKind,
};
use std::collections::HashMap;

// ── Public types ─────────────────────────────────────────────────────────────

/// A `ValueId` is simply an `ExprId` — the dag is hash-consed, so an `ExprId`
/// IS a value identity.
pub type ValueId = ExprId;

/// A stable, deduplicated list of resolution-leaf `ExprId`s that were actually
/// **reached** during the Stage-1 DFS walk (i.e. pruning was applied to them).
///
/// Only reached resolutions are planned here. Interning an unreached resolution
/// would create a `ctx.specials` entry with no `OperandLine::Special` reference,
/// which `validate_special_bindings` (the orphan check) rejects.
#[derive(Clone, Debug, Default)]
pub struct DescriptorPlan {
    /// Reached resolution-leaf ExprIds, in stable encounter order, deduplicated.
    pub keys: Vec<ExprId>,
}

/// Lost-future-benefit cost of NOT keeping a value resident (the residency
/// planner's eviction tie-breaker — higher cost = prefer to keep it).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MissPenalty {
    pub dram_reads: u32,
    pub instrs: u32,
    pub cell_ops: u32,
}

/// Per-value facts produced by `analyze_layer`.
#[derive(Clone, Debug)]
pub struct ValueInfo {
    /// Number of uses (references) of this value across the layer's expr trees.
    pub refcount: u32,
    /// The operand field (`Base` or `Ext`) this value lives in.
    pub field: OperandField,
    /// Cell width in field elements: 1 for Base, 4 for Ext.
    pub width: u8,
    /// True if this value has at least one use AFTER the point it first becomes
    /// available — e.g. a cache root's output expr referenced again (as a recomputed
    /// shared `ExprId`) in a later root's tree.
    pub is_candidate: bool,
    /// Estimated cost to re-obtain this value if evicted from residency.
    pub miss: MissPenalty,
    /// True if this value has a real global DRAM backing that can be re-read:
    /// `SourceKind::Read` or `VirtualSetup` (→ `OperandLine::Global`).
    /// False for compound `Add`/`Mul` subexprs, `Constant`/`Challenge` literals,
    /// and resolution-pruned (special-gather) leaves — these must be recomputed
    /// or re-gathered if evicted.
    pub has_backing: bool,
    /// True iff this value is a `SourceKind::Read` source (a real DRAM read — NOT
    /// `VirtualSetup`, which is computed) loaded/borrowed as a fold operand ≥ 2 times
    /// over the layer's materialize-bearing root trees. Drives source residency (load-once +
    /// borrow). EMISSION-EXACT for the three elided categories (zero-annihilated Mul,
    /// CopyAlias-action roots, sole-source passthrough roots) so a flagged read is one
    /// the emitter actually pins — see the candidate post-pass in `analyze_layer`.
    pub is_source_resident: bool,
}

/// The value graph produced by `analyze_layer`.
pub struct ValueGraph {
    /// Per-value facts, keyed by `ExprId`.
    pub info: HashMap<ValueId, ValueInfo>,
    /// Dependency edges: `(use, producer)`. Part B: the `Prior`-source edge is gone
    /// (same-layer cache reuse is now a recomputed shared `ExprId`), so this is
    /// currently always empty — kept for the residency-internal interface.
    pub dep_edges: Vec<(ValueId, ValueId)>,
    /// Resolution descriptors planned during analysis: the distinct leaf ExprIds
    /// that were reached and pruned. Stage 3 calls `materialize_descriptors` to
    /// intern these into `ctx.specials` exactly once.
    pub descriptors: DescriptorPlan,
}

// ── Cost constants ────────────────────────────────────────────────────────────

/// Miss cost for a stored cache root or source-backed read: re-reading from DRAM.
const MISS_BACKED_READ: MissPenalty = MissPenalty { dram_reads: 1, instrs: 1, cell_ops: 0 };

/// Miss cost for a PEEK / special gather (resolution-pruned fold): one instruction,
/// no DRAM (the special source is a precomputed array indexed at runtime).
const MISS_SPECIAL_GATHER: MissPenalty = MissPenalty { dram_reads: 0, instrs: 1, cell_ops: 0 };

/// Miss cost for a near-free literal (`Constant` or `Challenge`): zero.
const MISS_LITERAL: MissPenalty = MissPenalty { dram_reads: 0, instrs: 0, cell_ops: 0 };

// ── Analysis ──────────────────────────────────────────────────────────────────

/// True iff `expr_id` is a `SourceKind::Read` source (a DRAM read). `VirtualSetup` is
/// excluded — it lowers to a `Global` operand but is resolved by computation
/// (interp.rs:148), not `r.read`, so caching it saves no DRAM read.
fn is_read_source(layer: &DagLayer, expr_id: ExprId) -> bool {
    if let Expr::Source(src_id) = &layer.exprs[expr_id.0 as usize] {
        matches!(layer.sources[src_id.0 as usize].kind, SourceKind::Read { .. })
    } else {
        false
    }
}

/// DFS an Output-root expr tree, counting each operand-level use of a `Read` source.
/// Resolution-pruned exprs are terminals (match analyze's pruning), not descended.
/// A zero-annihilated `Mul` subtree is a terminal too: `compile_add` drops it via the
/// shared `is_zero_expr`, so none of its reads are emitted — mirror that elision exactly.
fn count_read_uses(layer: &DagLayer, expr_id: ExprId, counts: &mut HashMap<ExprId, u32>) {
    if layer.resolutions.contains_key(&expr_id) {
        return;
    }
    if is_read_source(layer, expr_id) {
        *counts.entry(expr_id).or_insert(0) += 1;
        return;
    }
    if let Expr::Add(children) | Expr::Mul(children) = &layer.exprs[expr_id.0 as usize] {
        // Category (a) — zero-annihilation: `is_zero_expr` is true for a `Mul` with any
        // zero factor and FALSE for an `Add`, so this prunes only zero Muls; an Add that
        // merely contains a zero-Mul sibling keeps counting its other reads.
        if is_zero_expr(layer, expr_id) {
            return;
        }
        let children = children.clone();
        for c in children {
            count_read_uses(layer, c, counts);
        }
    }
}

/// Pure Stage-1 value graph analysis.
///
/// Walks `layer.roots` and their expr subtrees, computing:
/// - `refcount` — total reference count across all root expr trees
/// - `field` / `width` — via the PURE `child_operand_field` (reads only `layer`
///   + `ctx.cross_layer_fields`, NEVER `ctx.specials` / `ctx.backings`)
/// - `is_candidate` — true when a value has any use AFTER its production point
/// - `miss` — recompute / re-obtain cost for the residency planner
/// - `dep_edges` — `(use_expr_id, producer_expr_id)` pairs
/// - `descriptors` — `DescriptorPlan` listing the distinct resolution leaf ExprIds
///   actually reached by the DFS (in encounter order, deduplicated)
///
/// Resolution pruning: if `layer.resolutions.contains_key(&id)`, the value's
/// `miss` is `MISS_SPECIAL_GATHER` and analysis does NOT descend into children
/// for refcounts or recompute cost.
///
/// PURE: takes `&DagForwardContext` and MUST NOT mutate it.
pub fn analyze_layer(layer: &DagLayer, ctx: &DagForwardContext) -> ValueGraph {
    let mut info: HashMap<ValueId, ValueInfo> = HashMap::new();
    let mut dep_edges: Vec<(ValueId, ValueId)> = Vec::new();
    let mut reached_resolutions: Vec<ExprId> = Vec::new();

    // produced_at[expr_id] = root index that "produces" this value.
    // For a cache root's output expr: the root index that materializes it.
    // All other exprs are produced on demand (no dedicated entry — they are
    // produced at the same root that first references them, so any LATER root
    // referencing them qualifies as a later use).
    //
    // A cache root is a `Cache` materialize with no claim (Part B: same-layer reuse is
    // now a recomputed shared `ExprId`, so a cache root's later use is an ordinary ref
    // in a later root's tree, not a `Prior` source).
    let mut produced_at: HashMap<ExprId, usize> = HashMap::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        let is_cache_root = matches!(
            root.materialize,
            Some(SinkInfo { kind: SinkKind::Cache { .. }, .. })
        ) && root.claim.is_none();
        if is_cache_root {
            // Cache root: produced at root idx, available to later roots.
            produced_at.insert(root.expr, idx);
        }
    }

    // Walk each root in order. For each expr encountered we record
    // (expr_id, root_idx_of_use).
    let mut all_refs: Vec<(ExprId, usize)> = Vec::new();

    for (root_idx, root) in layer.roots.iter().enumerate() {
        dfs_collect_refs(
            layer,
            root.expr,
            root_idx,
            ctx,
            &mut all_refs,
            &mut dep_edges,
            &mut reached_resolutions,
        );
    }

    // Accumulate refcounts and determine is_candidate / field / width / miss.
    for &(expr_id, use_root_idx) in &all_refs {
        let entry = info.entry(expr_id).or_insert_with(|| {
            let field = child_operand_field(
                layer,
                expr_id,
                OperandField::Base,
                &ctx.cross_layer_fields,
            );
            let width = if field == OperandField::Ext { 4 } else { 1 };
            let miss = compute_miss(layer, expr_id);
            let has_backing = has_global_backing(layer, expr_id);
            ValueInfo {
                refcount: 0,
                field,
                width,
                is_candidate: false,
                miss,
                has_backing,
                is_source_resident: false,
            }
        });
        entry.refcount += 1;

        // is_candidate: this expr has a use at a root index strictly after its
        // production root. For non-cache exprs, `produced_at` has no entry;
        // they are effectively produced at the first root that uses them, so we
        // compare against `use_root_idx` itself — they can only be candidates
        // if seen again from a later root. We handle this correctly because
        // `produced_at` defaults to `use_root_idx` for non-cache exprs (they
        // are never pre-produced), but a LATER root seeing the same ExprId again
        // will have `use_root_idx > produced_at[expr_id]` if we record the
        // production at first-use. However, for the main use case (cache roots)
        // `produced_at` is explicitly set.
        //
        // For non-cache compound exprs: they are not "pre-materialized" — they
        // are recomputed on every use — so `produced_at` has no entry. We set
        // `prod = use_root_idx` meaning they are never candidates on first use,
        // but if the SAME compound ExprId appears in a later root (which can
        // only happen due to hash-consing), that second reference at a higher
        // root_idx compared to first_seen would qualify. We track first_seen
        // below to handle this correctly.
        let prod = produced_at.get(&expr_id).copied();
        if let Some(prod_idx) = prod {
            if use_root_idx > prod_idx {
                entry.is_candidate = true;
            }
        }
        // For non-cache exprs (no produced_at entry): a second reference in a
        // later root makes them candidates. We detect this via refcount > 1 AND
        // the second reference having a higher root idx. But since we don't store
        // the "first use root" per expr in a separate map here, we use a simpler
        // approach: record first_use_root lazily.
    }

    // For non-cache exprs with no produced_at entry: detect multi-root reuse.
    // We need to track the first root index at which each expr was referenced,
    // then mark is_candidate if any later root also references it.
    // Do a second pass to fill this in.
    let mut first_use_root: HashMap<ExprId, usize> = HashMap::new();
    for &(expr_id, use_root_idx) in &all_refs {
        let first = first_use_root.entry(expr_id).or_insert(use_root_idx);
        if use_root_idx > *first && !produced_at.contains_key(&expr_id) {
            // Non-cache expr referenced in a later root than first seen → candidate.
            if let Some(entry) = info.get_mut(&expr_id) {
                entry.is_candidate = true;
            }
        }
    }

    // Dedup reached_resolutions (preserve encounter order, stable).
    let mut seen = std::collections::HashSet::new();
    let keys: Vec<ExprId> = reached_resolutions
        .into_iter()
        .filter(|id| seen.insert(*id))
        .collect();

    // Source-residency candidates: a `Read` source loaded/borrowed as a FOLD OPERAND
    // ≥2× over the EMITTED (materialize-bearing) trees. Claim-only (Constraint) roots
    // are dropped by the forward emitter (mod.rs skips `materialize.is_none()` roots),
    // so we walk materialize-bearing roots only.
    //
    // EMISSION-EXACT (Lever A): we mirror the three emitter elisions so a flagged read
    // is provably loaded/borrowed by the emitter (else admitting it pins a cell the
    // emitter never reads — which on add_sub/mul_div L0 fragments an Ext-aligned block
    // and raises the compile floor 8→12):
    //   (a) zero-annihilated `Mul([0,s])` reads — dropped by `count_read_uses` above.
    //   (b) CopyAlias-action roots — lowered with allow_source_load=false /
    //       allow_resident_smem=false (mod.rs CopyAlias arm); emit no source load.
    //   (c) sole-source passthrough roots (top expr is a bare `Read`) — fused to one
    //       direct MOV (arith.rs allow_source_load=false); no borrowable fold operand.
    // `ctx.actions` is populated at mod.rs:84 before analyze_layer at mod.rs:93, so the
    // CopyAlias classification is available here. (A floor-irrelevant residual remains:
    // a handful of mul_div interior reads flagged-but-not-admitted; harmless — they are
    // never pinned and do not affect the floor or dram_reads. Closing them would need
    // the emitted-Global-stream derivation, out of scope.)
    let mut read_use_counts: HashMap<ExprId, u32> = HashMap::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        // Materialize-bearing (forward-emitted) roots only; claim-only roots emit nothing.
        if root.materialize.is_none() {
            continue;
        }
        let rid = RootId(idx as u32);
        // (b) CopyAlias roots emit no source bytecode.
        if matches!(ctx.actions.get(&rid), Some(ForwardAction::CopyAlias { .. })) {
            continue;
        }
        // (c) Sole-source passthrough roots fuse to one MOV.
        if is_read_source(layer, root.expr) {
            continue;
        }
        count_read_uses(layer, root.expr, &mut read_use_counts);
    }
    for (expr_id, n) in read_use_counts {
        if n >= 2 {
            if let Some(entry) = info.get_mut(&expr_id) {
                entry.is_source_resident = true;
            }
        }
    }

    ValueGraph { info, dep_edges, descriptors: DescriptorPlan { keys } }
}

/// DFS walk of an expression tree rooted at `expr_id`, called within the context
/// of `root_idx` (the index of the enclosing root). Appends to `all_refs` for
/// every expr encountered.
///
/// Part B: same-layer cache reuse is now a recomputed shared `ExprId` — an ordinary
/// `Expr` child the DFS descends into — so there is no longer a `SourceKind::Prior`
/// arm (and no `dep_edges` pushed for it).
///
/// Resolution pruning: if `layer.resolutions.contains_key(&expr_id)`, record the
/// ref and append the `expr_id` to `reached_resolutions`, but do NOT descend.
#[allow(clippy::too_many_arguments)]
fn dfs_collect_refs(
    layer: &DagLayer,
    expr_id: ExprId,
    root_idx: usize,
    ctx: &DagForwardContext,
    all_refs: &mut Vec<(ExprId, usize)>,
    dep_edges: &mut Vec<(ValueId, ValueId)>,
    reached_resolutions: &mut Vec<ExprId>,
) {
    all_refs.push((expr_id, root_idx));

    // Resolution pruning: treat as a terminal, do not descend.
    if layer.resolutions.contains_key(&expr_id) {
        reached_resolutions.push(expr_id);
        return;
    }

    match &layer.exprs[expr_id.0 as usize] {
        Expr::Source(_) => {
            // Source nodes are terminals — no children.
        }
        Expr::Add(children) | Expr::Mul(children) => {
            let children = children.clone();
            for child_id in children {
                dfs_collect_refs(
                    layer,
                    child_id,
                    root_idx,
                    ctx,
                    all_refs,
                    dep_edges,
                    reached_resolutions,
                );
            }
        }
    }
}

/// Return `true` if `expr_id` has a real DRAM backing that can be re-read via
/// `OperandLine::Global` — i.e. it is a `SourceKind::Read` or `VirtualSetup` leaf.
/// Returns `false` for compound exprs, literals, and resolution-pruned leaves (those
/// are re-gathered or recomputed, not re-read from DRAM).
fn has_global_backing(layer: &DagLayer, expr_id: ExprId) -> bool {
    // Resolution-pruned → special gather, no DRAM backing.
    if layer.resolutions.contains_key(&expr_id) {
        return false;
    }
    match &layer.exprs[expr_id.0 as usize] {
        Expr::Source(src_id) => {
            matches!(
                &layer.sources[src_id.0 as usize].kind,
                SourceKind::Read { .. } | SourceKind::VirtualSetup { .. }
            )
        }
        Expr::Add(_) | Expr::Mul(_) => false,
    }
}

/// Compute the miss penalty for an expression.
///
/// - Resolution-pruned (`layer.resolutions.contains_key`) → `MISS_SPECIAL_GATHER`.
/// - `Expr::Source`: `Read`/`VirtualSetup` → `MISS_BACKED_READ`;
///   `Constant`/`Challenge` → `MISS_LITERAL`; `LookupValue` (uncovered leaf) → `MISS_LITERAL`.
/// - `Expr::Add`/`Expr::Mul` → recursive recompute cost (sum over subtree,
///   plus 1 instr for the fold itself).
fn compute_miss(layer: &DagLayer, expr_id: ExprId) -> MissPenalty {
    if layer.resolutions.contains_key(&expr_id) {
        return MISS_SPECIAL_GATHER;
    }
    match &layer.exprs[expr_id.0 as usize] {
        Expr::Source(src_id) => {
            match &layer.sources[src_id.0 as usize].kind {
                SourceKind::Read { .. }
                | SourceKind::VirtualSetup { .. } => MISS_BACKED_READ,
                SourceKind::Constant { .. }
                | SourceKind::Challenge { .. }
                | SourceKind::LookupValue { .. } => MISS_LITERAL,
            }
        }
        Expr::Add(children) | Expr::Mul(children) => {
            let children = children.clone();
            let mut total = MissPenalty { dram_reads: 0, instrs: 1, cell_ops: 0 };
            for &child_id in &children {
                let child_cost = compute_miss(layer, child_id);
                total.dram_reads += child_cost.dram_reads;
                total.instrs += child_cost.instrs;
                total.cell_ops += child_cost.cell_ops;
            }
            total
        }
    }
}

// ── Stage-3 helper ────────────────────────────────────────────────────────────

/// Stage-3 helper: intern each reached resolution descriptor into `ctx.specials`
/// exactly once, returning the `ExprId → special index` map.
///
/// For each key in `plan.keys`, this calls `lower_resolution(&layer.resolutions[&id], id)`
/// and pushes the resulting descriptor via `SpecialTable::push` (which does NOT dedup —
/// so calling this once per key guarantees `special_gathers == distinct descriptors`).
///
/// The returned map is used by Stage-3 emit instead of calling `resolve_or_descend`
/// per use-site (which pushed a fresh descriptor on every reference of the same leaf).
pub fn materialize_descriptors(
    plan: &DescriptorPlan,
    layer: &DagLayer,
    ctx: &mut DagForwardContext,
) -> HashMap<ExprId, u16> {
    let mut map = HashMap::with_capacity(plan.keys.len());
    for &id in &plan.keys {
        let strategy = layer.resolutions.get(&id)
            .expect("DescriptorPlan key must be present in layer.resolutions");
        let desc = lower_resolution(strategy, id);
        let idx = ctx.specials.push(desc);
        map.insert(id, idx);
    }
    map
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fwd::context::ForwardAction;
    use cs::definitions::GKRAddress;
    use cs::gkr_compiler::dag_ir::{
        ArenaBuilder, BatchingOrder, ClaimInfo, DagLayer, FieldKind, ReadPlace, ResolutionStrategy, Root,
        RootGroup, RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceKind,
    };
    use std::collections::BTreeMap;

    fn make_ctx() -> DagForwardContext {
        DagForwardContext::default()
    }

    // ── Fixture: layer with two distinct PEEKs and one duplicate ──────────────
    //
    // root0 = resolution-leaf A (PeekSetup)
    // root1 = resolution-leaf B (PeekAggregate{0})
    // root2 = resolution-leaf A again (same ExprId) — a duplicate reference
    //
    // Analysis must yield exactly 2 distinct descriptor keys (A and B).
    fn layer_with_two_peeks_one_dup() -> DagLayer {
        let mut arena = ArenaBuilder::new();
        // Expr 0: a constant source — will become resolution-leaf A
        let s0 = arena.intern_source(SourceKind::Constant { value: 2 });
        let leaf_a = arena.source_expr(s0);
        // Expr 1: a second constant source — will become resolution-leaf B
        let s1 = arena.intern_source(SourceKind::Constant { value: 3 });
        let leaf_b = arena.source_expr(s1);

        let mut resolutions = BTreeMap::new();
        resolutions.insert(leaf_a, ResolutionStrategy::PeekSetup);
        resolutions.insert(leaf_b, ResolutionStrategy::PeekAggregate { set_index: 0 });

        DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![
                claim_inner_root(leaf_a, 0),
                claim_inner_root(leaf_b, 1),
                claim_inner_root(leaf_a, 2), // duplicate
            ],
            batching: BatchingOrder { roots: vec![] },
            resolutions,
        }
    }

    /// A claim-bearing Inner-output `Root` materializing at `offset` (its own relation).
    /// The Stage-1 "old non-cache Output root": `materialize.is_some() && claim.is_some()`.
    fn claim_inner_root(expr: cs::gkr_compiler::dag_ir::ExprId, offset: usize) -> Root {
        Root {
            expr,
            materialize: Some(SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset },
                field: FieldKind::Base,
            }),
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: offset,
                    slot: RootSlot::Output(0),
                },
            }),
        }
    }

    // ── Fixture: layer with one reached and one unreached resolution ──────────
    //
    // leaf_used  is the root's expr AND has a resolutions entry → reached.
    // leaf_unused is NOT referenced by any root but HAS a resolutions entry → unreached.
    //
    // Analysis must plan only leaf_used (1 key); materialize must intern only that one.
    fn layer_one_used_one_unused_resolution() -> DagLayer {
        let mut arena = ArenaBuilder::new();
        // Expr 0: reached leaf
        let s0 = arena.intern_source(SourceKind::Constant { value: 2 });
        let leaf_used = arena.source_expr(s0);
        // Expr 1: unreached leaf — has a resolution entry but no root references it
        let s1 = arena.intern_source(SourceKind::Constant { value: 3 });
        let leaf_unused = arena.source_expr(s1);

        let mut resolutions = BTreeMap::new();
        resolutions.insert(leaf_used, ResolutionStrategy::PeekSetup);
        resolutions.insert(leaf_unused, ResolutionStrategy::PeekSetup);

        DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![
                claim_inner_root(leaf_used, 0),
                // leaf_unused is deliberately not a root and not referenced by any root
            ],
            batching: BatchingOrder { roots: vec![] },
            resolutions,
        }
    }

    // Mirror of `mod.rs::tests::cache_root_computes_and_materializes` but with a
    // second root REUSING root0's value via the shared `ExprId`:
    //   root0 = Add(memA, memB)   -- cache root (Cache sink, no claim), produced at index 0
    //   root1 = Mul(add_ab, memC) -- at index 1, reuses root0's value (Part B: a shared
    //                                ExprId child, NOT a `Prior` source)
    //
    // The ExprId of root0's expr (the Add) must be marked is_candidate = true
    // because it has a later use (root1's Mul references `add_ab` directly, a use of
    // the cache root's value at a root index after its production point).
    #[test]
    fn analyze_marks_single_prior_cache_root_as_candidate() {
        let mut arena = ArenaBuilder::new();

        // Sources: three memory reads
        let sa = arena.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerMemory { column: 0 },
        });
        let sb = arena.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerMemory { column: 1 },
        });
        let sc = arena.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerMemory { column: 2 },
        });

        let a = arena.source_expr(sa);
        let b = arena.source_expr(sb);
        let c = arena.source_expr(sc);

        // root0: Add(a, b) — a cache root (Cache sink, no claim).
        let add_ab = arena.add(vec![a, b]);

        // root1: Mul(add_ab, c) — reuses root0's value through the SHARED ExprId `add_ab`.
        let mul_prior_c = arena.mul(vec![add_ab, c]);

        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![
                Root {
                    expr: add_ab,
                    materialize: Some(SinkInfo {
                        kind: SinkKind::Cache { layer: 3, offset: 5 },
                        field: FieldKind::Base,
                    }),
                    claim: None, // Cache + no claim → cache root
                },
                claim_inner_root(mul_prior_c, 0),
            ],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        };

        let ctx = make_ctx();
        let graph = analyze_layer(&layer, &ctx);

        // root0's expr (add_ab) must be a candidate: it has a later use (root1 reuses it).
        assert!(
            graph.info[&add_ab].is_candidate,
            "a cache root with even one later reuse must be a residency candidate (#8)"
        );
    }

    // ── Task 1: Source-residency candidate detection ──────────────────────────

    #[test]
    fn source_resident_flags_reused_read_not_virtualsetup() {
        use cs::gkr_compiler::dag_ir::{ReadPlace, VirtualSetupKind};
        let mut a = ArenaBuilder::new();
        let r_sid  = a.intern_source(SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 3 } });
        let vs_sid = a.intern_source(SourceKind::VirtualSetup { kind: VirtualSetupKind::RangeCheck16Bits });
        let er  = a.source_expr(r_sid);
        let evs = a.source_expr(vs_sid);
        let root_expr = a.add(vec![er, er, evs, evs]); // read used 2x, vsetup used 2x

        let layer = DagLayer {
            sources: a.sources().to_vec(),
            exprs: a.exprs().to_vec(),
            roots: vec![claim_inner_root(root_expr, 0)],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        };
        let ctx = make_ctx();
        let g = analyze_layer(&layer, &ctx);
        assert!(g.info[&er].is_source_resident, "reused Read source must be a residency candidate");
        assert!(!g.info[&evs].is_source_resident, "VirtualSetup is computed, never a residency candidate");
    }

    #[test]
    fn identical_read_sources_dedup_to_one_exprid() {
        use cs::gkr_compiler::dag_ir::ReadPlace;
        let mut a = ArenaBuilder::new();
        let s1 = a.intern_source(SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 7 } });
        let s2 = a.intern_source(SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 7 } });
        assert_eq!(s1, s2, "intern_source must dedup identical Read sources (ExprId-keying depends on it)");
    }

    // ── Lever A: emission-exact candidate set ─────────────────────────────────

    // (a) A Read buried in a zero-annihilated Mul([0, read]) must NOT be flagged:
    //     compile_add drops the whole Mul subtree (is_zero_expr), so the read is
    //     never emitted. Without the Mul-node zero guard in count_read_uses the read
    //     would be counted twice (once per Mul) and falsely flagged.
    #[test]
    fn candidate_skips_zero_annihilated_mul_read() {
        use cs::gkr_compiler::dag_ir::ReadPlace;
        let mut a = ArenaBuilder::new();
        let r_sid = a.intern_source(SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 3 } });
        let z_sid = a.intern_source(SourceKind::Constant { value: 0 });
        let er = a.source_expr(r_sid);
        let ez = a.source_expr(z_sid);
        let m0 = a.mul(vec![ez, er]);
        let m1 = a.mul(vec![ez, er]);
        let root_expr = a.add(vec![m0, m1]); // read appears 2x, but only inside zero Muls

        let layer = DagLayer {
            sources: a.sources().to_vec(),
            exprs: a.exprs().to_vec(),
            roots: vec![claim_inner_root(root_expr, 0)],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        };
        let ctx = make_ctx();
        let g = analyze_layer(&layer, &ctx);
        assert!(
            !g.info[&er].is_source_resident,
            "a Read only inside zero-annihilated Mul([0,s]) must NOT be a residency candidate (emitter drops it)"
        );
    }

    // (b) A CopyAlias-action root emits NO source bytecode, so its reads must not be
    //     counted. Synthetic isolation fixture: the CopyAlias root's top expr is an
    //     Add (NOT a bare Read), so category (c) cannot fire — this isolates (b).
    #[test]
    fn candidate_skips_copyalias_root_read() {
        use cs::gkr_compiler::dag_ir::ReadPlace;
        let mut a = ArenaBuilder::new();
        let r_sid = a.intern_source(SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 4 } });
        let er = a.source_expr(r_sid);
        let root_expr = a.add(vec![er, er]); // read 2x under a CopyAlias root

        let layer = DagLayer {
            sources: a.sources().to_vec(),
            exprs: a.exprs().to_vec(),
            roots: vec![claim_inner_root(root_expr, 0)],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        };
        let mut ctx = make_ctx();
        ctx.actions.insert(
            RootId(0),
            ForwardAction::CopyAlias { src_addr: GKRAddress::placeholder(), dst_addr: GKRAddress::placeholder() },
        );
        let g = analyze_layer(&layer, &ctx);
        assert!(
            !g.info[&er].is_source_resident,
            "a Read under a CopyAlias-action root must NOT be a residency candidate (CopyAlias emits no source load)"
        );
    }

    // (c) A Read that is the SOLE top expr of an Output root is passthrough-fused into
    //     one direct MOV (allow_source_load=false), emitting no borrowable fold operand.
    //     Two such roots reading the same Read column reach count 2 pre-lever; the
    //     sole-source skip must drop both. Default (Compute) action → category (b) inert.
    #[test]
    fn candidate_skips_sole_source_passthrough_read() {
        use cs::gkr_compiler::dag_ir::ReadPlace;
        let mut a = ArenaBuilder::new();
        let r_sid = a.intern_source(SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 5 } });
        let er = a.source_expr(r_sid);

        let layer = DagLayer {
            sources: a.sources().to_vec(),
            exprs: a.exprs().to_vec(),
            roots: vec![
                claim_inner_root(er, 0), // bare-read passthrough
                claim_inner_root(er, 1), // bare-read passthrough (same ExprId)
            ],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        };
        let ctx = make_ctx();
        let g = analyze_layer(&layer, &ctx);
        assert!(
            !g.info[&er].is_source_resident,
            "a Read that is only ever a root's sole expr is passthrough-fused, never a residency candidate"
        );
    }

    // Negative guard (over-pruning) + positive case: an Add is NEVER pruned. A Read
    // used 2x directly inside an Add IS flagged, even when a sibling is a zero Mul —
    // the zero Mul's own read is dropped, but the Add's reads survive.
    #[test]
    fn candidate_keeps_read_in_add_with_zero_mul_sibling() {
        use cs::gkr_compiler::dag_ir::ReadPlace;
        let mut a = ArenaBuilder::new();
        let kept_sid = a.intern_source(SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 6 } });
        let dropped_sid = a.intern_source(SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: 7 } });
        let z_sid = a.intern_source(SourceKind::Constant { value: 0 });
        let kept = a.source_expr(kept_sid);
        let dropped = a.source_expr(dropped_sid);
        let ez = a.source_expr(z_sid);
        // `dropped` appears in TWO zero Muls so its pre-guard count is 2 (would be
        // flagged WITHOUT the guard) — this makes the drop assertion non-vacuous.
        let zero_mul_a = a.mul(vec![ez, dropped]); // annihilated → dropped read elided
        let zero_mul_b = a.mul(vec![ez, dropped]); // same ExprId (hash-consed) → count 2 pre-guard
        let root_expr = a.add(vec![kept, kept, zero_mul_a, zero_mul_b]);

        let layer = DagLayer {
            sources: a.sources().to_vec(),
            exprs: a.exprs().to_vec(),
            roots: vec![claim_inner_root(root_expr, 0)],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        };
        let ctx = make_ctx();
        let g = analyze_layer(&layer, &ctx);
        assert!(
            g.info[&kept].is_source_resident,
            "a Read used 2x directly inside an Add MUST stay a candidate (Adds are never pruned)"
        );
        assert!(
            !g.info[&dropped].is_source_resident,
            "a Read only inside a zero Mul sibling must be dropped (does not poison the Add's reads)"
        );
    }

    // ── Task 7: DescriptorPlan ────────────────────────────────────────────────

    #[test]
    fn descriptor_plan_dedups_and_analysis_is_pure() {
        let ctx = DagForwardContext::default();
        let before = ctx.specials.len();
        let layer = layer_with_two_peeks_one_dup();
        let graph = analyze_layer(&layer, &ctx);
        assert_eq!(graph.descriptors.keys.len(), 2, "two distinct PEEK descriptors expected");
        assert_eq!(ctx.specials.len(), before, "analysis must not mutate ctx.specials");
    }

    #[test]
    fn descriptor_plan_excludes_unreached_resolutions() {
        // layer.resolutions has TWO entries; only ONE is reached as an operand/root.
        let ctx = DagForwardContext::default();
        let layer = layer_one_used_one_unused_resolution();
        let graph = analyze_layer(&layer, &ctx);
        assert_eq!(graph.descriptors.keys.len(), 1, "only the reached resolution is planned (no orphan)");
        let mut ctx2 = DagForwardContext::default();
        materialize_descriptors(&graph.descriptors, &layer, &mut ctx2);
        assert_eq!(ctx2.specials.len(), 1, "materialize interns only the reached descriptor — no orphan for validate_special_bindings");
    }
}
