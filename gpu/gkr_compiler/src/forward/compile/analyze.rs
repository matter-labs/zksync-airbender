//! Stage-1 value graph: refcounts, next-use distances, and candidate eligibility.
//!
//! `analyze_layer` is a PURE analysis pass — it reads `&DagLayer` and
//! `&DagForwardContext` but NEVER mutates the context. It produces a `ValueGraph`
//! consumed by every downstream residency-planner task (S2+).

use super::super::context::{DagForwardContext, ForwardAction};
use super::super::isa::OperandField;
use super::super::source::lower_resolution;
use super::arith::{child_operand_field, is_zero_expr};
use gkr_eval_ir::{DagLayer, Expr, ExprId, RootId, SinkInfo, SinkKind, SourceKind};
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
    /// `SourceKind::Read` or `VirtualSetup` (→ `OperandLine::LogicalGlobal`).
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
const MISS_BACKED_READ: MissPenalty = MissPenalty {
    dram_reads: 1,
    instrs: 1,
    cell_ops: 0,
};

/// Miss cost for a PEEK / special gather (resolution-pruned fold): one instruction,
/// no DRAM (the special source is a precomputed array indexed at runtime).
const MISS_SPECIAL_GATHER: MissPenalty = MissPenalty {
    dram_reads: 0,
    instrs: 1,
    cell_ops: 0,
};

/// Miss cost for a near-free literal (`Constant` or `Challenge`): zero.
const MISS_LITERAL: MissPenalty = MissPenalty {
    dram_reads: 0,
    instrs: 0,
    cell_ops: 0,
};

// ── Analysis ──────────────────────────────────────────────────────────────────

/// True iff `expr_id` is a `SourceKind::Read` source (a DRAM read). `VirtualSetup` is
/// excluded — it lowers to a `Global` operand but is resolved by computation
/// (interp.rs:148), not `r.read`, so caching it saves no DRAM read.
fn is_read_source(layer: &DagLayer, expr_id: ExprId) -> bool {
    if let Expr::Source(src_id) = &layer.exprs[expr_id.0 as usize] {
        matches!(
            layer.sources[src_id.0 as usize].kind,
            SourceKind::Read { .. }
        )
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
            Some(SinkInfo {
                kind: SinkKind::Cache { .. },
                ..
            })
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
            let field =
                child_operand_field(layer, expr_id, OperandField::Base, &ctx.cross_layer_fields);
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

    ValueGraph {
        info,
        dep_edges,
        descriptors: DescriptorPlan { keys },
    }
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
/// `OperandLine::LogicalGlobal` — i.e. it is a `SourceKind::Read` or `VirtualSetup` leaf.
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
        Expr::Source(src_id) => match &layer.sources[src_id.0 as usize].kind {
            SourceKind::Read { .. }
            | SourceKind::VirtualSetup { .. }
            | SourceKind::InitsAndTeardownsTopBits { .. } => MISS_BACKED_READ,
            SourceKind::Constant { .. }
            | SourceKind::Challenge { .. }
            | SourceKind::LookupValue { .. } => MISS_LITERAL,
        },
        Expr::Add(children) | Expr::Mul(children) => {
            let children = children.clone();
            let mut total = MissPenalty {
                dram_reads: 0,
                instrs: 1,
                cell_ops: 0,
            };
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
/// so calling this once per key guarantees `special_gathers == distinct non-VirtualSetup
/// (peek) descriptors`, since `special_gathers` now excludes computed `VirtualSetup` entries).
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
        let strategy = layer
            .resolutions
            .get(&id)
            .expect("DescriptorPlan key must be present in layer.resolutions");
        let desc = lower_resolution(strategy, id);
        let idx = ctx.specials.push(desc);
        map.insert(id, idx);
    }
    map
}

// ── Tests ─────────────────────────────────────────────────────────────────────
