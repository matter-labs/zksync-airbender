//! Stage-1 value graph: refcounts, next-use distances, and candidate eligibility.
//!
//! `analyze_layer` is a PURE analysis pass — it reads `&DagLayer` and
//! `&DagForwardContext` but NEVER mutates the context. It produces a `ValueGraph`
//! consumed by every downstream residency-planner task (S2+).

use super::arith::child_operand_field;
use super::super::context::DagForwardContext;
use super::super::isa::OperandField;
use cs::gkr_compiler::dag_ir::{
    DagLayer, Expr, ExprId, RootId, Root, SourceKind,
};
use std::collections::HashMap;

// ── Public types ─────────────────────────────────────────────────────────────

/// A `ValueId` is simply an `ExprId` — the dag is hash-consed, so an `ExprId`
/// IS a value identity.
pub type ValueId = ExprId;

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
    /// available — including a cache root whose single later use is a `Prior` read.
    pub is_candidate: bool,
    /// Estimated cost to re-obtain this value if evicted from residency.
    pub miss: MissPenalty,
}

/// The value graph produced by `analyze_layer`.
pub struct ValueGraph {
    /// Per-value facts, keyed by `ExprId`.
    pub info: HashMap<ValueId, ValueInfo>,
    /// Dependency edges: `(use, producer)`. A `Prior{id}` source generates an
    /// edge from the using expr to the cache root's output expr.
    pub dep_edges: Vec<(ValueId, ValueId)>,
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

/// Pure Stage-1 value graph analysis.
///
/// Walks `layer.roots` and their expr subtrees, computing:
/// - `refcount` — total reference count across all root expr trees
/// - `field` / `width` — via the PURE `child_operand_field` (reads only `layer`
///   + `ctx.cross_layer_fields`, NEVER `ctx.specials` / `ctx.backings`)
/// - `is_candidate` — true when a value has any use AFTER its production point
/// - `miss` — recompute / re-obtain cost for the residency planner
/// - `dep_edges` — `(use_expr_id, producer_expr_id)` pairs
///
/// Resolution pruning: if `layer.resolutions.contains_key(&id)`, the value's
/// `miss` is `MISS_SPECIAL_GATHER` and analysis does NOT descend into children
/// for refcounts or recompute cost.
///
/// PURE: takes `&DagForwardContext` and MUST NOT mutate it.
pub fn analyze_layer(layer: &DagLayer, ctx: &DagForwardContext) -> ValueGraph {
    let mut info: HashMap<ValueId, ValueInfo> = HashMap::new();
    let mut dep_edges: Vec<(ValueId, ValueId)> = Vec::new();

    // Build a map: RootId → ExprId for all cache roots (roots with no origin).
    // This lets us resolve `SourceKind::Prior{id}` to the producer expr.
    let mut cache_root_expr: HashMap<RootId, ExprId> = HashMap::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        if let Root::Output { expr, .. } = root {
            let rid = RootId(idx as u32);
            if !layer.origins.contains_key(&rid) {
                cache_root_expr.insert(rid, *expr);
            }
        }
    }

    // produced_at[expr_id] = root index that "produces" this value.
    // For a cache root's output expr: the root index that materializes it.
    // All other exprs are produced on demand (no dedicated entry — they are
    // produced at the same root that first references them, so any LATER root
    // referencing them qualifies as a later use).
    let mut produced_at: HashMap<ExprId, usize> = HashMap::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        if let Root::Output { expr, .. } = root {
            let rid = RootId(idx as u32);
            if !layer.origins.contains_key(&rid) {
                // Cache root: produced at root idx, available to later roots.
                produced_at.insert(*expr, idx);
            }
        }
    }

    // Walk each root in order. For each expr encountered we record
    // (expr_id, root_idx_of_use). Additionally, when a `Prior{id}` source is
    // encountered at root_idx, we record a logical "use" of the cache root's
    // OUTPUT EXPR at root_idx so the candidate check fires on the right expr.
    // (The `prior_expr` itself — the `Source(Prior{id})` — is a separate node
    // from the cache root's expr; we must mark the CACHE ROOT's expr as candidate.)
    let mut all_refs: Vec<(ExprId, usize)> = Vec::new();

    for (root_idx, root) in layer.roots.iter().enumerate() {
        let root_expr = match root {
            Root::Output { expr, .. } => *expr,
            Root::Constraint { expr } => *expr,
        };
        dfs_collect_refs(
            layer,
            root_expr,
            root_idx,
            ctx,
            &cache_root_expr,
            &mut all_refs,
            &mut dep_edges,
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
            ValueInfo {
                refcount: 0,
                field,
                width,
                is_candidate: false,
                miss,
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

    ValueGraph { info, dep_edges }
}

/// DFS walk of an expression tree rooted at `expr_id`, called within the context
/// of `root_idx` (the index of the enclosing root). Appends to `all_refs` for
/// every expr encountered (including logical "producer expr" refs for `Prior`
/// sources), and records dep_edges for `Prior` sources.
///
/// Resolution pruning: if `layer.resolutions.contains_key(&expr_id)`, record the
/// ref but do NOT descend into children.
#[allow(clippy::too_many_arguments)]
fn dfs_collect_refs(
    layer: &DagLayer,
    expr_id: ExprId,
    root_idx: usize,
    ctx: &DagForwardContext,
    cache_root_expr: &HashMap<RootId, ExprId>,
    all_refs: &mut Vec<(ExprId, usize)>,
    dep_edges: &mut Vec<(ValueId, ValueId)>,
) {
    all_refs.push((expr_id, root_idx));

    // Resolution pruning: treat as a terminal, do not descend.
    if layer.resolutions.contains_key(&expr_id) {
        return;
    }

    match &layer.exprs[expr_id.0 as usize] {
        Expr::Source(src_id) => {
            match &layer.sources[src_id.0 as usize].kind {
                SourceKind::Prior { id } => {
                    // Prior source: record dep edge and also record a "use" of the
                    // cache root's output expr at this root index so the candidate
                    // check fires on the correct expr (the cache root's computed expr,
                    // not the `Prior` source node itself).
                    if let Some(&producer_expr) = cache_root_expr.get(id) {
                        dep_edges.push((expr_id, producer_expr));
                        // Record the cache root's expr as used at this root index.
                        // This is the key that makes `add_ab` (the cache root's expr)
                        // a candidate: it will have both a ref at root 0 (produced_at=0)
                        // and a ref at root 1 (from the Prior use), making use_root_idx
                        // (1) > produced_at (0).
                        all_refs.push((producer_expr, root_idx));
                    }
                }
                _ => {}
            }
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
                    cache_root_expr,
                    all_refs,
                    dep_edges,
                );
            }
        }
    }
}

/// Compute the miss penalty for an expression.
///
/// - Resolution-pruned (`layer.resolutions.contains_key`) → `MISS_SPECIAL_GATHER`.
/// - `Expr::Source`: `Read`/`VirtualSetup`/`Prior` → `MISS_BACKED_READ`;
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
                | SourceKind::VirtualSetup { .. }
                | SourceKind::Prior { .. } => MISS_BACKED_READ,
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

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{
        ArenaBuilder, BatchingOrder, FieldKind, ReadPlace, Root, SinkId, SinkInfo, SinkKind,
        SourceKind,
    };
    use std::collections::BTreeMap;

    fn make_ctx() -> DagForwardContext {
        DagForwardContext::default()
    }

    // Mirror of `mod.rs::tests::cache_root_computes_and_materializes` but with a
    // second root reading `Prior(root0)`:
    //   root0 = Add(memA, memB)   -- cache root (no origin), produced at index 0
    //   root1 = Mul(Prior(root0), memC) -- at index 1, reads the cache
    //
    // The ExprId of root0's expr (the Add) must be marked is_candidate = true
    // because it has a later Prior use (root1's Mul references Prior(root0),
    // which is a use of the cache root's value after its production point).
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

        // root0: Add(a, b) — a cache root (no origin entry)
        let add_ab = arena.add(vec![a, b]);

        // Prior source reading root0 (RootId(0))
        let prior_root0 = arena.intern_source(SourceKind::Prior {
            id: RootId(0),
        });
        let prior_expr = arena.source_expr(prior_root0);

        // root1: Mul(Prior(root0), c)
        let mul_prior_c = arena.mul(vec![prior_expr, c]);

        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![
                Root::Output { expr: add_ab, sink: SinkId(0) },
                Root::Output { expr: mul_prior_c, sink: SinkId(1) },
            ],
            sinks: vec![
                SinkInfo {
                    kind: SinkKind::Cache { layer: 3, offset: 5 },
                    field: FieldKind::Base,
                },
                SinkInfo {
                    kind: SinkKind::Inner { layer: 3, offset: 0 },
                    field: FieldKind::Base,
                },
            ],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(), // no origins → root0 is a cache root
            resolutions: BTreeMap::new(),
        };

        let ctx = make_ctx();
        let graph = analyze_layer(&layer, &ctx);

        // root0's expr (add_ab) must be a candidate: it has a later Prior use.
        assert!(
            graph.info[&add_ab].is_candidate,
            "a cache root with even one later Prior use must be a residency candidate (#8)"
        );
    }
}
