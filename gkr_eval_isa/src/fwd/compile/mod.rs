pub mod analyze;
pub mod arith;
pub mod negate;
pub mod residency;
pub mod resolution;
pub mod schedule;

use self::analyze::{analyze_layer, materialize_descriptors};
use self::arith::{compile_expr, source_to_operand, LoweringEnv};
pub use self::arith::build_cross_layer_field_map;
use self::residency::{Loc, RefEvent, RefString, ResidencyState};
use super::binding::BackingKey;
use super::context::{
    build_forward_actions, CompileTrace, CompiledLayer, DagForwardContext, ForwardAction,
    OutputCell, RootOutput,
};
use super::stats::{CompileStats, OP_ADD, OP_FMA, OP_MOV, OP_MUL};
use super::error::CompileError;
use super::isa::{DstLine, Instr, LdcSub, MovDir, OperandField, OperandLine, Program};
use cs::gkr_compiler::dag_ir::{
    DagLayer, Expr, ExprId, FieldKind, ReadPlace, Root, RootId, SinkInfo, SinkKind,
};
use cs::gkr_compiler::GKRLayerDescription;
use cs::definitions::GKRAddress;
use std::collections::{BTreeMap, HashMap};

/// Classification of a read operand for traffic-counter tallying (spec §11).
pub(crate) enum OperandClass {
    /// `OperandLine::Global` — a DRAM read (backing slot+col).
    Dram,
    /// `OperandLine::Ldc` with `sub != LdcSub::Special` — a load-constant read.
    Ldc,
    /// `OperandLine::Ldc` with `sub == LdcSub::Special` — an inline ±1/0 literal;
    /// near-free, counted in neither `dram_reads` nor `ldc_reads`.
    SpecialLit,
    /// `OperandLine::Special{desc}` — a resolved-fold special-source gather.
    SpecialGather,
    /// `OperandLine::Smem` — a register-file (smem) cell read.
    Smem,
}

/// Classify a single read operand into its traffic category.
pub(crate) fn classify_operand(op: &OperandLine) -> OperandClass {
    match op {
        OperandLine::Global { .. } => OperandClass::Dram,
        OperandLine::Smem { .. } => OperandClass::Smem,
        OperandLine::Ldc { sub: LdcSub::Special, .. } => OperandClass::SpecialLit,
        OperandLine::Ldc { .. } => OperandClass::Ldc,
        OperandLine::Special { .. } => OperandClass::SpecialGather,
    }
}

/// Tally the traffic class of a single read operand into `stats`.
///
/// `field` is the operand's field (Base/Ext), used to width-weight `dram_traffic`.
/// `backings` is the current layer's backing table, used to identify VirtualSetup-backed
/// Global reads (which are resolver-computed, not real DRAM, and contribute 0 traffic).
fn tally_operand(
    op: &OperandLine,
    field: OperandField,
    backings: &super::binding::BackingTable,
    stats: &mut CompileStats,
) {
    match classify_operand(op) {
        OperandClass::Dram => {
            stats.dram_reads += 1; // per-operand diagnostic, unchanged
            // Width-weighted traffic: VirtualSetup-backed Global reads are
            // resolver-computed, not DRAM → 0. Others cost the field width.
            // Invariant: classify_operand returns Dram only for Global operands,
            // so this `if let` always matches; it extracts the slot to check backing.
            if let OperandLine::Global { slot, .. } = op {
                let is_virtual = matches!(
                    backings.backing(*slot),
                    Some(super::binding::BackingKey::VirtualSetup { .. })
                );
                if !is_virtual {
                    stats.dram_traffic += if field == OperandField::Ext { 4 } else { 1 };
                }
            }
        }
        OperandClass::Ldc => stats.ldc_reads += 1,
        OperandClass::SpecialLit => {} // inline literal — near-free, not counted
        OperandClass::SpecialGather => stats.special_reads += 1,
        OperandClass::Smem => stats.cell_reads += 1,
    }
}

/// Public wrapper over the crate-private `arith::child_operand_field` so test-only
/// oracle code can resolve an expr's operand field (→ cell width: Ext=4, Base=1).
pub fn expr_operand_field(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    expr_id: cs::gkr_compiler::dag_ir::ExprId,
    cross: &std::collections::HashMap<
        cs::gkr_compiler::dag_ir::ReadPlace,
        cs::gkr_compiler::dag_ir::FieldKind,
    >,
) -> super::isa::OperandField {
    arith::child_operand_field(layer, expr_id, super::isa::OperandField::Base, cross)
}

/// Compile one `dag_ir` layer to a forward program (spec §10, §11).
///
/// Walks `layer.roots` by INDEX (caches lead, so a same-layer `Prior` read of a
/// cache always sees `cache_loc[id]` already populated). Each `Root::Output` is
/// dispatched by its `ForwardAction`:
/// - `Compute`: lower the expr into the acc and materialize. A CACHE root (no
///   origin) materializes to its `CacheOutput` backing and records `cache_loc`; a
///   NORMAL output materializes via its sink backing.
/// - `CopyAlias`: emit NO instructions; lower the root's single source expr to an
///   `OperandLine` recorded as `RootOutput::Alias`.
/// - `SkipScratchPrefill`: emit nothing; record the rid in `skipped`.
/// `Root::Constraint` roots are ignored for forward.
pub fn compile_layer(
    layer: &DagLayer,
    artifact_layer: &GKRLayerDescription,
    scratch_mapping: &BTreeMap<GKRAddress, usize>,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
    budget: usize,
) -> Result<CompiledLayer, CompileError> {
    let mut ctx = DagForwardContext::default();
    ctx.actions = build_forward_actions(layer, artifact_layer, scratch_mapping)?;
    // Cross-layer field map (codex Imp2): clone the circuit-wide map so
    // `child_operand_field` labels each cross-layer read with its TRUE producing-sink
    // field. Small — one entry per cross-layer-readable sink.
    ctx.cross_layer_fields = cross_layer_fields.clone();

    // ── Stage-2 residency pre-pass (#4, #8) ──────────────────────────────────────
    // 1) PURE value-graph analysis (refcounts, fields, miss penalties, reached
    //    resolution descriptors). Reads ctx but never mutates it.
    let graph = analyze_layer(layer, &ctx);
    // 2) Intern each reached resolution descriptor into `ctx.specials` EXACTLY ONCE
    //    (Task 7). The emitter looks these up via `desc_by_expr` and NEVER calls
    //    `resolve_or_descend` again — so `special_gathers == distinct descriptors`.
    let desc_by_expr = materialize_descriptors(&graph.descriptors, layer, &mut ctx);
    // 3) `RootId → producer ExprId` for cache roots (no origin). A `Prior{id}` read
    //    maps `id` to its producer expr to query residency (info is keyed by ExprId).
    let cache_root_expr = cache_root_expr_map(layer);
    // 4) The index-order reference string: a `Produce` when a cache root materializes,
    //    a `Use` at each `Prior` read of a cache (and a candidate non-cache compound's
    //    later reuse). Drives Belady next-use distances.
    let refs = build_ref_string(layer, &cache_root_expr, &graph);
    // 5) ONE per-layer residency planner (replaces the per-root CellAllocator) — a
    //    layer-wide high-water of residents + lowering temps that must stay ≤ BUDGET.
    let mut residency = ResidencyState::new(&refs, &graph.info, budget);

    let mut program = Program::default();
    let mut trace = CompileTrace::default();
    let mut root_outputs: Vec<(RootId, RootOutput)> = Vec::new();
    let mut skipped: Vec<RootId> = Vec::new();
    // Reference-string event cursor: advanced as the root walk consumes events so the
    // residency `point` at each emit matches the pre-pass `RefString` ordering.
    let mut point: usize = 0;

    for (idx, root) in layer.roots.iter().enumerate() {
        let rid = RootId(idx as u32);
        let (expr, sink_id) = match root {
            Root::Output { expr, sink } => (*expr, *sink),
            Root::Constraint { .. } => continue, // ignored for forward
        };

        let action = ctx
            .actions
            .get(&rid)
            .cloned()
            // Every Output root is classified by build_forward_actions.
            .ok_or(CompileError::OutputUnresolved(rid))?;

        match action {
            ForwardAction::Compute => {
                // Reject a bare 0/1 output (top expr is an empty Add/Mul) — §5.
                if is_empty_reduction(layer, expr) {
                    return Err(CompileError::DegenerateRoot(rid));
                }

                // Record the instruction count before lowering so we can detect
                // post-elision degeneracy (e.g. Mul of only `Constant{1}` factors
                // that all elide to identity → zero instructions emitted).
                let len_before = program.instrs.len();

                // The root's result field is its sink's field — pass it as the
                // `expected` hint so a fully-cross-layer expr (whose `expr_field` is
                // `Err` everywhere) labels its reads with the correct field, keeping
                // the validator's field-transition tracker consistent (Task 13).
                let sink = &layer.sinks[sink_id.0 as usize];
                let expected = operand_field_of(sink);

                // Lower the expr into the accumulator. The ONE per-layer
                // `ResidencyState` owns the single cell space holding both residents
                // (kept across roots) and this root's transient lowering temps: a
                // compound child materializes via `alloc_temp`, which evicts a backed
                // (DRAM-re-readable) resident on demand when full (emitting nothing —
                // the evicted value's later uses re-resolve via `location`). A reused
                // same-layer `Prior`/CSE value is BORROWED from its resident cell (a
                // lease pinning it for the consuming fold). No second allocator, no
                // static reservation, no pre-occupy: with one cell space the b5069ea0
                // transient/resident collision cannot occur by construction.
                {
                    let env = LoweringEnv {
                        desc_by_expr: &desc_by_expr,
                        cache_root_expr: &cache_root_expr,
                        point,
                        allow_resident_smem: true,
                    };
                    compile_expr(
                        layer,
                        expr,
                        &mut ctx,
                        &mut residency,
                        &mut trace,
                        &mut program.instrs,
                        expected,
                        env,
                    )?;
                }

                // If lowering emitted no instructions, the root is degenerate
                // (post-elision empty): materializing now would push a stale
                // accumulator value. Reject it — §5 / §6 DegenerateRoot.
                if program.instrs.len() == len_before {
                    return Err(CompileError::DegenerateRoot(rid));
                }

                let (key, col) = sink_to_backing(sink, artifact_layer.layer);
                let slot = ctx.backings.intern(key)?;

                // Passthrough fusion: when the root lowered to exactly one
                // `MOV AccFromSrc src` (a source/PEEK that needs no arithmetic),
                // rewrite the init+materialize pair into a single direct
                // `MOV DstFromSrc dst <- src`, dropping the accumulator round-trip.
                // A PEEK gather is not storage-addressable, so it cannot be a
                // `CopyAlias` and would otherwise cost two MOVs. Safe: a single-
                // source root that validates today already has src field == sink
                // field (else the `DstFromAcc` field-transition check would reject
                // it), so the fused MOV's field is self-consistent.
                let fused = if program.instrs.len() == len_before + 1 {
                    match program.instrs[len_before] {
                        Instr::Mov {
                            dir: MovDir::AccFromSrc,
                            field,
                            src: Some(src),
                            ..
                        } => {
                            program.instrs[len_before] = Instr::Mov {
                                dir: MovDir::DstFromSrc,
                                field,
                                dst: Some(DstLine::GlobalMaterialize { slot, col }),
                                src: Some(src),
                            };
                            true
                        }
                        _ => false,
                    }
                } else {
                    false
                };

                let is_cache_root = !layer.origins.contains_key(&rid);

                // Residency (#8): keep a heavily-reused cache root resident in an smem
                // cell so its same-layer `Prior` readers read the cell (no DRAM re-read).
                // Only NON-fused cache roots qualify — a fused passthrough never lands
                // in the acc (the value is a bare source already cheap to re-read), and
                // its single MOV writes straight to Global. The resident store
                // (`MOV DstFromAcc Smem{c}`) runs BEFORE the Global materialize, so the
                // acc still carries the root's value for both writes. The Global backing
                // is ALWAYS also written (cross-layer reads + the cache backing are
                // never dropped — codex re-review Imp1).
                if !fused && is_cache_root {
                    let producer = expr;
                    let candidate = graph
                        .info
                        .get(&producer)
                        .map(|i| i.is_candidate)
                        .unwrap_or(false);
                    if candidate {
                        if let Loc::Smem(cell) = residency.admit(producer, point)? {
                            program.instrs.push(Instr::Mov {
                                dir: MovDir::DstFromAcc,
                                field: expected,
                                dst: Some(DstLine::Smem { cell }),
                                src: None,
                            });
                        }
                    }
                }

                if !fused {
                    program.instrs.push(Instr::Mov {
                        dir: MovDir::DstFromAcc,
                        field: expected,
                        dst: Some(DstLine::GlobalMaterialize { slot, col }),
                        src: None,
                    });
                }

                // A cache root (no origin) records its location for same-layer Prior reads.
                if is_cache_root {
                    ctx.cache_loc.insert(rid, (slot, col));
                }
                root_outputs
                    .push((rid, RootOutput::Cell(OutputCell::Global { slot, col })));
            }
            ForwardAction::CopyAlias { .. } => {
                // §10: a view-alias produces NO kernel bytecode. Lower the root's
                // single source expr to an OperandLine for the action executor.
                let env = LoweringEnv {
                    desc_by_expr: &desc_by_expr,
                    cache_root_expr: &cache_root_expr,
                    point,
                    // A view-alias output is read at PROGRAM END, not at this root's
                    // program point — so it must reference STABLE storage. Forbid a
                    // resident `Smem` operand (which Belady could evict/reuse before
                    // the read): a same-layer `Prior` falls through to its `Global`
                    // cache backing instead (codex S2 review, finding 1).
                    allow_resident_smem: false,
                };
                // A CopyAlias root emits NO bytecode; pass a throwaway sink and
                // `allow_source_load=false` so no load MOV is ever produced here.
                let mut alias_sink: Vec<Instr> = Vec::new();
                let (op, lease) = source_to_operand(
                    layer,
                    expr,
                    &mut ctx,
                    &mut residency,
                    &mut trace,
                    &mut alias_sink,
                    /*allow_source_load=*/ false,
                    env,
                )?;
                debug_assert!(alias_sink.is_empty(), "CopyAlias lowering must emit no bytecode");
                // `allow_resident_smem=false` guarantees the Prior arm never borrows, so
                // the lease is `None` and the operand is stable storage (never a resident
                // Smem cell, which Belady could evict before the program-end alias read).
                debug_assert!(
                    matches!(lease, arith::OperandLease::None)
                        && !matches!(op, OperandLine::Smem { .. }),
                    "CopyAlias output must be stable storage, never a resident Smem cell \
                     (RootId {}); residency must not redirect an alias operand",
                    rid.0
                );
                let _ = lease;
                root_outputs.push((rid, RootOutput::Alias(op)));
            }
            ForwardAction::SkipScratchPrefill => {
                skipped.push(rid);
            }
        }
        // Advance the residency query cursor one step per root. `location` is
        // point-insensitive, so the per-root cursor only affects Belady eviction
        // tiebreaks, which engage under cap pressure. At a loose test budget (1024)
        // nothing evicts so the granularity is moot THERE — but at a real
        // occupancy-bound budget (~8-16 cells/thread, see fwd_parity floor table)
        // eviction DOES fire, and the coarse per-root point is the known limitation
        // the deferred per-event cursor would address. Not a no-op at real budgets.
        point += 1;
    }

    trace.max_live_cells = trace.max_live_cells.max(0);

    // Build per-layer stats from the compiled program and context (spec §11).
    let mut stats = CompileStats::default();
    stats.program_lanes = program.instrs.len();
    for instr in &program.instrs {
        match instr {
            Instr::Mov { dir, dst, src, field, .. } => {
                stats.op_counts[OP_MOV] += 1;
                // Tally the read operand (src), if any.
                if let Some(op) = src {
                    tally_operand(op, *field, &ctx.backings, &mut stats);
                }
                // Count cell-targeting MOV destinations as cell_stores.
                // `GlobalMaterialize` is an output WRITE (DstLine, not OperandLine)
                // and must never be counted as a dram_read.
                // S1 note: cell_loads is left at 0 — its doc semantics overlap
                // cell_stores for the DstFromAcc→Smem evict path, and there is no
                // separate reload path yet. Do not double-count a single MOV into
                // both cell_loads and cell_stores.
                if matches!(dir, MovDir::DstFromAcc | MovDir::DstFromSrc) {
                    if matches!(dst, Some(DstLine::Smem { .. })) {
                        stats.cell_stores += 1;
                    }
                }
            }
            Instr::Add { field, operands, .. } => {
                stats.op_counts[OP_ADD] += 1;
                for op in operands {
                    tally_operand(op, *field, &ctx.backings, &mut stats);
                }
            }
            Instr::Mul { field, operands, .. } => {
                stats.op_counts[OP_MUL] += 1;
                for op in operands {
                    tally_operand(op, *field, &ctx.backings, &mut stats);
                }
            }
            Instr::Fma { field_lhs, field_rhs, pairs, .. } => {
                stats.op_counts[OP_FMA] += 1;
                for (l, r) in pairs {
                    tally_operand(l, *field_lhs, &ctx.backings, &mut stats);
                    tally_operand(r, *field_rhs, &ctx.backings, &mut stats);
                }
            }
        }
    }
    // Alias operands (CopyAlias roots, zero program lanes) still read their source.
    // Count Global aliases as dram_reads; other classes tallied the same way.
    // RootOutput::Alias has no field annotation — alias outputs are stable-storage
    // (never Smem, per the CopyAlias invariant) and always Base width.
    for (_, out) in &root_outputs {
        if let RootOutput::Alias(op) = out {
            tally_operand(op, OperandField::Base, &ctx.backings, &mut stats);
        }
    }
    // special_gathers = number of resolved-fold Specials emitted (SpecialTable length).
    stats.special_gathers = ctx.specials.len();
    // max_live_cells is the LAYER-WIDE high-water of the ONE shared cell allocator the
    // `ResidencyState` owns — residents (admitted across all roots) and transient
    // lowering temps share that single space, so its peak IS the layer's simultaneous
    // live-cell count (residents + temps + evict partials). It must stay ≤ BUDGET; the
    // allocator enforces this by construction (`alloc()` fails with BudgetBelowFloor
    // beyond budget, so this can never under-report). `residency.max_live_cells()`
    // returns that allocator's high-water; `trace.max_live_cells` is sampled from the
    // same allocator inside `lower_operand`/`emit_reduction_group`, so the `.max()` is
    // a belt-and-braces lower bound, not a separate source.
    stats.max_live_cells = residency.max_live_cells().max(trace.max_live_cells);
    // Remaining counters (inline_reads, evicts, reloads, recomputes, split_count,
    // avg_chunk) require per-instruction fine-grained tracking not yet wired in SP1.
    // cell_loads: left at 0 in S1 — see cell_stores note above.
    // SP1: not yet counted.

    Ok(CompiledLayer {
        program,
        ctx,
        root_outputs,
        skipped,
        trace,
        budget,
        stats,
    })
}

/// Build `RootId → producer ExprId` for every CACHE root (a `Root::Output` with no
/// origin). Mirrors the internal map `analyze_layer` uses, exported here so the
/// emitter can map a `SourceKind::Prior{id}` (a `RootId`) to the cache root's output
/// expr — the key `ValueInfo`/residency are keyed by (an `ExprId`).
fn cache_root_expr_map(layer: &DagLayer) -> HashMap<RootId, ExprId> {
    let mut map = HashMap::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        if let Root::Output { expr, .. } = root {
            let rid = RootId(idx as u32);
            if !layer.origins.contains_key(&rid) {
                map.insert(rid, *expr);
            }
        }
    }
    map
}

/// Build the index-order reference string for residency planning.
///
/// Walks `layer.roots` in index order. For each CACHE root (no origin) that is a
/// residency candidate, emits a `Produce(producer_expr)` at the root's production
/// point; for each `SourceKind::Prior{id}` read encountered in any root's expr tree,
/// emits a `Use(producer_expr)` at the using root's point; for each
/// `SourceKind::Read` source that is marked `is_source_resident` in an Output root,
/// emits a `Use(source_expr)` so `ResidencyState`'s next-use table sees source reuse.
/// The events drive the Belady next-use distances in `ResidencyState`. The emit-side
/// `point` cursor is advanced in the same root order so query points line up.
fn build_ref_string(
    layer: &DagLayer,
    cache_root_expr: &HashMap<RootId, ExprId>,
    graph: &self::analyze::ValueGraph,
) -> RefString {
    let mut events: Vec<RefEvent> = Vec::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        let rid = RootId(idx as u32);
        // Produce: a candidate cache root makes its value available here.
        if let Some(&producer) = cache_root_expr.get(&rid) {
            let candidate = graph.info.get(&producer).map(|i| i.is_candidate).unwrap_or(false);
            if candidate {
                events.push(RefEvent::Produce(producer));
            }
        }
        // Use: Prior reads and (for Output roots) source-resident Read sources.
        match root {
            Root::Output { expr, .. } => {
                collect_prior_uses(layer, *expr, cache_root_expr, &graph.info, /*include_sources=*/ true, &mut events);
            }
            Root::Constraint { expr } => {
                // Constraint roots are not emitted in the forward pass; keep the
                // pre-existing Prior-use behavior, suppress source uses (no emission to align to).
                collect_prior_uses(layer, *expr, cache_root_expr, &graph.info, /*include_sources=*/ false, &mut events);
            }
        }
    }
    RefString { events }
}

/// DFS an expr tree, pushing a `Use(producer_expr)` for each `SourceKind::Prior{id}`
/// that maps to a known cache root. When `include_sources` is true, also pushes a
/// `Use(expr_id)` for each `SourceKind::Read` source whose `is_source_resident` flag
/// is set (reused across ≥2 Output roots). Resolution-pruned exprs are terminals (not
/// descended), matching `analyze_layer`'s pruning.
fn collect_prior_uses(
    layer: &DagLayer,
    expr_id: ExprId,
    cache_root_expr: &HashMap<RootId, ExprId>,
    info: &HashMap<ExprId, self::analyze::ValueInfo>,
    include_sources: bool,
    events: &mut Vec<RefEvent>,
) {
    if layer.resolutions.contains_key(&expr_id) {
        return;
    }
    match &layer.exprs[expr_id.0 as usize] {
        Expr::Source(src_id) => match &layer.sources[src_id.0 as usize].kind {
            cs::gkr_compiler::dag_ir::SourceKind::Prior { id } => {
                if let Some(&producer) = cache_root_expr.get(id) {
                    events.push(RefEvent::Use(producer));
                }
            }
            cs::gkr_compiler::dag_ir::SourceKind::Read { .. } if include_sources => {
                if info.get(&expr_id).map(|i| i.is_source_resident).unwrap_or(false) {
                    events.push(RefEvent::Use(expr_id)); // a Read source is its own producer (loaded at first use)
                }
            }
            _ => {}
        },
        Expr::Add(children) | Expr::Mul(children) => {
            for &c in children {
                collect_prior_uses(layer, c, cache_root_expr, info, include_sources, events);
            }
        }
    }
}

/// Map a sink to the backing `(key, col)` its value materializes into.
/// Cache sinks land in `CacheOutput`; ordinary layer outputs in `LayerOutput`;
/// scratch in `Scratch`. `this_layer` supplies the layer index for `Export`.
fn sink_to_backing(sink: &SinkInfo, this_layer: usize) -> (BackingKey, u16) {
    match sink.kind {
        SinkKind::Cache { layer, offset } => (BackingKey::CacheOutput { layer }, offset as u16),
        SinkKind::Inner { layer, offset } => (BackingKey::LayerOutput { layer }, offset as u16),
        SinkKind::Export { slot } => (BackingKey::LayerOutput { layer: this_layer }, slot as u16),
        SinkKind::Scratch { slot } => (BackingKey::Scratch, slot as u16),
    }
}

fn operand_field_of(sink: &SinkInfo) -> OperandField {
    match sink.field {
        cs::gkr_compiler::dag_ir::FieldKind::Base => OperandField::Base,
        cs::gkr_compiler::dag_ir::FieldKind::Ext => OperandField::Ext,
    }
}

/// True if `expr` is a structurally-empty Add/Mul (zero children) — a bare 0/1
/// output (§5). Resolution-pruned exprs and sources are never empty reductions.
fn is_empty_reduction(layer: &DagLayer, expr: ExprId) -> bool {
    match &layer.exprs[expr.0 as usize] {
        Expr::Add(children) | Expr::Mul(children) => children.is_empty(),
        Expr::Source(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{
        ArenaBuilder, BatchingOrder, FieldKind, ReadPlace, Root, SinkId, SinkInfo, SinkKind,
        SourceKind,
    };
    use cs::gkr_compiler::{GKRLayerDescription, GateArtifacts};
    use std::collections::BTreeMap;

    fn artifact_layer(layer: usize) -> GKRLayerDescription {
        GKRLayerDescription {
            layer,
            gates: vec![],
            gates_with_external_connections: vec![],
            cached_relations: BTreeMap::new(),
            intermediate_layer_width: None,
        }
    }

    // A single cache root `Add(a_base, b_base)` (no origin) compiles to:
    //   MOV acc←a; ADD Base +[b]; MOV CacheOutput ← acc
    // recording cache_loc + a Global RootOutput. Smoke test of the Compute path.
    #[test]
    fn cache_root_computes_and_materializes() {
        let mut arena = ArenaBuilder::new();
        let sa = arena.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerMemory { column: 0 },
        });
        let sb = arena.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerMemory { column: 1 },
        });
        let a = arena.source_expr(sa);
        let b = arena.source_expr(sb);
        let add = arena.add(vec![a, b]);

        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![Root::Output { expr: add, sink: SinkId(0) }],
            sinks: vec![SinkInfo {
                kind: SinkKind::Cache { layer: 3, offset: 5 },
                field: FieldKind::Base,
            }],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(), // no origin → cache root → Compute
            resolutions: BTreeMap::new(),
        };

        let compiled =
            compile_layer(&layer, &artifact_layer(7), &BTreeMap::new(), &HashMap::new(), 16)
                .unwrap();

        // Last instruction materializes the cache via GlobalMaterialize.
        let last = compiled.program.instrs.last().unwrap();
        let (slot, col) = match last {
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                dst: Some(DstLine::GlobalMaterialize { slot, col }),
                ..
            } => (*slot, *col),
            other => panic!("expected cache materialize MOV, got {:?}", other),
        };
        assert_eq!(col, 5);
        assert_eq!(
            compiled.ctx.backings.backing(slot),
            Some(&BackingKey::CacheOutput { layer: 3 })
        );
        // cache_loc recorded, and a Global RootOutput.
        assert_eq!(compiled.ctx.cache_loc.get(&RootId(0)), Some(&(slot, 5)));
        assert_eq!(
            compiled.root_outputs,
            vec![(RootId(0), RootOutput::Cell(OutputCell::Global { slot, col: 5 }))]
        );
        assert!(compiled.skipped.is_empty());
    }

    // #6: a passthrough Compute root whose body lowers to a single `MOV AccFromSrc`
    // (here a bare source read into a cache backing) fuses its init+materialize
    // into ONE `MOV DstFromSrc dst <- src`, dropping the accumulator round-trip.
    // (With empty `cached_relations` the root is Compute, not a `CopyAlias`.)
    #[test]
    fn passthrough_source_root_fuses_to_dst_from_src() {
        let mut arena = ArenaBuilder::new();
        let s = arena.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerMemory { column: 0 },
        });
        let a = arena.source_expr(s);
        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![Root::Output { expr: a, sink: SinkId(0) }],
            sinks: vec![SinkInfo {
                kind: SinkKind::Cache { layer: 3, offset: 5 },
                field: FieldKind::Base,
            }],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        };
        let compiled =
            compile_layer(&layer, &artifact_layer(7), &BTreeMap::new(), &HashMap::new(), 16)
                .unwrap();
        // Exactly ONE instruction — the fused direct move, not an AccFromSrc +
        // DstFromAcc pair.
        assert_eq!(
            compiled.program.instrs.len(),
            1,
            "passthrough root must compile to a single fused MOV, got {:?}",
            compiled.program.instrs
        );
        match &compiled.program.instrs[0] {
            Instr::Mov {
                dir: MovDir::DstFromSrc,
                dst: Some(DstLine::GlobalMaterialize { col, .. }),
                src: Some(_),
                ..
            } => assert_eq!(*col, 5),
            other => panic!("expected fused MOV DstFromSrc, got {:?}", other),
        }
    }

    // Task 3 fusion guard: a bare-source `Read` root that is ALSO reused elsewhere
    // (refcount ≥ 2 across roots → a source-residency candidate) must STILL fuse to a
    // single `MOV DstFromSrc GlobalMaterialize` at its sole-source root. Load-once'ing
    // there would split the one fused passthrough into load + AccFromSrc + DstFromAcc —
    // a BIT-EXACT regression the parity gate cannot catch. The `allow_source_load=false`
    // guard on the `compile_expr` top-level Source arm is what preserves the fusion;
    // the load fires at the OTHER (fold-operand) use instead.
    fn test_two_roots_one_bare_one_fold_share_read() -> DagLayer {
        let mut arena = ArenaBuilder::new();
        // Read(col9) — shared between the two roots (identical Reads dedup to one ExprId,
        // so it is used across BOTH Output trees → `is_source_resident`).
        let s9 = arena.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerMemory { column: 9 },
        });
        let r9 = arena.source_expr(s9);
        // A second column for the fold's other operand.
        let s2 = arena.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerMemory { column: 2 },
        });
        let r2 = arena.source_expr(s2);
        // Root B: a fold that USES read9 as an operand (load-once fires here).
        let fold = arena.add(vec![r9, r2]);
        DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![
                // Root A: bare-source passthrough whose expr IS read9 (sole expr).
                Root::Output { expr: r9, sink: SinkId(0) },
                // Root B: the fold sharing read9.
                Root::Output { expr: fold, sink: SinkId(1) },
            ],
            sinks: vec![
                SinkInfo { kind: SinkKind::Cache { layer: 3, offset: 5 }, field: FieldKind::Base },
                SinkInfo { kind: SinkKind::Inner { layer: 0, offset: 0 }, field: FieldKind::Base },
            ],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        }
    }

    #[test]
    fn reused_bare_source_root_still_fuses() {
        let layer = test_two_roots_one_bare_one_fold_share_read();
        let c = compile_layer(&layer, &artifact_layer(7), &BTreeMap::new(), &HashMap::new(), 1024)
            .unwrap();
        // The bare-source root's materialize must be a single fused DstFromSrc→GlobalMaterialize,
        // NOT load(DstFromSrc Smem) + AccFromSrc + DstFromAcc.
        let fused = c.program.instrs.iter().any(|i| {
            matches!(
                i,
                Instr::Mov {
                    dir: MovDir::DstFromSrc,
                    dst: Some(DstLine::GlobalMaterialize { .. }),
                    src: Some(OperandLine::Global { .. }),
                    ..
                }
            )
        });
        assert!(
            fused,
            "a reused bare-source passthrough root must still fuse (no load-once at the \
             sole-source root): {:#?}",
            c.program.instrs
        );
    }

    // A post-elision degenerate root is rejected: top expr is Mul([Constant{1}]),
    // which is structurally non-empty (1 child) so is_empty_reduction returns false,
    // but compile_expr emits zero instructions after eliding the Constant{1} factor.
    // The len_before guard must catch this and return DegenerateRoot.
    #[test]
    fn degenerate_post_elision_mul_one_root_rejected() {
        let mut arena = ArenaBuilder::new();
        let one_src = arena.intern_source(SourceKind::Constant { value: 1 });
        let one = arena.source_expr(one_src);
        let mul_one = arena.mul(vec![one]); // Mul([Constant{1}]) — non-empty structurally
        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![Root::Output { expr: mul_one, sink: SinkId(0) }],
            sinks: vec![SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset: 0 },
                field: FieldKind::Base,
            }],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        };
        let err = compile_layer(&layer, &artifact_layer(0), &BTreeMap::new(), &HashMap::new(), 16)
            .unwrap_err();
        assert_eq!(err, CompileError::DegenerateRoot(RootId(0)));
    }

    // A degenerate root (top expr is an empty Mul) is rejected.
    #[test]
    fn degenerate_empty_reduction_root_rejected() {
        let mut arena = ArenaBuilder::new();
        let empty = arena.mul(vec![]); // empty Mul = bare `1`
        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![Root::Output { expr: empty, sink: SinkId(0) }],
            sinks: vec![SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset: 0 },
                field: FieldKind::Base,
            }],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        };
        let err = compile_layer(&layer, &artifact_layer(0), &BTreeMap::new(), &HashMap::new(), 16)
            .unwrap_err();
        assert_eq!(err, CompileError::DegenerateRoot(RootId(0)));
    }

    // ── Task 10 Step 6: invariant goldens (real add_sub L0 fixture) ────────────────

    use std::path::PathBuf;
    use cs::gkr_compiler::dag_ir::{lower_dag, validate};
    use cs::gkr_compiler::GKRCircuitArtifact;
    use field::baby_bear::base::BabyBearField;
    use crate::fwd::validate::validate_compiled;

    fn load_fixture(name: &str) -> Option<GKRCircuitArtifact<BabyBearField>> {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits");
        let bytes = std::fs::read(dir.join(format!("{}.json", name))).ok()?;
        serde_json::from_slice(&bytes).ok()
    }

    // (6a) `root_outputs` are in RootId index order and identical to a recomputed-by-
    // RootId reference (S2 keeps index order — no reorder until S3). (6b) `ctx.specials`
    // holds exactly the DISTINCT reached descriptors (no per-use duplication). (6c)
    // `validate_compiled` passes — field transitions, ext alignment, budget all clean
    // over the residency-redirected program.
    #[test]
    fn add_sub_layer0_invariant_goldens() {
        let artifact = match load_fixture("add_sub_lui_auipc_mop_layout_gkr") {
            Some(a) => a,
            None => return,
        };
        let dag = lower_dag(&artifact).expect("lower_dag");
        validate(&dag).expect("validate dag");
        let cross = build_cross_layer_field_map(&dag);
        let compiled =
            compile_layer(&dag.layers[0], &artifact.layers[0], &artifact.scratch_space_mapping, &cross, 1024)
                .expect("compile_layer");

        // (6a) root_outputs sorted by RootId, matching a by-RootId reference.
        let ids: Vec<RootId> = compiled.root_outputs.iter().map(|(rid, _)| *rid).collect();
        let mut sorted = ids.clone();
        sorted.sort_by_key(|r| r.0);
        assert_eq!(ids, sorted, "root_outputs must stay in RootId index order (no reorder until S3)");
        // Recompute the by-RootId reference and assert identity.
        let mut reference: std::collections::BTreeMap<u32, RootOutput> = std::collections::BTreeMap::new();
        for (rid, out) in &compiled.root_outputs {
            assert!(reference.insert(rid.0, *out).is_none(), "duplicate RootId {} in root_outputs", rid.0);
        }
        let recomputed: Vec<(RootId, RootOutput)> =
            reference.into_iter().map(|(k, v)| (RootId(k), v)).collect();
        assert_eq!(compiled.root_outputs, recomputed, "root_outputs must equal the by-RootId reference");

        // (6b) specials hold exactly the distinct reached descriptors — no duplicates.
        let graph = analyze_layer(&dag.layers[0], &DagForwardContext::default());
        let distinct = graph.descriptors.keys.len();
        assert_eq!(
            compiled.ctx.specials.len(),
            distinct,
            "ctx.specials.len() {} must equal the distinct reached-descriptor count {}",
            compiled.ctx.specials.len(),
            distinct
        );
        // Every descriptor origin is distinct (no per-use duplication).
        let mut origins: std::collections::HashSet<ExprId> = std::collections::HashSet::new();
        for d in compiled.ctx.specials.iter() {
            assert!(origins.insert(d.origin_expr), "duplicate descriptor for origin {:?}", d.origin_expr);
        }

        // (6c) the residency-redirected program validates cleanly.
        validate_compiled(&compiled, &dag.layers[0]).expect("validate_compiled must pass");
    }

    // ── A resident compound survives ACROSS two roots while a transient nested child
    // lowered between them is freed (one shared allocator: residents and temps share
    // the cell space, so a temp never lands on a live resident's cell). ─────────────
    //
    //   root0 = Add(memA, memB)            — cache root (no origin), CANDIDATE (later
    //                                        Prior use) → admitted resident in cell c.
    //   root1 = Mul(Add(memC, memD), memE) — its Add child lowers into a TRANSIENT cell
    //                                        (freed after root1's fold).
    //   root2 = Mul(Prior(root0), memF)    — reads root0 from its RESIDENT cell c.
    //
    // Asserts: (i) root0 emits a resident store `MOV DstFromAcc Smem{c}`; (ii) root2
    // reads `OperandLine::Smem{c}` (resident survived + is read by root2, NOT re-read
    // from DRAM); (iii) the transient cell from root1 does not collide with the
    // resident cell c (resident map and transient allocator are disjoint — codex Mod3).
    #[test]
    fn resident_compound_survives_across_roots_transient_freed() {
        use crate::fwd::isa::OperandLine;
        let mut arena = ArenaBuilder::new();
        let mem = |arena: &mut ArenaBuilder, col: usize| {
            let s = arena.intern_source(SourceKind::Read {
                place: ReadPlace::BaseLayerMemory { column: col },
            });
            arena.source_expr(s)
        };
        let a = mem(&mut arena, 0);
        let b = mem(&mut arena, 1);
        let add_ab = arena.add(vec![a, b]); // root0 expr (cache root)

        let c = mem(&mut arena, 2);
        let d = mem(&mut arena, 3);
        let add_cd = arena.add(vec![c, d]); // transient compound child of root1
        let e = mem(&mut arena, 4);
        let mul_cde = arena.mul(vec![add_cd, e]); // root1 expr (Mul of a compound + source)

        let prior0 = arena.intern_source(SourceKind::Prior { id: RootId(0) });
        let prior0_expr = arena.source_expr(prior0);
        let f = mem(&mut arena, 5);
        let mul_prior_f = arena.mul(vec![prior0_expr, f]); // root2 expr (reads root0)

        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![
                Root::Output { expr: add_ab, sink: SinkId(0) },     // cache root
                Root::Output { expr: mul_cde, sink: SinkId(1) },    // normal output
                Root::Output { expr: mul_prior_f, sink: SinkId(2) },// reads root0
            ],
            sinks: vec![
                SinkInfo { kind: SinkKind::Cache { layer: 3, offset: 0 }, field: FieldKind::Base },
                SinkInfo { kind: SinkKind::Inner { layer: 3, offset: 0 }, field: FieldKind::Base },
                SinkInfo { kind: SinkKind::Inner { layer: 3, offset: 1 }, field: FieldKind::Base },
            ],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(), // root0 has no origin → cache root
            resolutions: BTreeMap::new(),
        };

        let compiled =
            compile_layer(&layer, &artifact_layer(3), &BTreeMap::new(), &HashMap::new(), 1024)
                .expect("compile_layer");

        // (i) root0 emitted a resident store MOV DstFromAcc Smem{c}; capture cell c.
        let resident_cell = compiled.program.instrs.iter().find_map(|i| match i {
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                dst: Some(DstLine::Smem { cell }),
                ..
            } => Some(*cell),
            _ => None,
        });
        let resident_cell = resident_cell.expect(
            "root0 (a reused cache root) must be kept resident via MOV DstFromAcc Smem",
        );

        // (ii) some instruction reads the resident cell as an Smem operand (root2's
        // Prior read), proving the resident survived and was read — not re-read DRAM.
        let reads_resident = compiled.program.instrs.iter().any(|i| match i {
            Instr::Mul { operands, .. } | Instr::Add { operands, .. } => {
                operands.iter().any(|o| matches!(o, OperandLine::Smem { cell } if *cell == resident_cell))
            }
            Instr::Mov { src: Some(OperandLine::Smem { cell }), .. } => *cell == resident_cell,
            Instr::Fma { pairs, .. } => pairs.iter().any(|(l, r)| {
                matches!(l, OperandLine::Smem { cell } if *cell == resident_cell)
                    || matches!(r, OperandLine::Smem { cell } if *cell == resident_cell)
            }),
            _ => false,
        });
        assert!(
            reads_resident,
            "root2's Prior read must consume the RESIDENT cell {resident_cell} (resident survived across roots), program: {:#?}",
            compiled.program.instrs
        );

        // (iii) The transient `add_cd` cell in root1 must be evicted to a DIFFERENT cell
        // than the resident cell. With ONE shared allocator, `alloc_temp` only hands out
        // cells not currently occupied — a live resident occupies its cell, so a transient
        // can never collide with it (the b5069ea0 collision is impossible by construction).
        // Every transient evict store `MOV DstFromAcc Smem{t}` other than root0's resident
        // store must have t != resident_cell.
        let transient_evicts: Vec<u16> = compiled
            .program
            .instrs
            .iter()
            .filter_map(|i| match i {
                Instr::Mov { dir: MovDir::DstFromAcc, dst: Some(DstLine::Smem { cell }), .. } => Some(*cell),
                _ => None,
            })
            .collect();
        // There must be >1 Smem evict (the resident store + root1's transient evict),
        // and the transient one(s) must not reuse the resident cell.
        let transient_collision = transient_evicts
            .iter()
            .filter(|&&t| t == resident_cell)
            .count();
        assert_eq!(
            transient_collision, 1,
            "exactly ONE store may target the resident cell (root0's resident store); a transient evict reusing it would clobber the resident: evicts={transient_evicts:?}, resident={resident_cell}",
        );

        // We assert no Global re-read of root0 leaked in:
        let root0_backing = compiled.ctx.cache_loc.get(&RootId(0)).copied();
        if let Some((slot, col)) = root0_backing {
            let reread_global = compiled.program.instrs.iter().any(|i| match i {
                Instr::Mul { operands, .. } | Instr::Add { operands, .. } => operands
                    .iter()
                    .any(|o| matches!(o, OperandLine::Global { slot: s, col: cc } if *s == slot && *cc == col)),
                Instr::Mov { src: Some(OperandLine::Global { slot: s, col: cc }), .. } => *s == slot && *cc == col,
                _ => false,
            });
            assert!(
                !reread_global,
                "root0's cache backing ({slot},{col}) must NOT be re-read — the resident cell replaces it",
            );
        }
        // The compiled layer validates cleanly with both resident + transient cells.
        validate_compiled(&compiled, &layer).expect("validate_compiled must pass");
    }

    // ── Task 1: width-weighted dram_traffic counter ───────────────────────────
    //
    // Build a single Add root with three operands:
    //   - an Ext cross-layer Read{LayerOutput{1,0}}  → width 4, counts in dram_traffic
    //   - a Base Read{BaseLayerWitness{0}}           → width 1, counts in dram_traffic
    //   - a VirtualSetup{RangeCheck16Bits}           → resolver-computed, 0 traffic
    //
    // Expected: dram_reads = 3 (all three are Global operands, unchanged);
    //           dram_traffic = 4 + 1 + 0 = 5.
    fn single_root_layer_ext_base_vsetup() -> (DagLayer, GKRLayerDescription) {
        use cs::gkr_compiler::dag_ir::VirtualSetupKind;
        let mut arena = ArenaBuilder::new();
        // Ext cross-layer read (field supplied via cross map below).
        let s_ext = arena.intern_source(SourceKind::Read {
            place: ReadPlace::LayerOutput { layer: 1, offset: 0 },
        });
        // Base witness read.
        let s_base = arena.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerWitness { column: 0 },
        });
        // VirtualSetup source — resolver-computed, 0 DRAM traffic.
        let s_vs = arena.intern_source(SourceKind::VirtualSetup {
            kind: VirtualSetupKind::RangeCheck16Bits,
        });
        let e_ext  = arena.source_expr(s_ext);
        let e_base = arena.source_expr(s_base);
        let e_vs   = arena.source_expr(s_vs);
        // Add all three — the Ext operand makes the result Ext.
        let add = arena.add(vec![e_ext, e_base, e_vs]);
        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![Root::Output { expr: add, sink: SinkId(0) }],
            sinks: vec![SinkInfo {
                kind: SinkKind::Inner { layer: 2, offset: 0 },
                field: FieldKind::Ext, // Ext sink to accept the mixed (→ Ext) add
            }],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        };
        (layer, artifact_layer(2))
    }

    #[test]
    fn dram_traffic_weights_ext_and_zeroes_virtual_setup() {
        let (layer, art_layer) = single_root_layer_ext_base_vsetup();
        let mut cross: HashMap<ReadPlace, FieldKind> = HashMap::new();
        cross.insert(ReadPlace::LayerOutput { layer: 1, offset: 0 }, FieldKind::Ext);
        let compiled = compile_layer(&layer, &art_layer, &BTreeMap::new(), &cross, 1024).unwrap();
        assert_eq!(compiled.stats.dram_reads, 3, "per-operand count unchanged (incl. vsetup)");
        assert_eq!(compiled.stats.dram_traffic, 5, "4 (ext read) + 1 (base read) + 0 (vsetup)");
    }

    // Two Output roots both reference the same Read source; build_ref_string must
    // emit a Use(source_expr) for each reference after Task 2 extends
    // collect_prior_uses with the Read-source arm.
    //
    // Before Task 2: use_count == 0 (only Prior sources emit Use events).
    // After Task 2:  use_count >= 2 (one per root that references the source).
    #[test]
    fn ref_string_includes_source_resident_uses() {
        let mut arena = ArenaBuilder::new();
        // One Read source referenced by both roots (≥2 uses → is_source_resident).
        let src = arena.intern_source(SourceKind::Read {
            place: ReadPlace::BaseLayerMemory { column: 0 },
        });
        let read_expr = arena.source_expr(src);

        // Give root0 a non-trivial expr so it is a cache root candidate:
        // root0 = Add(read_expr, read_expr)  → two refs to read_expr here.
        let add0 = arena.add(vec![read_expr, read_expr]);

        // root1 = Add(read_expr, read_expr)  → two more refs (same ExprId).
        let add1 = arena.add(vec![read_expr, read_expr]);

        let layer = DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots: vec![
                Root::Output { expr: add0, sink: SinkId(0) },
                Root::Output { expr: add1, sink: SinkId(1) },
            ],
            sinks: vec![
                SinkInfo {
                    kind: SinkKind::Cache { layer: 0, offset: 0 },
                    field: FieldKind::Base,
                },
                SinkInfo {
                    kind: SinkKind::Inner { layer: 0, offset: 0 },
                    field: FieldKind::Base,
                },
            ],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        };

        let ctx = DagForwardContext::default();
        let graph = crate::fwd::compile::analyze::analyze_layer(&layer, &ctx);
        assert!(
            graph.info[&read_expr].is_source_resident,
            "precondition: source is a residency candidate (used ≥2×)"
        );

        let cache_root_expr = cache_root_expr_map(&layer);
        let refs = build_ref_string(&layer, &cache_root_expr, &graph);
        let use_count = refs
            .events
            .iter()
            .filter(|e| matches!(e, RefEvent::Use(v) if *v == read_expr))
            .count();
        assert!(
            use_count >= 2,
            "build_ref_string must emit a Use per source-resident read use; got {use_count}"
        );
    }
}
