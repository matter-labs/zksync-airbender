pub mod analyze;
pub mod arith;
pub mod negate;
pub mod residency;
pub mod resolution;
pub mod schedule;

use self::arith::{compile_expr, source_to_operand};
pub use self::arith::build_cross_layer_field_map;
use self::schedule::CellAllocator;
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
fn tally_operand(op: &OperandLine, stats: &mut CompileStats) {
    match classify_operand(op) {
        OperandClass::Dram => stats.dram_reads += 1,
        OperandClass::Ldc => stats.ldc_reads += 1,
        OperandClass::SpecialLit => {} // inline literal — near-free, not counted
        OperandClass::SpecialGather => stats.special_reads += 1,
        OperandClass::Smem => stats.cell_reads += 1,
    }
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

    let mut program = Program::default();
    let mut trace = CompileTrace::default();
    let mut root_outputs: Vec<(RootId, RootOutput)> = Vec::new();
    let mut skipped: Vec<RootId> = Vec::new();

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

                // Lower the expr into the accumulator. A fresh `CellAllocator`
                // sized by the budget backs the general nested-subexpression
                // fallback (Task 13): each Compute root starts with an empty cell
                // file (no inter-root cell residency in SP1).
                let mut alloc = CellAllocator::new(budget);
                compile_expr(
                    layer,
                    expr,
                    &mut ctx,
                    &mut trace,
                    &mut program.instrs,
                    &mut alloc,
                    expected,
                )?;

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

                if !fused {
                    program.instrs.push(Instr::Mov {
                        dir: MovDir::DstFromAcc,
                        field: expected,
                        dst: Some(DstLine::GlobalMaterialize { slot, col }),
                        src: None,
                    });
                }

                // A cache root (no origin) records its location for same-layer Prior reads.
                if !layer.origins.contains_key(&rid) {
                    ctx.cache_loc.insert(rid, (slot, col));
                }
                root_outputs
                    .push((rid, RootOutput::Cell(OutputCell::Global { slot, col })));
            }
            ForwardAction::CopyAlias { .. } => {
                // §10: a view-alias produces NO kernel bytecode. Lower the root's
                // single source expr to an OperandLine for the action executor.
                let op = source_to_operand(layer, expr, &mut ctx, &mut trace)?;
                root_outputs.push((rid, RootOutput::Alias(op)));
            }
            ForwardAction::SkipScratchPrefill => {
                skipped.push(rid);
            }
        }
    }

    trace.max_live_cells = trace.max_live_cells.max(0);

    // Build per-layer stats from the compiled program and context (spec §11).
    let mut stats = CompileStats::default();
    stats.program_lanes = program.instrs.len();
    for instr in &program.instrs {
        match instr {
            Instr::Mov { dir, dst, src, .. } => {
                stats.op_counts[OP_MOV] += 1;
                // Tally the read operand (src), if any.
                if let Some(op) = src {
                    tally_operand(op, &mut stats);
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
            Instr::Add { operands, .. } => {
                stats.op_counts[OP_ADD] += 1;
                for op in operands {
                    tally_operand(op, &mut stats);
                }
            }
            Instr::Mul { operands, .. } => {
                stats.op_counts[OP_MUL] += 1;
                for op in operands {
                    tally_operand(op, &mut stats);
                }
            }
            Instr::Fma { pairs, .. } => {
                stats.op_counts[OP_FMA] += 1;
                for (l, r) in pairs {
                    tally_operand(l, &mut stats);
                    tally_operand(r, &mut stats);
                }
            }
        }
    }
    // Alias operands (CopyAlias roots, zero program lanes) still read their source.
    // Count Global aliases as dram_reads; other classes tallied the same way.
    for (_, out) in &root_outputs {
        if let RootOutput::Alias(op) = out {
            tally_operand(op, &mut stats);
        }
    }
    // special_gathers = number of resolved-fold Specials emitted (SpecialTable length).
    stats.special_gathers = ctx.specials.len();
    // max_live_cells from the compiler's high-water mark across all roots.
    stats.max_live_cells = trace.max_live_cells;
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
}
