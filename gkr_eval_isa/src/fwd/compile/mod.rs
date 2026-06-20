pub mod arith;
pub mod negate;
pub mod resolution;

use self::arith::{compile_expr, source_to_operand};
use super::binding::BackingKey;
use super::context::{
    build_forward_actions, CompileTrace, CompiledLayer, DagForwardContext, ForwardAction,
    OutputCell, RootOutput,
};
use super::error::CompileError;
use super::isa::{DstLine, Instr, MovDir, OperandField, Program};
use cs::gkr_compiler::dag_ir::{DagLayer, Expr, ExprId, Root, RootId, SinkInfo, SinkKind};
use cs::gkr_compiler::GKRLayerDescription;
use cs::definitions::GKRAddress;
use std::collections::BTreeMap;

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
    budget: usize,
) -> Result<CompiledLayer, CompileError> {
    let mut ctx = DagForwardContext::default();
    ctx.actions = build_forward_actions(layer, artifact_layer, scratch_mapping)?;

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

                // Lower the expr into the accumulator.
                compile_expr(layer, expr, &mut ctx, &mut trace, &mut program.instrs)?;

                // If lowering emitted no instructions, the root is degenerate
                // (post-elision empty): materializing now would push a stale
                // accumulator value. Reject it — §5 / §6 DegenerateRoot.
                if program.instrs.len() == len_before {
                    return Err(CompileError::DegenerateRoot(rid));
                }

                let sink = &layer.sinks[sink_id.0 as usize];
                let (key, col) = sink_to_backing(sink, artifact_layer.layer);
                let slot = ctx.backings.intern(key)?;

                program.instrs.push(Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: operand_field_of(sink),
                    dst: Some(DstLine::GlobalMaterialize { slot, col }),
                    src: None,
                });

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
    Ok(CompiledLayer {
        program,
        ctx,
        root_outputs,
        skipped,
        trace,
        budget,
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
            compile_layer(&layer, &artifact_layer(7), &BTreeMap::new(), 16).unwrap();

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
        let err = compile_layer(&layer, &artifact_layer(0), &BTreeMap::new(), 16).unwrap_err();
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
        let err = compile_layer(&layer, &artifact_layer(0), &BTreeMap::new(), 16).unwrap_err();
        assert_eq!(err, CompileError::DegenerateRoot(RootId(0)));
    }
}
