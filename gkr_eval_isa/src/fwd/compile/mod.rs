pub mod analyze;
pub mod arith;
mod lower;
pub mod negate;
mod place;
pub mod resolution;
pub mod schedule;
mod schedule_residency;

pub use self::arith::build_cross_layer_field_map;
use self::lower::lower_layer_virtual;
use self::place::{plan_placement, PlacementInput, RelocStep, ValueId, VirtualOp};
use self::schedule_residency::build_materialize_map;
use super::binding::BackingKey;
use super::context::{
    build_forward_actions, CompileTrace, CompiledLayer, DagForwardContext, ForwardAction,
    OutputCell, RootOutput,
};
use super::stats::{CompileStats, OP_ADD, OP_FMA, OP_MOV, OP_MUL};
use super::error::CompileError;
use super::isa::{DstLine, Instr, LdcSub, MovDir, OperandField, OperandLine, Program};
use self::lower::{VDst, VInstr, VirtualRootOutput};
use cs::gkr_compiler::dag_ir::{
    CircuitSchedule, DagCircuit, DagLayer, Expr, ExprId, FieldKind, LayerSchedule, ReadPlace, Root,
    RootId, SinkInfo, SinkKind,
};
use cs::gkr_compiler::{GKRCircuitArtifact, GKRLayerDescription};
use cs::definitions::GKRAddress;
use field::baby_bear::base::BabyBearField;
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

/// Map a `GKRAddress` copy-source to the `ReadPlace` its materialized backing reads
/// from — mirrors cs's `dag_ir::lower::map_address` for the read-addressable variants.
///
/// A `CopyAlias` root copies its relation's `src_addr` (a materialized GKR address) to
/// `dst_addr`. Its operand is the BACKING of `src_addr`, not a re-lowering of `root.expr`:
/// under the shared-`ExprId` model a `Read{Cached/Inner}` whose value has an in-layer
/// materializer is aliased to that producer's (possibly COMPOUND) expr, so lowering
/// `root.expr` via `source_to_operand` would hit a non-source compound and fail. The
/// producer root already materialized `src_addr`'s value into this backing, so reading it
/// as a `Global` operand is value-identical to (and the structural equivalent of) the
/// pre-shared-`ExprId` `Read{src_addr}` source the alias used to carry.
fn copy_src_read_place(addr: GKRAddress) -> Option<ReadPlace> {
    match addr {
        GKRAddress::BaseLayerWitness(column) => Some(ReadPlace::BaseLayerWitness { column }),
        GKRAddress::BaseLayerMemory(column) => Some(ReadPlace::BaseLayerMemory { column }),
        GKRAddress::Setup(column) => Some(ReadPlace::Setup { column }),
        GKRAddress::ScratchSpace(slot) => Some(ReadPlace::Scratch { slot }),
        GKRAddress::InnerLayer { layer, offset } => Some(ReadPlace::LayerOutput { layer, offset }),
        GKRAddress::Cached { layer, offset } => Some(ReadPlace::CacheOutput { layer, offset }),
        // A VirtualSetup copy source is resolver-computed, not a backing read; no such
        // CopyAlias source exists in the corpus. Signal "not a plain backing read".
        GKRAddress::VirtualSetup(_) => None,
    }
}

fn operand_field_of(sink: &SinkInfo) -> OperandField {
    match sink.field {
        cs::gkr_compiler::dag_ir::FieldKind::Base => OperandField::Base,
        cs::gkr_compiler::dag_ir::FieldKind::Ext => OperandField::Ext,
    }
}

// ─────────────────────────────────────────────────────────────────────────────────
// Stage-3 schedule-driven compile path. `lower.rs` holds the value/admit model.
// ─────────────────────────────────────────────────────────────────────────────────

/// A whole circuit's schedule-driven forward program (OP-3).
#[derive(Clone, Debug)]
pub struct CompiledCircuit {
    pub circuit: String,
    pub budget: usize,
    pub layers: Vec<CompiledLayer>,
}

/// Compile one layer from its committed `LayerSchedule` (Stage-3 3-phase pipeline).
///
/// Phase 1 lowers to a rich `VInstr` stream with symbolic operands (`lower_layer_virtual`).
/// Phase 2 projects onto `place::VirtualInstr` and runs the Task-1 lifetime-overlap
/// allocator. Phase 3 materializes the rich stream to ISA `Instr` using the allocator's
/// `cell_of` map, interleaving Base-relocation compaction moves.
///
/// This is the single forward-program compile path (the old residency-coupled
/// `compile_layer` was deleted in the T3b flip).
pub fn compile_layer(
    layer: &DagLayer,
    artifact_layer: &GKRLayerDescription,
    scratch_mapping: &BTreeMap<GKRAddress, usize>,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
    schedule: &LayerSchedule,
    budget: usize,
) -> Result<CompiledLayer, CompileError> {
    let mut ctx = DagForwardContext::default();
    ctx.actions = build_forward_actions(layer, artifact_layer, scratch_mapping)?;
    ctx.cross_layer_fields = cross_layer_fields.clone();

    // Phase 1 — lower to a rich virtual-instruction stream.
    let mat = build_materialize_map(layer);
    let (vinstrs, step_of, vouts, resident_realized) =
        lower_layer_virtual(layer, schedule, &mut ctx, &mat, artifact_layer.layer)?;

    // Per-ValueId width: every defined value's own field. All values placement touches
    // are defined (via a `defines` instr) or read as `Value` (hence defined earlier), so
    // the `defines` scan is exhaustive for `plan_placement`'s `width_of`.
    let mut widths: HashMap<ValueId, OperandField> = HashMap::new();
    for vi in &vinstrs {
        if let Some(v) = vi.defines() {
            widths.insert(v, vi.field());
        }
    }

    // Phase 2 — project + run the lifetime-overlap allocator. Placement liveness is
    // driven by the REALIZED def/use of the virtual stream (`lower_layer_virtual`
    // realizes the schedule's residency lazily as cones compute shared values), so we
    // hand it residency-free `StepPlan`s: the schedule's `resident_*` SETS would inject
    // phantom cells for values realized elsewhere in the cone and mis-report lifetimes.
    // The realized residency is recorded separately in `resident_realized` (H5). Exact
    // per-event residency alignment to the schedule sets is Task-5 work.
    let free_steps: Vec<cs::gkr_compiler::dag_ir::StepPlan> = schedule
        .steps
        .iter()
        .map(|_| cs::gkr_compiler::dag_ir::StepPlan {
            resident_before: vec![],
            events: vec![],
            resident_after: vec![],
        })
        .collect();
    let place_instrs: Vec<self::place::VirtualInstr> = vinstrs.iter().map(|vi| vi.to_place()).collect();
    let placement = plan_placement(&PlacementInput {
        instrs: &place_instrs,
        steps: &free_steps,
        step_of_instr: &step_of,
        widths: &widths,
        budget,
    })?;

    // Phase 3 — materialize the rich stream to ISA instructions.
    let mut moves_at: HashMap<usize, Vec<RelocStep>> = HashMap::new();
    for (i, r) in &placement.moves {
        moves_at.entry(*i).or_default().push(*r);
    }
    let mut program = Program::default();
    for (i, vi) in vinstrs.iter().enumerate() {
        if let Some(ms) = moves_at.get(&i) {
            for r in ms {
                program.instrs.push(Instr::Mov {
                    dir: MovDir::DstFromSrc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: r.to }),
                    src: Some(OperandLine::Smem { cell: r.from }),
                });
            }
        }
        program.instrs.push(materialize_vinstr(vi, i, &placement.cell_of)?);
    }

    // Root outputs from the virtual outputs.
    let root_outputs: Vec<(RootId, RootOutput)> = vouts
        .into_iter()
        .map(|(rid, vo)| {
            let out = match vo {
                VirtualRootOutput::Global { slot, col } => {
                    RootOutput::Cell(OutputCell::Global { slot, col })
                }
                VirtualRootOutput::Alias(op) => RootOutput::Alias(op),
                VirtualRootOutput::Cell(v) => {
                    // Not emitted in T3a; resolve to its last recorded cell if present.
                    let cell = placement
                        .cell_of
                        .iter()
                        .filter(|((_, val), _)| *val == v)
                        .map(|((i, _), c)| (*i, *c))
                        .max_by_key(|(i, _)| *i)
                        .map(|(_, c)| c)
                        .unwrap_or(0);
                    RootOutput::Cell(OutputCell::Smem(cell))
                }
            };
            (rid, out)
        })
        .collect();

    let mut skipped: Vec<RootId> = ctx
        .actions
        .iter()
        .filter(|(_, a)| matches!(a, ForwardAction::SkipScratchPrefill))
        .map(|(rid, _)| *rid)
        .collect();
    skipped.sort_by_key(|r| r.0);

    // Stats — tally the concrete program (reuses the `compile_layer` accounting loop).
    let mut stats = CompileStats::default();
    stats.program_lanes = program.instrs.len();
    for instr in &program.instrs {
        match instr {
            Instr::Mov { dir, dst, src, field, .. } => {
                stats.op_counts[OP_MOV] += 1;
                if let Some(op) = src {
                    tally_operand(op, *field, &ctx.backings, &mut stats);
                }
                if matches!(dir, MovDir::DstFromAcc | MovDir::DstFromSrc)
                    && matches!(dst, Some(DstLine::Smem { .. }))
                {
                    stats.cell_stores += 1;
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
    for (_, out) in &root_outputs {
        if let RootOutput::Alias(op) = out {
            tally_operand(op, OperandField::Base, &ctx.backings, &mut stats);
        }
    }
    stats.special_gathers = ctx.specials.len();
    stats.max_live_cells = placement.max_live_cells;

    let mut trace = CompileTrace::default();
    trace.max_live_cells = placement.max_live_cells;

    Ok(CompiledLayer {
        program,
        ctx,
        root_outputs,
        skipped,
        trace,
        budget,
        stats,
        resident_realized,
    })
}

/// Materialize one rich `VInstr` to an ISA `Instr` using the allocator's `cell_of` map.
fn materialize_vinstr(
    vi: &VInstr,
    i: usize,
    cell_of: &HashMap<(usize, ValueId), u16>,
) -> Result<Instr, CompileError> {
    let op_of = |op: &VirtualOp| -> Result<OperandLine, CompileError> {
        match op {
            VirtualOp::Value(v) => {
                let cell = *cell_of.get(&(i, *v)).ok_or_else(|| {
                    CompileError::FieldMismatch(format!(
                        "no cell for value {} at instr {i}",
                        v.0
                    ))
                })?;
                Ok(OperandLine::Smem { cell })
            }
            VirtualOp::Global { slot, col } => Ok(OperandLine::Global { slot: *slot, col: *col }),
            VirtualOp::Ldc { sub, idx } => Ok(OperandLine::Ldc { sub: *sub, idx: *idx }),
            VirtualOp::Special { desc } => Ok(OperandLine::Special { desc: *desc }),
            VirtualOp::Acc => Err(CompileError::FieldMismatch("unexpected Acc operand".into())),
        }
    };
    Ok(match vi {
        VInstr::Add { field, sign, reads, .. } => Instr::Add {
            field: *field,
            sign: *sign,
            operands: reads.iter().map(&op_of).collect::<Result<_, _>>()?,
        },
        VInstr::Mul { field, reads, .. } => Instr::Mul {
            field: *field,
            operands: reads.iter().map(&op_of).collect::<Result<_, _>>()?,
        },
        VInstr::Fma { field_lhs, field_rhs, sign, pairs, .. } => {
            let mut out = Vec::with_capacity(pairs.len());
            for (l, r) in pairs {
                out.push((op_of(l)?, op_of(r)?));
            }
            Instr::Fma { field_lhs: *field_lhs, field_rhs: *field_rhs, sign: *sign, pairs: out }
        }
        VInstr::Mov { dir, field, dst, src, .. } => {
            let dst = match dst {
                None => None,
                Some(VDst::Cell(v)) => {
                    let cell = *cell_of.get(&(i, *v)).ok_or_else(|| {
                        CompileError::FieldMismatch(format!(
                            "no cell for defined value {} at instr {i}",
                            v.0
                        ))
                    })?;
                    Some(DstLine::Smem { cell })
                }
                Some(VDst::GlobalMaterialize { slot, col }) => {
                    Some(DstLine::GlobalMaterialize { slot: *slot, col: *col })
                }
            };
            let src = match src {
                None => None,
                Some(op) => Some(op_of(op)?),
            };
            Instr::Mov { dir: *dir, field: *field, dst, src }
        }
    })
}

/// Compile a whole circuit from its committed `CircuitSchedule` (OP-3).
///
/// Builds the whole-circuit cross-layer field map once, then compiles each layer from
/// its `LayerSchedule`. A layer with no atom roots and no materialize-bearing roots
/// yields an empty `CompiledLayer`; otherwise `compile_layer`.
pub fn compile_circuit(
    dag: &DagCircuit,
    schedule: &CircuitSchedule,
    artifact: &GKRCircuitArtifact<BabyBearField>,
) -> Result<CompiledCircuit, CompileError> {
    if schedule.layers.len() != dag.layers.len() {
        return Err(CompileError::FieldMismatch(format!(
            "schedule has {} layers, circuit has {}",
            schedule.layers.len(),
            dag.layers.len()
        )));
    }
    let cross = build_cross_layer_field_map(dag);
    let mut layers = Vec::with_capacity(dag.layers.len());
    for (li, layer) in dag.layers.iter().enumerate() {
        let ls = &schedule.layers[li];
        if ls.order.is_empty() && layer.roots.iter().all(|r| r.materialize.is_none()) {
            layers.push(CompiledLayer {
                program: Program::default(),
                ctx: DagForwardContext::default(),
                root_outputs: Vec::new(),
                skipped: Vec::new(),
                trace: CompileTrace::default(),
                budget: schedule.budget,
                stats: CompileStats::default(),
                resident_realized: Vec::new(),
            });
        } else {
            layers.push(compile_layer(
                layer,
                &artifact.layers[li],
                &artifact.scratch_space_mapping,
                &cross,
                ls,
                schedule.budget,
            )?);
        }
    }
    Ok(CompiledCircuit { circuit: schedule.circuit.clone(), budget: schedule.budget, layers })
}
