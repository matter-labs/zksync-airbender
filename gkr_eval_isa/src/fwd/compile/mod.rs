pub mod analyze;
pub mod arith;
pub mod decisions;
mod lower;
pub mod negate;
mod optimize;
mod place;
pub mod resolution;
pub mod schedule;

pub use self::arith::build_cross_layer_field_map;
pub use self::decisions::SiteDecisions;
use self::lower::lower_layer_virtual;
use self::place::{plan_placement, PlacementInput, RelocStep, ResidencyStep, ValueId, VInstrKind, VirtualOp};
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
    CircuitSchedule, DagCircuit, DagLayer, ExprId, FieldKind, LayerSchedule, ReadPlace, RootId,
    SinkInfo, SinkKind,
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
/// `specials` is the layer's special-source table, used to split a `Special` gather by
/// strategy: a `VirtualSetup` gather is resolver-computed (0 traffic, not a `special_read`,
/// like a `SpecialLit`); the peek strategies are real resolved-fold gathers.
fn tally_operand(
    op: &OperandLine,
    field: OperandField,
    specials: &super::source::SpecialTable,
    stats: &mut CompileStats,
) {
    match classify_operand(op) {
        OperandClass::Dram => {
            stats.dram_reads += 1; // per-operand diagnostic, unchanged
            // Every `Global` operand is now a real DRAM read: VirtualSetup no longer has a
            // Global backing (it lowers to a computed `Special`), so no exemption is needed.
            stats.dram_traffic += if field == OperandField::Ext { 4 } else { 1 };
        }
        OperandClass::Ldc => stats.ldc_reads += 1,
        OperandClass::SpecialLit => {} // inline literal — near-free, not counted
        OperandClass::SpecialGather => {
            if let OperandLine::Special { desc } = op {
                match specials.get(*desc).map(|d| &d.strategy) {
                    // VirtualSetup is resolver-computed — 0 traffic, like a SpecialLit.
                    Some(super::source::SpecialStrategy::VirtualSetup { .. }) => {}
                    _ => stats.special_reads += 1,
                }
            }
        }
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

/// Test-facing view of one Phase-1 lowered virtual instruction (Task 1 synthetic tests
/// inspect emission SHAPE — cache-produce `Mul`→cell vs `Fma` fuse vs `Value` read —
/// without depending on the crate-private `VInstr`/`VirtualOp` types).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoweredKind {
    Add,
    Mul,
    Fma,
    Mov,
}

/// A single lowered virtual instruction, projected for test inspection: its step index,
/// opcode kind, the `ValueId` it defines (a `Mov`→cell evict, incl. cache-produce), and
/// the `Value(v)` (smem-cell) operands it reads.
#[derive(Clone, Debug)]
pub struct LoweredInstr {
    pub step: usize,
    pub kind: LoweredKind,
    pub defines: Option<ExprId>,
    pub value_reads: Vec<ExprId>,
}

/// Lower one layer's `VInstr` stream under `decisions`/`budget` and project it to
/// `LoweredInstr`s. Test-only seam: runs Stage-3 Phase 1 (`lower_layer_virtual`) and
/// exposes the emission shape so synthetic tests can assert the cache-produce/fuse/resident
/// partition. `decisions: None` is the uncached (per-step recompute) baseline; `Some` runs
/// the sub-project-2 residency machine at `budget`.
pub fn lower_layer_stream(
    layer: &DagLayer,
    artifact_layer: &GKRLayerDescription,
    scratch_mapping: &BTreeMap<GKRAddress, usize>,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
    schedule: &LayerSchedule,
    budget: usize,
    decisions: Option<&SiteDecisions>,
) -> Result<Vec<LoweredInstr>, CompileError> {
    let mut ctx = DagForwardContext::default();
    ctx.actions = build_forward_actions(layer, artifact_layer, scratch_mapping)?;
    ctx.cross_layer_fields = cross_layer_fields.clone();
    let (vinstrs, step_of, _vouts, _rr) =
        lower_layer_virtual(layer, schedule, &mut ctx, artifact_layer.layer, decisions, budget)?;
    Ok(vinstrs
        .iter()
        .zip(step_of)
        .map(|(vi, step)| {
            let pv = vi.to_place();
            let kind = match pv.op {
                VInstrKind::Add => LoweredKind::Add,
                VInstrKind::Mul => LoweredKind::Mul,
                VInstrKind::Fma => LoweredKind::Fma,
                VInstrKind::Mov => LoweredKind::Mov,
            };
            let value_reads = pv
                .reads
                .iter()
                .filter_map(|r| match r {
                    VirtualOp::Value(v) => Some(*v),
                    _ => None,
                })
                .collect();
            LoweredInstr { step, kind, defines: pv.defines, value_reads }
        })
        .collect())
}

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
///
/// `decisions: None` is the uncached (per-step recompute) baseline;
/// `Some` runs the sub-project-2 residency machine at `budget`. The
/// policy is threaded into Phase 1 (`lower_layer_virtual`); everything downstream
/// (placement, materialize) is decisions-agnostic.
pub fn compile_layer(
    layer: &DagLayer,
    artifact_layer: &GKRLayerDescription,
    scratch_mapping: &BTreeMap<GKRAddress, usize>,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
    schedule: &LayerSchedule,
    budget: usize,
    decisions: Option<&SiteDecisions>,
) -> Result<CompiledLayer, CompileError> {
    let mut ctx = DagForwardContext::default();
    ctx.actions = build_forward_actions(layer, artifact_layer, scratch_mapping)?;
    ctx.cross_layer_fields = cross_layer_fields.clone();

    // Phase 1 — lower to a rich virtual-instruction stream.
    let (vinstrs, step_of, vouts, resident_realized) =
        lower_layer_virtual(layer, schedule, &mut ctx, artifact_layer.layer, decisions, budget)?;

    // Phase 1.5 — value-preserving peephole (F1/F4/F2/F5). `resident_realized` above stays
    // the lowering-time admission diagnostic (pre-optimization; consumed by decisions_policy).
    let (vinstrs, step_of) = self::optimize::optimize_vinstrs(vinstrs, step_of);

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
    // realizes residency lazily as cones compute shared values), so we hand it
    // residency-free `ResidencyStep`s (place.rs's local, schema-agnostic type — schema
    // v2 (Task 4) has no persisted per-step residency at all to inject phantom cells
    // from). The realized residency is recorded separately in `resident_realized` (H5).
    // Step boundaries derive from `schedule.atom_order()` (one step per ordered atom root).
    let free_steps: Vec<ResidencyStep> =
        (0..schedule.atom_order().len()).map(|_| ResidencyStep::default()).collect();
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
                    tally_operand(op, *field, &ctx.specials, &mut stats);
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
                    tally_operand(op, *field, &ctx.specials, &mut stats);
                }
            }
            Instr::Mul { field, operands, .. } => {
                stats.op_counts[OP_MUL] += 1;
                for op in operands {
                    tally_operand(op, *field, &ctx.specials, &mut stats);
                }
            }
            Instr::Fma { field_lhs, field_rhs, pairs, .. } => {
                stats.op_counts[OP_FMA] += 1;
                for (l, r) in pairs {
                    tally_operand(l, *field_lhs, &ctx.specials, &mut stats);
                    tally_operand(r, *field_rhs, &ctx.specials, &mut stats);
                }
            }
        }
    }
    for (_, out) in &root_outputs {
        if let RootOutput::Alias(op) = out {
            tally_operand(op, OperandField::Base, &ctx.specials, &mut stats);
        }
    }
    stats.special_gathers = ctx
        .specials
        .iter()
        .filter(|d| !matches!(d.strategy, super::source::SpecialStrategy::VirtualSetup { .. }))
        .count();
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

/// Shared skip predicate (ground truth for "does this layer need compiling"):
/// a layer is trivially skippable iff its schedule's `units` are empty (⟺ empty
/// atom order) AND no root in the layer carries a `materialize` sink.
/// `units.is_empty()` alone is NOT sufficient — a layer can have zero atom roots
/// (empty `units`, since `schedule_search::structure::relation_units` only counts
/// `materialize.is_some() && claim.is_some()` roots) while still carrying a
/// materialize-only root (e.g. a `Cache` root with no `claim`), which still
/// needs a real `compile_layer` pass to emit its materialization. Both
/// `compile_circuit` and the on-demand schedule producer
/// (`schedule_search::producer::produce_circuit_schedule`) call this so the
/// two skip decisions cannot drift (Task 6 review finding).
pub fn layer_needs_compile(order_is_empty: bool, layer: &DagLayer) -> bool {
    !(order_is_empty && layer.roots.iter().all(|r| r.materialize.is_none()))
}

/// Load one committed `*_schedule_b16_gkr.json`. Parse-only — structural
/// validation against the circuit happens in `compile_circuit`
/// (`validate_circuit_schedule`), so a caller cannot forget it. A missing or
/// unparsable file is a hard error: there is NO produce-on-missing fallback
/// (on-demand production is an explicit caller act via
/// `schedule_search::producer::produce_circuit_schedule`).
pub fn load_committed_schedule(path: &std::path::Path) -> Result<CircuitSchedule, CompileError> {
    let bytes = std::fs::read(path).map_err(|e| {
        CompileError::InvalidSchedule(format!("read {}: {e}", path.display()))
    })?;
    serde_json::from_slice(&bytes).map_err(|e| {
        CompileError::InvalidSchedule(format!("parse {}: {e}", path.display()))
    })
}

/// Compile a whole circuit from its committed `CircuitSchedule` (OP-3): the single
/// production forward-program compile path.
///
/// Validates `schedule` against `dag` first (`validate_circuit_schedule` — units match
/// the canonical relation-unit decomposition, the stored site-key set matches the structural
/// domain exactly, priorities are finite, `floor <= predicted_traffic`); a stale or
/// malformed schedule is rejected with `CompileError::InvalidSchedule` before any layer
/// is touched. Then builds the whole-circuit cross-layer field map once and compiles
/// each layer from its `LayerSchedule`'s stored `sites`, decoded into a `SiteDecisions`
/// and run through the sub-project-2 residency machine at the schedule's `budget`. A
/// layer with no atom roots and no materialize-bearing roots yields an empty
/// `CompiledLayer`; otherwise `compile_layer`.
pub fn compile_circuit(
    dag: &DagCircuit,
    schedule: &CircuitSchedule,
    artifact: &GKRCircuitArtifact<BabyBearField>,
) -> Result<CompiledCircuit, CompileError> {
    cs::gkr_compiler::dag_ir::validate_circuit_schedule(dag, schedule)
        .map_err(CompileError::InvalidSchedule)?;
    let cross = build_cross_layer_field_map(dag);
    let mut layers = Vec::with_capacity(dag.layers.len());
    for (li, layer) in dag.layers.iter().enumerate() {
        let ls = &schedule.layers[li];
        if !layer_needs_compile(ls.units.is_empty(), layer) {
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
            let decisions = SiteDecisions::new(ls.sites.iter().copied());
            layers.push(compile_layer(
                layer,
                &artifact.layers[li],
                &artifact.scratch_space_mapping,
                &cross,
                ls,
                schedule.budget,
                Some(&decisions),
            )?);
        }
    }
    Ok(CompiledCircuit { circuit: schedule.circuit.clone(), budget: schedule.budget, layers })
}

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{BatchingOrder, Expr, Root, SourceId};
    use std::collections::BTreeMap;

    /// Review finding (Task 6): a layer with a materialize-only root (a `Cache`
    /// root with no `claim`) and no atom roots has an empty `relation_units` —
    /// so its schedule's `units` would be `[]` — but `layer_needs_compile` must
    /// still say "needs compile" so `compile_circuit` runs `compile_layer`
    /// instead of skipping, and so the producer (which uses
    /// `relation_units(layer).is_empty()` as its own `order_is_empty` proxy)
    /// stays consistent with `compile_circuit`'s ground-truth skip decision.
    #[test]
    fn layer_needs_compile_true_for_materialize_only_root_with_empty_order() {
        let sink = SinkInfo { kind: SinkKind::Cache { layer: 0, offset: 0 }, field: FieldKind::Ext };
        let layer = DagLayer {
            sources: vec![],
            exprs: vec![Expr::Source(SourceId(0))],
            roots: vec![Root { expr: ExprId(7), materialize: Some(sink), claim: None }],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        };

        // Producer's proxy for "would this layer's order be empty": no atom
        // (materialize+claim) roots.
        let order_would_be_empty = crate::schedule_search::structure::relation_units(&layer).is_empty();
        assert!(order_would_be_empty, "materialize-only root has no claim, so it is not an atom root");

        // Ground truth: `compile_circuit` must NOT skip this layer.
        assert!(
            layer_needs_compile(order_would_be_empty, &layer),
            "a materialize-bearing root must force compile_layer even with an empty order"
        );
    }

    /// Companion case: a layer with genuinely nothing (no roots at all) must
    /// still be skippable — `layer_needs_compile` isn't unconditionally `true`.
    #[test]
    fn layer_needs_compile_false_for_empty_layer() {
        let layer = DagLayer {
            sources: vec![],
            exprs: vec![],
            roots: vec![],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        };
        let order_would_be_empty =
            crate::schedule_search::structure::relation_units(&layer).is_empty();
        assert!(order_would_be_empty);
        assert!(!layer_needs_compile(order_would_be_empty, &layer));
    }
}
