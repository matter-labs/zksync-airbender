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
use self::lower::{VDst, VInstr, VirtualRootOutput};
pub use self::place::MoveCtx;
use self::place::{
    PlacementInput, RelocStep, ResidencyStep, VInstrKind, ValueId, VirtualOp, plan_placement,
    plan_placement_with_peak,
};
use super::binding::{BackingKey, SourceMarkerMode, bind_final_sources};
use super::context::{
    CompileTrace, CompiledLayer, DagForwardContext, ForwardAction, OutputCell, RootOutput,
    build_forward_actions,
};
use super::error::CompileError;
use super::isa::{DstLine, Instr, LdcSub, MovDir, OperandField, OperandLine, Program};
use super::stats::{CompileStats, OP_ADD, OP_FMA, OP_MOV, OP_MUL};
use crate::bwd::batch::{BATCH_COEFFICIENT_MAX, BATCH_COEFFICIENT_ONE, pack_batch_dst};
use crate::schedule::{CircuitSchedule, LayerSchedule};
use gkr_eval_ir::{
    DagCircuit, DagLayer, ExprId, FieldKind, ReadPlace, RootExecution, RootId, SinkInfo, SinkKind,
};
use std::collections::{BTreeMap, HashMap};

/// Classification of a read operand for traffic-counter tallying (spec §11).
pub(crate) enum OperandClass {
    /// `OperandLine::LogicalGlobal` — a DRAM read (backing slot+col).
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
        OperandLine::LogicalGlobal { .. }
        | OperandLine::LogicalFold { .. }
        | OperandLine::Source { .. } => OperandClass::Dram,
        OperandLine::Smem { .. } => OperandClass::Smem,
        OperandLine::Ldc {
            sub: LdcSub::Special,
            ..
        } => OperandClass::SpecialLit,
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
    layer: &gkr_eval_ir::DagLayer,
    expr_id: gkr_eval_ir::ExprId,
    cross: &std::collections::HashMap<gkr_eval_ir::ReadPlace, gkr_eval_ir::FieldKind>,
) -> super::isa::OperandField {
    arith::child_operand_field(layer, expr_id, super::isa::OperandField::Base, cross)
}

/// Map a sink to the backing `(key, original offset)` its value materializes into.
/// Cache sinks land in `CacheOutput`; ordinary layer outputs in `LayerOutput`;
/// scratch in `Scratch`. `this_layer` supplies the layer index for `Export`.
/// Layer/cache keys are FIELD-QUALIFIED by the sink's own field (spec §2: one
/// slot = one homogeneous matrix); `Scratch` is intrinsically bf. The offset is
/// the ORIGINAL layer-offset — callers renumber it to a dense per-slot col via
/// `BackingTable::slot_col` (the same authority the read side uses), so a
/// value's `GlobalMaterialize` write and its re-reads share one dense col.
fn sink_to_backing(sink: &SinkInfo, this_layer: usize) -> (BackingKey, usize) {
    let field = operand_field_of(sink);
    match sink.kind {
        SinkKind::Cache { layer, offset } => (BackingKey::CacheOutput { layer, field }, offset),
        SinkKind::Inner { layer, offset } => (BackingKey::LayerOutput { layer, field }, offset),
        SinkKind::Export { slot } => (
            BackingKey::LayerOutput {
                layer: this_layer,
                field,
            },
            slot,
        ),
        SinkKind::Scratch { slot } => (BackingKey::Scratch, slot),
    }
}

/// The storage field of a backing READ: intrinsically-bf places are `Base`; a
/// cross-layer `LayerOutput`/`CacheOutput` read carries its PRODUCING sink's
/// field (the cross-layer field map — see `build_cross_layer_field_map`).
/// `fallback` covers a map miss (defensive; a valid circuit's map contains
/// every cross-layer-read place) and must match what the caller labels the
/// instruction with, so slot keying and instruction field bits agree.
pub(crate) fn read_place_operand_field(
    place: &ReadPlace,
    cross: &HashMap<ReadPlace, FieldKind>,
    fallback: OperandField,
) -> OperandField {
    match place {
        ReadPlace::LayerOutput { .. } | ReadPlace::CacheOutput { .. } => cross
            .get(place)
            .map(|f| match f {
                FieldKind::Base => OperandField::Base,
                FieldKind::Ext => OperandField::Ext,
            })
            .unwrap_or(fallback),
        _ => OperandField::Base,
    }
}

fn operand_field_of(sink: &SinkInfo) -> OperandField {
    match sink.field {
        gkr_eval_ir::FieldKind::Base => OperandField::Base,
        gkr_eval_ir::FieldKind::Ext => OperandField::Ext,
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
    layer_index: usize,
    root_execution: Option<&BTreeMap<RootId, RootExecution>>,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
    schedule: &LayerSchedule,
    budget: usize,
    decisions: Option<&SiteDecisions>,
) -> Result<Vec<LoweredInstr>, CompileError> {
    let mut ctx = DagForwardContext::default();
    ctx.actions = build_forward_actions(layer, root_execution)?;
    ctx.cross_layer_fields = cross_layer_fields.clone();
    let (vinstrs, step_of, _vouts, _rr) =
        lower_layer_virtual(layer, schedule, &mut ctx, layer_index, decisions, budget)?;
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
            LoweredInstr {
                step,
                kind,
                defines: pv.defines,
                value_reads,
            }
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
/// Compile one layer under the "fill-then-trim" strategy: cache maximally (lower with
/// eviction effectively disabled), then let `plan_placement` at the real `budget` be the
/// feasibility oracle. If the maximal-cache stream overflows the budget, descend the
/// lowering budget — the eviction dial; greedy eviction picks victims by per-occurrence
/// genome priority — to the largest value whose placement still fits (the fewest
/// evictions the budget allows).
///
/// Why this is never worse than the old greedy single-pass: `lower_budget == budget`
/// reproduces it exactly, and that point is always in the searched interval (it is the
/// binary search's `lo` seed / baseline). So the returned traffic is `<=` the old path's
/// for every layer, and strictly better where maximal caching (or more of it) fits — the
/// old in-loop `evict_to_fit` over-reserved against `live_width` (a 1-D width sum) while
/// real feasibility is `plan_placement`'s 2-D (lifetime x quad, with defrag) packing.
pub fn compile_layer(
    layer: &DagLayer,
    layer_index: usize,
    root_execution: Option<&BTreeMap<RootId, RootExecution>>,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
    schedule: &LayerSchedule,
    budget: usize,
    decisions: Option<&SiteDecisions>,
) -> Result<CompiledLayer, CompileError> {
    // FILL disables eviction (no real layer's live width approaches it), so lowering at
    // FILL caches every admittable value for its whole live range — the maximal-cache
    // "fill" stream. `plan_placement` at the true `budget` then decides if it fits.
    const FILL: usize = 1 << 20;
    let at = |lb: usize| {
        compile_layer_at(
            layer,
            layer_index,
            root_execution,
            cross_layer_fields,
            schedule,
            budget,
            lb,
            decisions,
        )
    };
    match at(FILL) {
        Ok(c) => return Ok(c),
        // Only a placement OVERFLOW (BudgetBelowFloor) means "too much cached" — descend.
        // Any other compile error is genuine; propagate it.
        Err(CompileError::BudgetBelowFloor { .. }) => {}
        Err(e) => return Err(e),
    }

    // Fill overflowed: binary-search the largest lowering budget in [budget, FILL) whose
    // placement fits at `budget`. `lower_budget == budget` always fits (it is exactly the
    // old lower-and-place-at-budget path), so it is the guaranteed lower bound / baseline.
    let mut best = at(budget)?; // baseline — never worse than this
    let (mut lo, mut hi) = (budget, FILL); // lo fits, hi overflows
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        match at(mid) {
            Ok(c) => {
                best = c;
                lo = mid;
            }
            Err(CompileError::BudgetBelowFloor { .. }) => hi = mid,
            Err(e) => return Err(e),
        }
    }
    Ok(best)
}

/// Lower the layer at `lower_budget` (the eviction dial) and place it at `place_budget`
/// (the real cell budget), materializing the ISA program. Factored out of `compile_layer`
/// so the fill-then-trim search can retry lowering at different budgets against a fixed
/// placement budget. `lower_budget == place_budget` is the pre-redesign behavior.
#[allow(clippy::too_many_arguments)]
fn compile_layer_at(
    layer: &DagLayer,
    layer_index: usize,
    root_execution: Option<&BTreeMap<RootId, RootExecution>>,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
    schedule: &LayerSchedule,
    place_budget: usize,
    lower_budget: usize,
    decisions: Option<&SiteDecisions>,
) -> Result<CompiledLayer, CompileError> {
    let mut ctx = DagForwardContext::default();
    ctx.actions = build_forward_actions(layer, root_execution)?;
    ctx.cross_layer_fields = cross_layer_fields.clone();

    // Phase 1 — lower to a rich virtual-instruction stream.
    let (vinstrs, step_of, vouts, resident_realized) = lower_layer_virtual(
        layer,
        schedule,
        &mut ctx,
        layer_index,
        decisions,
        lower_budget,
    )?;

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
    let free_steps: Vec<ResidencyStep> = (0..schedule.atom_order().len())
        .map(|_| ResidencyStep::default())
        .collect();
    let place_instrs: Vec<self::place::VirtualInstr> =
        vinstrs.iter().map(|vi| vi.to_place()).collect();
    let placement = plan_placement(&PlacementInput {
        instrs: &place_instrs,
        steps: &free_steps,
        step_of_instr: &step_of,
        widths: &widths,
        budget: place_budget,
    })?;

    // Phase 3 — materialize the rich stream to ISA instructions.
    let mut moves_at: HashMap<usize, Vec<RelocStep>> = HashMap::new();
    for (i, r) in &placement.moves {
        moves_at.entry(*i).or_default().push(*r);
    }
    let mut program = Program::default();
    // vinstr index → its materialized instruction's PROGRAM index (they coincide today
    // — two-phase placement is relocation-free, so no MOVs are interleaved — but the
    // placed-width map below keys by program index, so track it explicitly).
    let mut prog_idx_of_vinstr: Vec<usize> = Vec::with_capacity(vinstrs.len());
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
        prog_idx_of_vinstr.push(program.instrs.len());
        program
            .instrs
            .push(materialize_vinstr(vi, i, &placement.cell_of)?);
    }

    // Phase 3.5 — v2 promote emission (spec §1.2 iff rule). Runs over the FINAL concrete
    // stream (post-optimizer, post-placement, relocation MOVs included) so the tracked
    // acc domain reflects exactly what the VM will execute.
    apply_promote(&mut program);
    ctx.source_windows =
        bind_final_sources(&mut program, &ctx.backings, SourceMarkerMode::Forward)?;

    // Root outputs from the virtual outputs. Task 5 (spec §3): every materialized root
    // is a GlobalMaterialize write-through (or a zero-lane alias of one) — there is no
    // smem-cell-resident root output variant, by construction of `VirtualRootOutput`.
    let root_outputs: Vec<(RootId, RootOutput)> = vouts
        .into_iter()
        .map(|(rid, vo)| {
            let out = match vo {
                VirtualRootOutput::Global { slot, col } => {
                    RootOutput::Cell(OutputCell::Global { slot, col })
                }
                VirtualRootOutput::Alias(op) => RootOutput::Alias(op),
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
            Instr::Mov {
                dir,
                dst,
                src,
                field,
                ..
            } => {
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
            Instr::Add {
                field, operands, ..
            } => {
                stats.op_counts[OP_ADD] += 1;
                for op in operands {
                    tally_operand(op, *field, &ctx.specials, &mut stats);
                }
            }
            Instr::Mul {
                field, operands, ..
            } => {
                stats.op_counts[OP_MUL] += 1;
                for op in operands {
                    tally_operand(op, *field, &ctx.specials, &mut stats);
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                stats.op_counts[OP_FMA] += 1;
                for (l, r) in pairs {
                    tally_operand(l, *field_lhs, &ctx.specials, &mut stats);
                    tally_operand(r, *field_rhs, &ctx.specials, &mut stats);
                }
            }
        }
    }
    // A `CopyAlias` output root copies its `src_addr`'s backing straight to `dst_addr`
    // with ZERO program lanes (resolved outside the ISA stream); on device it is a
    // pointer/view, not a re-read. So it costs no DRAM traffic and is NOT tallied here —
    // matching the floor (`dag_traffic_floor_with_actions` counts `Compute` roots only)
    // and the device. (Charging it inflated `dram_traffic` — the S3 objective — by the
    // alias count, making the floor unreachable by construction; the alias set is DAG-
    // structural so this is a pure relabel, not a schedule change.)
    stats.special_gathers = ctx
        .specials
        .iter()
        .filter(|d| {
            !matches!(
                d.strategy,
                super::source::SpecialStrategy::VirtualSetup { .. }
            )
        })
        .count();
    stats.max_live_cells = placement.max_live_cells;

    let mut trace = CompileTrace::default();
    trace.max_live_cells = placement.max_live_cells;
    trace.placement_moves = placement.move_ctx.clone();
    // Task 6: retain the per-cell placed-width map for `validate.rs`'s
    // `SmemRegionMismatch` check — `placement.cell_of` is consumed above and dropped
    // with this function, so project it (via `widths`) onto `(program instr, lane)`
    // keys now. An Ext value's entry covers all 4 lanes of its bucket, so a bf-view
    // poke into ANY lane of a live Ext bucket is detectable, not just lane 0.
    for (&(vi_idx, v), &lane) in &placement.cell_of {
        let f = *widths.get(&v).expect("placed value has a recorded width");
        let pi = prog_idx_of_vinstr[vi_idx];
        match f {
            OperandField::Ext => {
                for j in 0..4 {
                    trace.placed_cell_fields.insert((pi, lane + j), f);
                }
            }
            OperandField::Base => {
                trace.placed_cell_fields.insert((pi, lane), f);
            }
        }
    }

    Ok(CompiledLayer {
        program,
        ctx,
        root_outputs,
        skipped,
        trace,
        budget: place_budget,
        stats,
        resident_realized,
    })
}

fn apply_promote(program: &mut Program) {
    let mut acc_is_ext = false;
    for instr in &mut program.instrs {
        match instr {
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                field,
                ..
            } => {
                acc_is_ext = *field == OperandField::Ext;
            }
            Instr::Mov { .. } => {} // stores/copies never change the acc domain
            Instr::Add { field, promote, .. } => {
                let requires_ext = *field == OperandField::Ext;
                *promote = requires_ext && !acc_is_ext;
                acc_is_ext |= requires_ext;
            }
            Instr::Mul {
                field,
                promote,
                operands,
                ..
            } => {
                // Mul{Base} dispatches (scale) and zero-arity Mul is pure negation —
                // neither requires an ext acc; only Mul{Ext} with operands does.
                let requires_ext = *field == OperandField::Ext && !operands.is_empty();
                *promote = requires_ext && !acc_is_ext;
                acc_is_ext |= requires_ext;
            }
            Instr::Fma {
                field_rhs, promote, ..
            } => {
                // Fma{B,B} is a bf-product + limb-0 add; Fma{B,E}/{E,E} fold a full e4
                // product into acc (canonical order puts Ext on the rhs).
                let requires_ext = *field_rhs == OperandField::Ext;
                *promote = requires_ext && !acc_is_ext;
                acc_is_ext |= requires_ext;
            }
        }
    }
}

/// v2 wire index for an `Smem` reference (spec §3): the 14-bit cell field is a plain
/// index whose UNIT the instruction's field bit selects — bf → the allocator's 4-B
/// lane index unchanged (v1 bf cell `4b+j`), ext → the 16-B BUCKET index `lane / 4`.
/// Placement guarantees every Ext lane is 4-aligned (Ext-first quad packing), so the
/// divide fails CLOSED on a misaligned lane (a compiler bug) instead of flooring.
fn smem_wire_index(lane: u16, field: OperandField) -> Result<u16, CompileError> {
    match field {
        OperandField::Base => Ok(lane),
        OperandField::Ext => {
            if lane % 4 != 0 {
                return Err(CompileError::ExtCellMisaligned(lane));
            }
            Ok(lane / 4)
        }
    }
}

/// Materialize one rich `VInstr` to an ISA `Instr` using the allocator's `cell_of` map.
/// Smem indices are translated to their v2 wire unit per operand/dst field bit
/// (`smem_wire_index`): Add/Mul apply `field` to every operand, Fma applies
/// `field_lhs`/`field_rhs` per side, Mov applies `field` to both src and dst.
fn materialize_vinstr(
    vi: &VInstr,
    i: usize,
    cell_of: &HashMap<(usize, ValueId), u16>,
) -> Result<Instr, CompileError> {
    let lane_of = |v: &ValueId| -> Result<u16, CompileError> {
        cell_of.get(&(i, *v)).copied().ok_or_else(|| {
            CompileError::FieldMismatch(format!("no cell for value {} at instr {i}", v.0))
        })
    };
    let op_of = |op: &VirtualOp, field: OperandField| -> Result<OperandLine, CompileError> {
        match op {
            VirtualOp::Value(v) => Ok(OperandLine::Smem {
                cell: smem_wire_index(lane_of(v)?, field)?,
            }),
            VirtualOp::Global { slot, col } => Ok(OperandLine::LogicalGlobal {
                slot: *slot,
                col: *col,
            }),
            VirtualOp::Ldc { sub, idx } => Ok(OperandLine::Ldc {
                sub: *sub,
                idx: *idx,
            }),
            VirtualOp::Special { desc } => Ok(OperandLine::Special { desc: *desc }),
            VirtualOp::Acc => Err(CompileError::FieldMismatch("unexpected Acc operand".into())),
        }
    };
    Ok(match vi {
        VInstr::Add {
            field, sign, reads, ..
        } => Instr::Add {
            field: *field,
            sign: *sign,
            promote: false,
            operands: reads
                .iter()
                .map(|o| op_of(o, *field))
                .collect::<Result<_, _>>()?,
        },
        VInstr::Mul { field, reads, .. } => Instr::Mul {
            field: *field,
            promote: false,
            // v2 §1.2: zero-arity Mul IS the pure acc negation (the wire legality rule
            // is "arity 0 iff negate_acc", and the lowering emits an empty-reads Mul
            // only from `emit_unary_negate`). Non-empty Muls never negate.
            negate_acc: reads.is_empty(),
            operands: reads
                .iter()
                .map(|o| op_of(o, *field))
                .collect::<Result<_, _>>()?,
        },
        VInstr::Fma {
            field_lhs,
            field_rhs,
            sign,
            pairs,
            ..
        } => {
            let mut out = Vec::with_capacity(pairs.len());
            for (l, r) in pairs {
                out.push((op_of(l, *field_lhs)?, op_of(r, *field_rhs)?));
            }
            Instr::Fma {
                field_lhs: *field_lhs,
                field_rhs: *field_rhs,
                sign: *sign,
                promote: false,
                pairs: out,
            }
        }
        VInstr::Mov {
            dir,
            field,
            dst,
            src,
            ..
        } => {
            let dst = match dst {
                None => None,
                Some(VDst::Cell(v)) => Some(DstLine::Smem {
                    cell: smem_wire_index(lane_of(v)?, *field)?,
                }),
                Some(VDst::GlobalMaterialize { slot, col }) => Some(DstLine::GlobalMaterialize {
                    slot: *slot,
                    col: *col,
                }),
                Some(VDst::BatchAccumulate { coefficient_desc }) => {
                    let coefficient_desc = match coefficient_desc {
                        Some(desc) if *desc <= BATCH_COEFFICIENT_MAX => *desc,
                        Some(desc) => {
                            return Err(CompileError::FieldMismatch(format!(
                                "backward batch coefficient descriptor {desc:#06x} exceeds \
                                 maximum {BATCH_COEFFICIENT_MAX:#06x}"
                            )));
                        }
                        None => BATCH_COEFFICIENT_ONE,
                    };
                    Some(pack_batch_dst(coefficient_desc).map_err(|error| {
                        CompileError::FieldMismatch(format!(
                            "invalid backward batch coefficient descriptor: {error:?}"
                        ))
                    })?)
                }
            };
            let src = match src {
                None => None,
                Some(op) => Some(op_of(op, *field)?),
            };
            Instr::Mov {
                dir: *dir,
                field: *field,
                dst,
                src,
            }
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
    let bytes = std::fs::read(path)
        .map_err(|e| CompileError::InvalidSchedule(format!("read {}: {e}", path.display())))?;
    parse_committed_schedule(&bytes, &path.display().to_string())
}

/// Parse a committed `*_schedule_b16_gkr.json` already in memory.
/// [`load_committed_schedule`] is this plus the file read; a consumer that
/// embeds the schedule in its binary has no path to read at runtime and calls
/// this directly. `origin` only names the source in the error message.
pub fn parse_committed_schedule(
    bytes: &[u8],
    origin: &str,
) -> Result<CircuitSchedule, CompileError> {
    serde_json::from_slice(bytes)
        .map_err(|e| CompileError::InvalidSchedule(format!("parse {origin}: {e}")))
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
) -> Result<CompiledCircuit, CompileError> {
    crate::schedule::validate_circuit_schedule(dag, schedule)
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
                li,
                dag.globals.root_execution.get(li),
                &cross,
                ls,
                schedule.budget,
                Some(&decisions),
            )?);
        }
    }
    Ok(CompiledCircuit {
        circuit: schedule.circuit.clone(),
        budget: schedule.budget,
        layers,
    })
}
