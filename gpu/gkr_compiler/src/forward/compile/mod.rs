mod arith;
pub(crate) mod decisions;
mod lower;
mod optimize;
mod place;

use self::decisions::SiteDecisions;
use self::lower::lower_layer_virtual;
use self::lower::{VDst, VInstr};
use self::place::{plan_placement, ValueId, VirtualOp};
use super::binding::{bind_final_sources, BackingKey};
use super::context::{build_compute_roots, CompiledLayer, CompiledLayerBuild, DagForwardContext};
use super::error::CompileError;
use super::isa::{DstLine, Instr, OperandField, OperandLine, Program};
use super::stats::CompileStats;
use crate::analysis::build_cross_layer_field_map;
use crate::forward::artifact::{ForwardLayerArtifact, ForwardSearchArtifact};
use crate::forward::BF_LANES_PER_E4_BUCKET;
use gkr_eval_ir::{DagCircuit, DagLayer, FieldKind, ReadPlace, SinkInfo, SinkKind};
use std::collections::HashMap;

fn tally_dram_traffic(op: &OperandLine, field: OperandField, traffic: &mut usize) {
    if matches!(op, OperandLine::Source { .. }) {
        *traffic += field.lanes();
    }
}

#[cfg(feature = "search")]
pub(crate) fn expr_operand_field(
    layer: &gkr_eval_ir::DagLayer,
    expr_id: gkr_eval_ir::ExprId,
    cross: &std::collections::HashMap<gkr_eval_ir::ReadPlace, gkr_eval_ir::FieldKind>,
) -> super::isa::OperandField {
    arith::child_operand_field(layer, expr_id, cross)
}

/// Map a sink to the backing `(key, original offset)` its value materializes into.
/// Cache sinks land in `CacheOutput`; ordinary layer outputs in `LayerOutput`;
/// scratch in `Scratch`.
/// Layer/cache keys include the sink field; scratch is always base-field. The
/// caller renumbers the original offset through `BackingTable::slot_col`.
fn sink_to_backing(sink: &SinkInfo) -> (BackingKey, usize) {
    let field = operand_field_of(sink);
    match sink.kind {
        SinkKind::Cache { layer, offset } => (BackingKey::CacheOutput { layer, field }, offset),
        SinkKind::Inner { layer, offset } => (BackingKey::LayerOutput { layer, field }, offset),
        SinkKind::Scratch { slot } => (BackingKey::Scratch, slot),
    }
}

/// The storage field of a backing READ: intrinsically-bf places are `Base`; a
/// cross-layer `LayerOutput`/`CacheOutput` read carries its PRODUCING sink's
/// field (the cross-layer field map — see `build_cross_layer_field_map`).
pub(crate) fn read_place_operand_field(
    place: &ReadPlace,
    cross: &HashMap<ReadPlace, FieldKind>,
) -> OperandField {
    match place {
        ReadPlace::LayerOutput { .. } | ReadPlace::CacheOutput { .. } => cross
            .get(place)
            .copied()
            .map(Into::into)
            .expect("cross-layer fields must be resolved before compilation"),
        _ => OperandField::Base,
    }
}

fn operand_field_of(sink: &SinkInfo) -> OperandField {
    sink.field.into()
}

#[derive(Clone, Debug)]
pub struct CompiledCircuit {
    pub layers: Vec<CompiledLayer>,
}

/// Compile one scheduled layer, retaining as much selected cache residency as fits.
pub(crate) fn compile_layer(
    layer: &DagLayer,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
    schedule: &ForwardLayerArtifact,
    budget: usize,
) -> Result<CompiledLayerBuild, CompileError> {
    const FILL: usize = 1 << 20;
    let decisions = SiteDecisions::new(schedule.sites.iter().copied());
    let at =
        |lb: usize| compile_layer_at(layer, cross_layer_fields, schedule, budget, lb, &decisions);
    match at(FILL) {
        Ok(c) => return Ok(c),
        Err(CompileError::BudgetBelowFloor { .. }) => {}
        Err(e) => return Err(e),
    }

    let mut best = at(budget)?;
    let (mut lo, mut hi) = (budget, FILL);
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

#[allow(clippy::too_many_arguments)]
fn compile_layer_at(
    layer: &DagLayer,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
    schedule: &ForwardLayerArtifact,
    place_budget: usize,
    lower_budget: usize,
    decisions: &SiteDecisions,
) -> Result<CompiledLayerBuild, CompileError> {
    let mut ctx = DagForwardContext::default();
    let compute_roots = build_compute_roots(layer);
    let (vinstrs, widths) = lower_layer_virtual(
        layer,
        schedule,
        &mut ctx,
        cross_layer_fields,
        &compute_roots,
        decisions,
        lower_budget,
    )?;

    // Value-preserving peephole optimization.
    let vinstrs = self::optimize::optimize_vinstrs(vinstrs, &widths);

    let cell_of = plan_placement(&vinstrs, &widths, place_budget)?;

    let mut program = Program::default();
    for (i, vi) in vinstrs.iter().enumerate() {
        program
            .instrs
            .push(materialize_vinstr(vi, i, &cell_of, &widths)?);
    }

    // Bind logical reads to source windows.
    ctx.source_windows = bind_final_sources(&mut program, &ctx.backings)?;

    let mut stats = CompileStats::default();
    stats.instrs = program.instrs.len();
    for instr in &program.instrs {
        match instr {
            Instr::Mov { src, field, .. } => {
                if let Some(op) = src {
                    tally_dram_traffic(op, *field, &mut stats.dram_traffic);
                }
            }
            Instr::Add {
                field, operands, ..
            } => {
                for op in operands {
                    tally_dram_traffic(op, *field, &mut stats.dram_traffic);
                }
            }
            Instr::Mul {
                field, operands, ..
            } => {
                for op in operands {
                    tally_dram_traffic(op, *field, &mut stats.dram_traffic);
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                for (l, r) in pairs {
                    tally_dram_traffic(l, *field_lhs, &mut stats.dram_traffic);
                    tally_dram_traffic(r, *field_rhs, &mut stats.dram_traffic);
                }
            }
        }
    }

    Ok(CompiledLayerBuild {
        program,
        ctx,
        budget_lanes: place_budget,
        stats,
    })
}

/// Convert an allocator lane to the field-dependent shared-memory wire index.
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

/// Materialize one rich instruction with its fixed cell assignment.
fn materialize_vinstr(
    vi: &VInstr,
    i: usize,
    cell_of: &HashMap<ValueId, u16>,
    widths: &HashMap<ValueId, OperandField>,
) -> Result<Instr, CompileError> {
    let lane_of = |v: &ValueId, field: OperandField| -> Result<u16, CompileError> {
        if widths.get(v).copied() != Some(field) {
            return Err(CompileError::FieldMismatch(format!(
                "value {} used as {field:?}",
                v.0
            )));
        }
        cell_of.get(v).copied().ok_or_else(|| {
            CompileError::FieldMismatch(format!("no cell for value {} at instr {i}", v.0))
        })
    };
    let op_of = |op: &VirtualOp, field: OperandField| -> Result<OperandLine, CompileError> {
        match op {
            VirtualOp::Value(v) => Ok(OperandLine::Smem {
                cell: smem_wire_index(lane_of(v, field)?, field)?,
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
        }
    };
    Ok(match vi {
        VInstr::Add {
            field, sign, reads, ..
        } => Instr::Add {
            field: *field,
            sign: *sign,
            operands: reads
                .iter()
                .map(|o| op_of(o, *field))
                .collect::<Result<_, _>>()?,
        },
        VInstr::Mul { field, reads, .. } => Instr::Mul {
            field: *field,
            // Empty Mul is the pure accumulator negation.
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
                    cell: smem_wire_index(lane_of(v, *field)?, *field)?,
                }),
                Some(VDst::GlobalMaterialize { slot, col }) => Some(DstLine::GlobalMaterialize {
                    slot: *slot,
                    col: *col,
                }),
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

/// Compile a checked circuit schedule into one program per DAG layer.
pub(crate) fn compile_circuit(
    dag: &DagCircuit,
    schedule: &ForwardSearchArtifact,
) -> Result<Vec<CompiledLayerBuild>, CompileError> {
    let budget_lanes = schedule.budget_buckets * BF_LANES_PER_E4_BUCKET;
    let cross = build_cross_layer_field_map(dag);
    let mut layers = Vec::with_capacity(dag.layers.len());
    for (li, layer) in dag.layers.iter().enumerate() {
        let ls = &schedule.layers[li];
        if ls.units.is_empty() {
            layers.push(CompiledLayerBuild {
                program: Program::default(),
                ctx: DagForwardContext::default(),
                budget_lanes,
                stats: CompileStats::default(),
            });
        } else {
            layers.push(compile_layer(layer, &cross, ls, budget_lanes)?);
        }
    }
    Ok(layers)
}
