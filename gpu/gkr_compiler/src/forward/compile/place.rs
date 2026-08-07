//! Fixed shared-memory placement for the forward instruction stream.

use std::collections::HashMap;

use gkr_eval_ir::ExprId;

use crate::forward::compile::CompileError;
use crate::forward::isa::{LdcSub, OperandField};
use crate::interval_pack::{self, Interval, PackFailure, PackWidth};

use super::lower::VInstr;

pub(super) type ValueId = ExprId;

#[derive(Clone, Copy, Debug)]
pub(super) enum VirtualOp {
    Value(ValueId),
    Global { slot: u8, col: u16 },
    Ldc { sub: LdcSub, idx: u16 },
    Special { desc: u16 },
}

// ─────────────────────────────────────────────────────────────────────────────────
// Live ranges.
// ─────────────────────────────────────────────────────────────────────────────────

type LiveRange = Interval;

/// Build each value's inclusive `[def, last_use]` interval.
fn compute_live_ranges(instrs: &[VInstr]) -> HashMap<ValueId, LiveRange> {
    let mut ranges = HashMap::new();
    for (i, instr) in instrs.iter().enumerate() {
        if let Some(v) = instr.defines() {
            ranges.entry(v).or_insert(LiveRange {
                def: i,
                last_use: i,
            });
        }
    }
    for (i, instr) in instrs.iter().enumerate() {
        instr.for_each_read(|read| {
            if let VirtualOp::Value(v) = read {
                let range = ranges
                    .get_mut(v)
                    .unwrap_or_else(|| panic!("value {v:?} is read but never defined"));
                assert!(i >= range.def, "value {v:?} is read before its definition");
                range.last_use = range.last_use.max(i);
            }
        });
    }
    ranges
}

/// The packer's width for a forward value.
fn pack_width_of(widths: &HashMap<ValueId, OperandField>, v: ValueId) -> PackWidth {
    match widths.get(&v) {
        Some(OperandField::Ext) => PackWidth::Quad,
        Some(OperandField::Base) => PackWidth::Single,
        None => panic!("no width recorded for value {v:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────────
// Two-phase interval packing (Ext-first) — the adapter onto `crate::interval_pack`.
// ─────────────────────────────────────────────────────────────────────────────────

/// Assign non-overlapping cells, keeping extension values on aligned quads.
fn assign_cells(
    ranges: &HashMap<ValueId, LiveRange>,
    widths: &HashMap<ValueId, OperandField>,
    budget: usize,
) -> Result<HashMap<ValueId, u16>, CompileError> {
    interval_pack::assign_lanes(ranges, |v| pack_width_of(widths, v), budget).map_err(
        |e: PackFailure| CompileError::BudgetBelowFloor {
            floor: e.floor(budget),
            budget,
        },
    )
}

pub(super) fn plan_placement(
    instrs: &[VInstr],
    widths: &HashMap<ValueId, OperandField>,
    budget: usize,
) -> Result<HashMap<ValueId, u16>, CompileError> {
    assign_cells(&compute_live_ranges(instrs), widths, budget)
}
