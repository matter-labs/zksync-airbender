use std::collections::BTreeSet;

use gpu_gkr_compiler::{
    ForwardDstLine as Dst, ForwardInstr as Instr, ForwardMovDir as Mov,
    ForwardOperandField as Field, ForwardOperandLine as Operand,
};

pub(super) fn visit_operands(instruction: &Instr, mut visit: impl FnMut(&Operand, Field)) {
    match instruction {
        Instr::Add {
            field, operands, ..
        }
        | Instr::Mul {
            field, operands, ..
        } => {
            for operand in operands {
                visit(operand, *field);
            }
        }
        Instr::Fma {
            field_lhs,
            field_rhs,
            pairs,
            ..
        } => {
            for (lhs, rhs) in pairs {
                visit(lhs, *field_lhs);
                visit(rhs, *field_rhs);
            }
        }
        Instr::Mov {
            field,
            src: Some(src),
            ..
        } => visit(src, *field),
        Instr::Mov { src: None, .. } => {}
    }
}

fn cell_lanes(cell: u16, field: Field) -> std::ops::Range<usize> {
    // BF cell indices address individual lanes; E4 indices address four-lane buckets.
    let width = if field == Field::Base { 1 } else { 4 };
    let start = usize::from(cell) * width;
    start..start + width
}

pub(super) fn keep_instruction(
    instruction: &Instr,
    acc_live: &mut bool,
    cells: &mut BTreeSet<usize>,
    keep_store: impl FnOnce(u8, u16) -> bool,
) -> bool {
    let keep = match instruction {
        Instr::Mov {
            dir: Mov::AccFromSrc,
            ..
        } => std::mem::replace(acc_live, false),
        Instr::Mov {
            dir, field, dst, ..
        } => {
            let keep = match dst.expect("compiled move destination") {
                Dst::GlobalMaterialize { slot, col } => keep_store(slot, col),
                Dst::Smem { cell } => {
                    let mut live = false;
                    for lane in cell_lanes(cell, *field) {
                        live |= cells.remove(&lane);
                    }
                    live
                }
            };
            if keep && *dir == Mov::DstFromAcc {
                *acc_live = true;
            }
            keep
        }
        Instr::Add { .. } | Instr::Mul { .. } | Instr::Fma { .. } => *acc_live,
    };
    if keep {
        visit_operands(instruction, |operand, field| {
            if let Operand::Smem { cell } = operand {
                cells.extend(cell_lanes(*cell, field));
            }
        });
    }
    keep
}

#[cfg(test)]
mod cpu_tests;
