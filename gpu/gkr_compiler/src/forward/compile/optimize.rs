//! Value-preserving peephole optimization before placement.

use std::collections::{HashMap, HashSet};

use super::lower::{VDst, VInstr};
use super::place::{ValueId, VirtualOp};
use crate::forward::isa::{MovDir, OperandField, Sign};

/// Abstract accumulator contents at a program point. `Value(v)` means acc currently
/// holds the same value the cell for `v` holds (established either by loading `v` or by
/// storing acc into cell `v`). `Unknown` = a derived/unmodeled value.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum AccVal {
    Unknown,
    Value(ValueId),
}

/// acc contents AFTER executing `vi`, given acc BEFORE it.
fn next_acc(vi: &VInstr, acc: AccVal) -> AccVal {
    match vi {
        VInstr::Mov {
            dir: MovDir::AccFromSrc,
            src,
            ..
        } => match src {
            Some(VirtualOp::Value(v)) => AccVal::Value(*v),
            _ => AccVal::Unknown, // leaf/ldc/global-in-acc: not tracked as a Value
        },
        // A cell store gives the accumulator that value's identity.
        VInstr::Mov {
            dir: MovDir::DstFromAcc,
            dst,
            ..
        } => match dst {
            Some(VDst::Cell(v)) => AccVal::Value(*v),
            _ => acc,
        },
        VInstr::Mov {
            dir: MovDir::DstFromSrc,
            ..
        } => acc, // does not touch acc
        VInstr::Add { .. } | VInstr::Mul { .. } | VInstr::Fma { .. } => AccVal::Unknown,
    }
}

/// `acc_before[i]` = acc contents immediately BEFORE instruction `i`.
fn acc_before(vinstrs: &[VInstr]) -> Vec<AccVal> {
    let mut acc = AccVal::Unknown;
    let mut out = Vec::with_capacity(vinstrs.len());
    for vi in vinstrs {
        out.push(acc);
        acc = next_acc(vi, acc);
    }
    out
}

fn delete_indices(vinstrs: &mut Vec<VInstr>, del: &[bool]) -> bool {
    let changed = del.iter().any(|&delete| delete);
    if !changed {
        return false;
    }
    let mut i = 0usize;
    vinstrs.retain(|_| {
        let keep = !del[i];
        i += 1;
        keep
    });
    true
}

/// Does `vi` read the accumulator's current value (before possibly overwriting it)?
/// AccFromSrc overwrites without reading; DstFromSrc doesn't touch acc. All arithmetic
/// ops read acc, and DstFromAcc reads acc (to store it).
fn reads_acc(vi: &VInstr) -> bool {
    match vi {
        VInstr::Mov {
            dir: MovDir::AccFromSrc,
            ..
        }
        | VInstr::Mov {
            dir: MovDir::DstFromSrc,
            ..
        } => false,
        VInstr::Mov {
            dir: MovDir::DstFromAcc,
            ..
        } => true,
        VInstr::Add { .. } | VInstr::Mul { .. } | VInstr::Fma { .. } => true,
    }
}

/// Fuse `AccFromSrc(src); DstFromAcc(dst)` when the accumulator is dead afterwards.
fn fuse_leaf_loads(vinstrs: &mut Vec<VInstr>) -> bool {
    let mut del = vec![false; vinstrs.len()];
    let mut next_touch_reads = vec![false; vinstrs.len() + 1];
    for i in (0..vinstrs.len()).rev() {
        next_touch_reads[i] = if reads_acc(&vinstrs[i]) {
            true
        } else if matches!(
            vinstrs[i],
            VInstr::Mov {
                dir: MovDir::AccFromSrc,
                ..
            }
        ) {
            false
        } else {
            next_touch_reads[i + 1]
        };
    }
    let mut i = 0usize;
    while i + 1 < vinstrs.len() {
        let (load_src, load_field) = match &vinstrs[i] {
            VInstr::Mov {
                dir: MovDir::AccFromSrc,
                src: Some(s),
                field,
                ..
            } => (*s, *field),
            _ => {
                i += 1;
                continue;
            }
        };
        let store = matches!(
            &vinstrs[i + 1],
            VInstr::Mov {
                dir: MovDir::DstFromAcc,
                field,
                dst: Some(VDst::Cell(_) | VDst::GlobalMaterialize { .. }),
                ..
            } if *field == load_field
        );
        if !store {
            i += 1;
            continue;
        }
        if next_touch_reads[i + 2] {
            i += 1;
            continue;
        }
        // Do not create a self-read/self-define.
        if let VirtualOp::Value(x) = &load_src {
            if vinstrs[i + 1].defines() == Some(*x) {
                i += 1;
                continue;
            }
        }
        // Rewrite the store into `DstFromSrc(dst <- load_src)`.
        if let VInstr::Mov {
            dir, field, src, ..
        } = &mut vinstrs[i + 1]
        {
            *dir = MovDir::DstFromSrc;
            *field = load_field;
            *src = Some(load_src);
        }
        del[i] = true;
        i += 2;
    }
    delete_indices(vinstrs, &del)
}

/// Delete a cell reload when the accumulator already holds that value.
fn drop_redundant_reloads(vinstrs: &mut Vec<VInstr>) -> bool {
    let ab = acc_before(vinstrs);
    let mut del = vec![false; vinstrs.len()];
    for (i, vi) in vinstrs.iter().enumerate() {
        if let VInstr::Mov {
            dir: MovDir::AccFromSrc,
            src: Some(VirtualOp::Value(v)),
            ..
        } = vi
        {
            if ab[i] == AccVal::Value(*v) {
                del[i] = true;
            }
        }
    }
    delete_indices(vinstrs, &del)
}

/// Drop a cell definition that is never read before redefinition or program end.
fn drop_dead_admissions(vinstrs: &mut Vec<VInstr>) -> bool {
    let mut del = vec![false; vinstrs.len()];
    let mut live = HashSet::new();
    for (i, instr) in vinstrs.iter().enumerate().rev() {
        if let Some(value) = instr.defines() {
            if !live.remove(&value) {
                del[i] = true;
            }
        }
        instr.for_each_read(|op| {
            if let VirtualOp::Value(value) = op {
                live.insert(*value);
            }
        });
    }
    delete_indices(vinstrs, &del)
}

/// Can `vi` (the consumer at i+1) commute an operand with the accumulator seed?
/// Mul: always. Add: only the Plus sign. Fma/minus-Add: no.
fn op_commutes_with_seed(vi: &VInstr) -> bool {
    matches!(
        vi,
        VInstr::Mul { .. }
            | VInstr::Add {
                sign: Sign::Plus,
                ..
            }
    )
}

/// Keep the old accumulator value and retarget a commuting operand to the reloaded cell.
/// Equal widths are required because the consumer field governs the substituted cell read.
fn commute_keep_in_acc(vinstrs: &mut Vec<VInstr>, widths: &HashMap<ValueId, OperandField>) -> bool {
    let ab = acc_before(vinstrs);
    let mut del = vec![false; vinstrs.len()];
    let mut i = 0usize;
    while i + 1 < vinstrs.len() {
        let w = match &vinstrs[i] {
            VInstr::Mov {
                dir: MovDir::AccFromSrc,
                src: Some(VirtualOp::Value(w)),
                ..
            } => *w,
            _ => {
                i += 1;
                continue;
            }
        };
        let v = match ab[i] {
            AccVal::Value(v) => v,
            AccVal::Unknown => {
                i += 1;
                continue;
            }
        };
        if v == w {
            i += 1;
            continue;
        }
        if !op_commutes_with_seed(&vinstrs[i + 1]) {
            i += 1;
            continue;
        }
        if widths.get(&w) != widths.get(&v) {
            i += 1;
            continue;
        }
        if retarget_value_to_op(&mut vinstrs[i + 1], v, &VirtualOp::Value(w)) {
            del[i] = true;
            i += 2;
        } else {
            i += 1;
        }
    }
    delete_indices(vinstrs, &del)
}

/// Replace the first `Value(from)` operand with `to`.
fn retarget_value_to_op(vi: &mut VInstr, from: ValueId, to: &VirtualOp) -> bool {
    let is_from = |op: &VirtualOp| matches!(op, VirtualOp::Value(x) if *x == from);
    match vi {
        VInstr::Mov { src, .. } => {
            if src.as_ref().is_some_and(is_from) {
                *src = Some(*to);
                true
            } else {
                false
            }
        }
        VInstr::Add { reads, .. } | VInstr::Mul { reads, .. } => {
            for op in reads.iter_mut() {
                if is_from(op) {
                    *op = *to;
                    return true;
                }
            }
            false
        }
        VInstr::Fma { pairs, .. } => {
            for (l, r) in pairs.iter_mut() {
                if is_from(l) {
                    *l = *to;
                    return true;
                }
                if is_from(r) {
                    *r = *to;
                    return true;
                }
            }
            false
        }
    }
}

/// Propagate an immutable leaf source into its sole read. Cell sources and accumulator
/// spills are excluded.
fn propagate_single_use_leaf_copies(vinstrs: &mut [VInstr]) -> bool {
    let mut leaf_copies: Vec<(ValueId, VirtualOp)> = Vec::new();
    for vi in vinstrs.iter() {
        if let VInstr::Mov {
            dir: MovDir::DstFromSrc,
            dst: Some(VDst::Cell(v)),
            src: Some(op),
            ..
        } = vi
        {
            if matches!(
                op,
                VirtualOp::Global { .. } | VirtualOp::Special { .. } | VirtualOp::Ldc { .. }
            ) {
                leaf_copies.push((*v, *op));
            }
        }
    }
    let mut uses: HashMap<ValueId, (usize, usize)> = HashMap::new();
    for (i, instr) in vinstrs.iter().enumerate() {
        instr.for_each_read(|op| {
            if let VirtualOp::Value(value) = op {
                let use_info = uses.entry(*value).or_insert((0, i));
                use_info.0 += 1;
                use_info.1 = i;
            }
        });
    }
    let mut changed = false;
    for (v, op) in leaf_copies {
        let Some(&(1, reader)) = uses.get(&v) else {
            continue;
        };
        if retarget_value_to_op(&mut vinstrs[reader], v, &op) {
            changed = true;
        }
    }
    changed
}

/// Optimize the lowered stream via a fixpoint of the rewrite rules.
pub(crate) fn optimize_vinstrs(
    mut vinstrs: Vec<VInstr>,
    widths: &HashMap<ValueId, OperandField>,
) -> Vec<VInstr> {
    loop {
        let mut changed = false;
        changed |= fuse_leaf_loads(&mut vinstrs);
        changed |= drop_redundant_reloads(&mut vinstrs);
        changed |= commute_keep_in_acc(&mut vinstrs, widths);
        changed |= propagate_single_use_leaf_copies(&mut vinstrs);
        changed |= drop_dead_admissions(&mut vinstrs);
        if !changed {
            break;
        }
    }
    vinstrs
}
