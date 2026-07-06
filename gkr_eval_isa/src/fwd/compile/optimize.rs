//! Pre-placement VInstr peephole optimizer (spec: emitter codegen-quality pass).
//! Runs after `lower_layer_virtual`, before the `widths` scan / placement in
//! `compile_layer`. Every rewrite is value-preserving; placement re-derives liveness
//! from the rewritten stream. Rules: F1 leaf-fuse, F4/redundant-reload, F2 commute,
//! F5 dead-admission (added in later tasks). This task is the scaffold + acc model.

use std::collections::BTreeSet;

use cs::gkr_compiler::dag_ir::ExprId;

use super::lower::{VDst, VInstr};
use super::place::{ValueId, VirtualOp};
use crate::fwd::isa::MovDir;

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
        // Storing acc into cell v makes acc alias v (codex-R5); a committed backing
        // write (GlobalMaterialize) leaves acc unchanged.
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

/// Delete `del` indices from `vinstrs` and `step_of` in lockstep (preserves the
/// `step_of.len() == vinstrs.len()` invariant).
fn delete_indices(vinstrs: &mut Vec<VInstr>, step_of: &mut Vec<usize>, del: &BTreeSet<usize>) {
    if del.is_empty() {
        return;
    }
    let mut i = 0usize;
    vinstrs.retain(|_| {
        let keep = !del.contains(&i);
        i += 1;
        keep
    });
    let mut j = 0usize;
    step_of.retain(|_| {
        let keep = !del.contains(&j);
        j += 1;
        keep
    });
}

/// Optimize the lowered stream. Identity for now; rules are added in later tasks.
pub(crate) fn optimize_vinstrs(
    vinstrs: Vec<VInstr>,
    step_of: Vec<usize>,
) -> (Vec<VInstr>, Vec<usize>) {
    debug_assert_eq!(
        vinstrs.len(),
        step_of.len(),
        "step_of must parallel vinstrs"
    );
    (vinstrs, step_of)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fwd::isa::OperandField;

    fn mov_load(v: ValueId) -> VInstr {
        VInstr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(VirtualOp::Value(v)),
            defines: None,
            is_dram_read: false,
        }
    }
    fn mov_store(v: ValueId) -> VInstr {
        VInstr::Mov {
            dir: MovDir::DstFromAcc,
            field: OperandField::Base,
            dst: Some(VDst::Cell(v)),
            src: None,
            defines: Some(v),
            is_dram_read: false,
        }
    }

    #[test]
    fn identity_optimize_preserves_stream_and_lockstep() {
        let v = ExprId(0);
        let vinstrs = vec![mov_store(v), mov_load(v)];
        let step_of = vec![0, 0];
        let (out, step) = optimize_vinstrs(vinstrs.clone(), step_of.clone());
        assert_eq!(out.len(), vinstrs.len());
        assert_eq!(step, step_of);
    }

    #[test]
    fn acc_model_refines_on_store_and_load() {
        let v = ExprId(0);
        let stream = vec![mov_store(v), mov_load(v)];
        let ab = acc_before(&stream);
        assert_eq!(ab, vec![AccVal::Unknown, AccVal::Value(v)]); // before store Unknown; before load acc aliases v
    }
}
