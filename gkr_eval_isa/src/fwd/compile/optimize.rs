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

/// Whether `vi` overwrites acc without first reading it (a "fresh" acc write).
fn writes_acc_fresh(vi: &VInstr) -> bool {
    matches!(
        vi,
        VInstr::Mov {
            dir: MovDir::AccFromSrc,
            ..
        }
    )
}

/// F1: `AccFromSrc(src); DstFromAcc(Cell/Global dst)` where the src value is dead after
/// the store (the next acc-touching instr overwrites acc without reading it) → fuse to a
/// single `DstFromSrc(dst, src)`. Returns true if any fusion happened.
fn fuse_leaf_loads(vinstrs: &mut Vec<VInstr>, step_of: &mut Vec<usize>) -> bool {
    let mut del: BTreeSet<usize> = BTreeSet::new();
    let mut i = 0usize;
    while i + 1 < vinstrs.len() {
        let (load_src, load_field) = match &vinstrs[i] {
            VInstr::Mov {
                dir: MovDir::AccFromSrc,
                src: Some(s),
                field,
                ..
            } => (s.clone(), *field),
            _ => {
                i += 1;
                continue;
            }
        };
        let store = matches!(
            &vinstrs[i + 1],
            VInstr::Mov {
                dir: MovDir::DstFromAcc,
                ..
            }
        );
        if !store || del.contains(&i) {
            i += 1;
            continue;
        }
        // acc-liveness: scan from i+2 for the first instr that touches acc.
        let mut acc_dead = true;
        for vj in &vinstrs[i + 2..] {
            if writes_acc_fresh(vj) {
                acc_dead = true;
                break;
            }
            if reads_acc(vj) {
                acc_dead = false;
                break;
            }
            // DstFromSrc doesn't touch acc — keep scanning.
        }
        if !acc_dead {
            i += 1;
            continue;
        }
        // codex-R3 guard: never fuse into a self-read/self-define. If the load source is
        // `Value(x)` and the store defines that same `x` (cell x <- cell x), the fused
        // `DstFromSrc Cell(x) <- Value(x)` would both define and read `x` at one instr,
        // and placement (keyed by `(instr, ValueId)`) could resolve the read to the
        // freshly-defined cell. Skip it.
        if let VirtualOp::Value(x) = &load_src {
            if vinstrs[i + 1].defines() == Some(*x) {
                i += 1;
                continue;
            }
        }
        // Rewrite the store (i+1) into `DstFromSrc(dst <- load_src)`; delete the load (i).
        // `dst`/`defines` on the store are unchanged; only dir/src/field/is_dram_read move.
        if let VInstr::Mov {
            dir,
            field,
            src,
            is_dram_read,
            ..
        } = &mut vinstrs[i + 1]
        {
            *dir = MovDir::DstFromSrc;
            *field = load_field;
            *src = Some(load_src);
            *is_dram_read = false; // a copy, not a fold DRAM read
        }
        del.insert(i);
        i += 2;
    }
    let changed = !del.is_empty();
    delete_indices(vinstrs, step_of, &del);
    changed
}

/// F4 (+ spill-immediate-reload): delete a `Mov AccFromSrc Value(v)` whose acc-before is
/// already `Value(v)` — the reload is a no-op. General redundant-reload elimination.
fn drop_redundant_reloads(vinstrs: &mut Vec<VInstr>, step_of: &mut Vec<usize>) -> bool {
    let ab = acc_before(vinstrs);
    let mut del: BTreeSet<usize> = BTreeSet::new();
    for (i, vi) in vinstrs.iter().enumerate() {
        if let VInstr::Mov {
            dir: MovDir::AccFromSrc,
            src: Some(VirtualOp::Value(v)),
            ..
        } = vi
        {
            if ab[i] == AccVal::Value(*v) {
                del.insert(i);
            }
        }
    }
    let changed = !del.is_empty();
    delete_indices(vinstrs, step_of, &del);
    changed
}

/// Optimize the lowered stream via a fixpoint of the rewrite rules.
pub(crate) fn optimize_vinstrs(
    mut vinstrs: Vec<VInstr>,
    mut step_of: Vec<usize>,
) -> (Vec<VInstr>, Vec<usize>) {
    debug_assert_eq!(
        vinstrs.len(),
        step_of.len(),
        "step_of must parallel vinstrs"
    );
    loop {
        let mut changed = false;
        changed |= fuse_leaf_loads(&mut vinstrs, &mut step_of);
        changed |= drop_redundant_reloads(&mut vinstrs, &mut step_of);
        if !changed {
            break;
        }
    }
    debug_assert_eq!(vinstrs.len(), step_of.len());
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

    fn mov_load_global(slot: u8, col: u16) -> VInstr {
        VInstr::Mov {
            dir: MovDir::AccFromSrc,
            field: OperandField::Base,
            dst: None,
            src: Some(VirtualOp::Global { slot, col }),
            defines: None,
            is_dram_read: true,
        }
    }

    #[test]
    fn f1_fuses_leaf_load_when_acc_dead_after_store() {
        let v = ExprId(5);
        // acc <- GLOBAL; cellv <- acc; acc <- GLOBAL2  (third overwrites acc => leaf value dead)
        let mut vinstrs = vec![mov_load_global(2, 4), mov_store(v), mov_load_global(2, 2)];
        let mut step_of = vec![0, 0, 0];
        let changed = fuse_leaf_loads(&mut vinstrs, &mut step_of);
        assert!(changed);
        assert_eq!(vinstrs.len(), 2); // load+store fused into one
        assert_eq!(step_of.len(), 2);
        // first instr is now DstFromSrc cellv <- GLOBAL
        match &vinstrs[0] {
            VInstr::Mov {
                dir: MovDir::DstFromSrc,
                dst: Some(VDst::Cell(w)),
                src: Some(VirtualOp::Global { slot, col }),
                ..
            } => {
                assert_eq!(*w, v);
                assert_eq!((*slot, *col), (2, 4));
            }
            other => panic!("expected fused DstFromSrc, got {other:?}"),
        }
    }

    #[test]
    fn f1_does_not_fuse_when_acc_read_after_store() {
        let v = ExprId(5);
        // acc <- GLOBAL; cellv <- acc; MUL acc *= something  (MUL reads acc => leaf value live)
        let mut vinstrs = vec![
            mov_load_global(2, 4),
            mov_store(v),
            VInstr::Mul {
                field: OperandField::Base,
                reads: vec![VirtualOp::Ldc {
                    sub: crate::fwd::isa::LdcSub::Const,
                    idx: 0,
                }],
                defines: None,
                is_dram_read: false,
            },
        ];
        let mut step_of = vec![0, 0, 0];
        let changed = fuse_leaf_loads(&mut vinstrs, &mut step_of);
        assert!(!changed);
        assert_eq!(vinstrs.len(), 3);
    }

    #[test]
    fn f1_skips_self_define_value_copy() {
        // acc <- Value(v); cellv <- acc; acc <- GLOBAL  — fusing would make
        // `DstFromSrc Cell(v) <- Value(v)` (self read+define). Must NOT fuse.
        let v = ExprId(5);
        let mut vinstrs = vec![mov_load(v), mov_store(v), mov_load_global(2, 2)];
        let mut step_of = vec![0, 0, 0];
        let changed = fuse_leaf_loads(&mut vinstrs, &mut step_of);
        assert!(!changed, "self-define Value(v)->Cell(v) copy must not fuse");
        assert_eq!(vinstrs.len(), 3);
    }

    #[test]
    fn f1_fuses_value_copy_to_different_cell() {
        // acc <- Value(w); cellv <- acc; acc <- GLOBAL  (w != v) — safe cell->cell copy.
        let (v, w) = (ExprId(5), ExprId(6));
        let mut vinstrs = vec![mov_load(w), mov_store(v), mov_load_global(2, 2)];
        let mut step_of = vec![0, 0, 0];
        let changed = fuse_leaf_loads(&mut vinstrs, &mut step_of);
        assert!(changed);
        assert_eq!(vinstrs.len(), 2);
        match &vinstrs[0] {
            VInstr::Mov {
                dir: MovDir::DstFromSrc,
                dst: Some(VDst::Cell(d)),
                src: Some(VirtualOp::Value(s)),
                ..
            } => {
                assert_eq!((*d, *s), (v, w));
            }
            other => panic!("expected DstFromSrc Cell(v)<-Value(w), got {other:?}"),
        }
    }

    #[test]
    fn identity_optimize_preserves_stream_and_lockstep() {
        // Neither F1 nor F4 applies: a leaf load into acc not immediately followed by a
        // store (so F1's adjacency doesn't match), followed by an arithmetic op that reads
        // acc but isn't an `AccFromSrc(Value)` reload (so F4 doesn't match either). Note:
        // `[mov_store(v), mov_load(v)]` is NOT an identity input anymore — F4 correctly
        // deletes the redundant reload there (see `f4_deletes_reload_of_value_already_in_acc`).
        let vinstrs = vec![
            mov_load_global(2, 4),
            VInstr::Mul {
                field: OperandField::Base,
                reads: vec![VirtualOp::Ldc {
                    sub: crate::fwd::isa::LdcSub::Const,
                    idx: 0,
                }],
                defines: None,
                is_dram_read: false,
            },
        ];
        let step_of = vec![0, 1];
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

    #[test]
    fn f4_deletes_reload_of_value_already_in_acc() {
        let v = ExprId(3);
        // cellv <- acc (acc now aliases v); acc <- v  => second is redundant
        let mut vinstrs = vec![mov_store(v), mov_load(v)];
        let mut step_of = vec![0, 0];
        let changed = drop_redundant_reloads(&mut vinstrs, &mut step_of);
        assert!(changed);
        assert_eq!(vinstrs.len(), 1);
        assert!(matches!(
            vinstrs[0],
            VInstr::Mov {
                dir: MovDir::DstFromAcc,
                ..
            }
        ));
    }

    #[test]
    fn f4_keeps_reload_when_acc_holds_other_value() {
        let (v, w) = (ExprId(3), ExprId(4));
        let mut vinstrs = vec![mov_store(v), mov_load(w)]; // acc=v, then reload w — needed
        let mut step_of = vec![0, 0];
        let changed = drop_redundant_reloads(&mut vinstrs, &mut step_of);
        assert!(!changed);
        assert_eq!(vinstrs.len(), 2);
    }
}
