//! Pre-placement VInstr peephole optimizer (spec: emitter codegen-quality pass).
//! Runs after `lower_layer_virtual`, before the `widths` scan / placement in
//! `compile_layer`. Every rewrite is value-preserving; placement re-derives liveness
//! from the rewritten stream. Rules: F1 leaf-fuse, F4/redundant-reload, F2 commute,
//! F5 dead-admission (added in later tasks). This task is the scaffold + acc model.

use std::collections::BTreeSet;

use cs::gkr_compiler::dag_ir::ExprId;

use super::lower::{VDst, VInstr};
use super::place::{ValueId, VirtualOp};
use crate::fwd::isa::{MovDir, Sign};

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

/// F7: reused resolution-peek cache root. The lowering emits a peek cache root as a
/// direct source materialize (`DstFromSrc GlobalMaterialize <- Special{peek}`), then —
/// because the peek value also feeds a consumer — seeds acc from the SAME peek
/// (`AccFromSrc <- Special{peek}`), reading the device-memory resolution array TWICE.
/// A *computed* cache value never does this: it is produced into acc and materialized
/// from acc (`compile_expr_virtual`). Make the peek match that shape — hoist the acc load
/// ahead of the materialize and source the cache write from acc:
///   `DstFromSrc G<-PEEK ; AccFromSrc acc<-PEEK`  →  `AccFromSrc acc<-PEEK ; DstFromAcc G<-acc`
/// One peek instead of two; the value lands in acc for the consumer, exactly as a
/// computed value would. Instruction count is unchanged (a reorder + a dir flip), so this
/// only trims `special_gathers`, never `dram_traffic`. Restricted to `Special` sources —
/// the only re-readable operand that materializes a cache root this way in the corpus.
fn hoist_reused_peek_materialize(vinstrs: &mut Vec<VInstr>, step_of: &mut Vec<usize>) -> bool {
    let mut changed = false;
    let mut i = 0usize;
    while i + 1 < vinstrs.len() {
        // [i] must be a direct-from-peek materialize to a committed backing.
        let mat = match &vinstrs[i] {
            VInstr::Mov {
                dir: MovDir::DstFromSrc,
                field,
                dst: Some(VDst::GlobalMaterialize { slot, col }),
                src: Some(VirtualOp::Special { desc }),
                ..
            } => Some((*field, *slot, *col, *desc)),
            _ => None,
        };
        let Some((field, slot, col, mat_desc)) = mat else {
            i += 1;
            continue;
        };
        // [i+1] must seed acc from the SAME peek (the reuse).
        let reuse = matches!(
            &vinstrs[i + 1],
            VInstr::Mov { dir: MovDir::AccFromSrc, src: Some(VirtualOp::Special { desc }), .. }
                if *desc == mat_desc
        );
        if !reuse {
            i += 1;
            continue;
        }
        // Reorder: the acc load moves up (now at i), the materialize sources from acc (at i+1).
        vinstrs[i] = vinstrs[i + 1].clone();
        vinstrs[i + 1] = VInstr::Mov {
            dir: MovDir::DstFromAcc,
            field,
            dst: Some(VDst::GlobalMaterialize { slot, col }),
            src: None,
            defines: None,
            is_dram_read: false,
        };
        step_of.swap(i, i + 1);
        changed = true;
        i += 2;
    }
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

/// True if `vi` reads `v` as a `VirtualOp::Value` operand.
fn reads_value(vi: &VInstr, v: ValueId) -> bool {
    let hit = |op: &VirtualOp| matches!(op, VirtualOp::Value(w) if *w == v);
    match vi {
        VInstr::Add { reads, .. } | VInstr::Mul { reads, .. } => reads.iter().any(hit),
        VInstr::Fma { pairs, .. } => pairs.iter().any(|(l, r)| hit(l) || hit(r)),
        VInstr::Mov { src, .. } => src.as_ref().is_some_and(hit),
    }
}

/// Number of times `vi` reads `Value(v)` as an operand (occurrence count, not a bool).
/// Mirrors `reads_value`'s positions: `Mov.src`, `Add`/`Mul.reads`, `Fma.pairs` (both sides).
fn count_value_reads(vi: &VInstr, v: ValueId) -> usize {
    let is_v = |op: &VirtualOp| matches!(op, VirtualOp::Value(x) if *x == v);
    match vi {
        VInstr::Add { reads, .. } | VInstr::Mul { reads, .. } => {
            reads.iter().filter(|o| is_v(o)).count()
        }
        VInstr::Fma { pairs, .. } => pairs
            .iter()
            .map(|(l, r)| is_v(l) as usize + is_v(r) as usize)
            .sum(),
        VInstr::Mov { src, .. } => src.as_ref().map_or(0, |o| is_v(o) as usize),
    }
}

/// Is `v` read (as a Value) at any index in `from..` before it is redefined?
fn value_read_after(vinstrs: &[VInstr], from: usize, v: ValueId) -> bool {
    for vj in &vinstrs[from..] {
        if reads_value(vj, v) {
            return true;
        }
        if vj.defines() == Some(v) {
            return false; // redefined before any read → the earlier def is dead
        }
    }
    false
}

/// F5: drop a cell-defining MOV whose value is never read before redefine/end.
/// Precondition (codex-R6): the deleted instruction must not establish the current
/// accumulator for a following op — safe for `DstFromAcc(Cell)` (acc unchanged) and
/// `DstFromSrc(Cell, src)` (acc untouched); those are the only shapes that `defines` a
/// cell without loading acc. An `AccFromSrc` never defines a cell, so it is never a
/// candidate here. Run AFTER F1 fusion so the shape is settled.
///
/// ASSUMPTION (codex-R7): a value's only consumers are `VInstr` reads — incl. final-sweep
/// `DstFromSrc(GlobalMaterialize) <- Value(v)`, which `value_read_after` counts (Mov `src`
/// is scanned). Root outputs live in `vinstrs` as materialize MOVs, not in the separate
/// `vouts` channel — Task 5 made this STRUCTURAL: `VirtualRootOutput` has no smem-cell
/// variant (spec §3 write-through-only stores), so no root output can name a cell whose
/// sole define this pass might drop.
fn drop_dead_admissions(vinstrs: &mut Vec<VInstr>, step_of: &mut Vec<usize>) -> bool {
    let mut del: BTreeSet<usize> = BTreeSet::new();
    for i in 0..vinstrs.len() {
        let is_cell_def = matches!(
            &vinstrs[i],
            VInstr::Mov {
                dir: MovDir::DstFromAcc | MovDir::DstFromSrc,
                dst: Some(VDst::Cell(_)),
                ..
            }
        );
        if !is_cell_def {
            continue;
        }
        let v = match vinstrs[i].defines() {
            Some(v) => v,
            None => continue,
        };
        if !value_read_after(vinstrs, i + 1, v) {
            del.insert(i);
        }
    }
    let changed = !del.is_empty();
    delete_indices(vinstrs, step_of, &del);
    changed
}

/// Can `vi` (the consumer at i+1) commute an operand with the accumulator seed?
/// Mul: always. Add: only the Plus sign. Fma/minus-Add: no.
fn op_commutes_with_seed(vi: &VInstr) -> bool {
    matches!(vi, VInstr::Mul { .. })
        || matches!(
            vi,
            VInstr::Add {
                sign: Sign::Plus,
                ..
            }
        )
}

/// Replace the first `Value(from)` operand of `vi` with `Value(to)`. Returns true on hit.
fn retarget_value_operand(vi: &mut VInstr, from: ValueId, to: ValueId) -> bool {
    let repl = |op: &mut VirtualOp| -> bool {
        if matches!(op, VirtualOp::Value(x) if *x == from) {
            *op = VirtualOp::Value(to);
            true
        } else {
            false
        }
    };
    match vi {
        VInstr::Add { reads, .. } | VInstr::Mul { reads, .. } => {
            for op in reads.iter_mut() {
                if repl(op) {
                    return true;
                }
            }
            false
        }
        _ => false, // only Add/Mul are commuted here
    }
}

/// F2 (adjacent, sign-aware): `AccFromSrc Value(w); <commuting op reads Value(v)>` with
/// `acc_before[reload] == Value(v)` → delete the reload and retarget the op's `Value(v)`
/// operand to `Value(w)`. Acc keeps `v`; the op consumes `w` instead. No new ISA operand.
fn commute_keep_in_acc(vinstrs: &mut Vec<VInstr>, step_of: &mut Vec<usize>) -> bool {
    let ab = acc_before(vinstrs);
    let mut del: BTreeSet<usize> = BTreeSet::new();
    let mut i = 0usize;
    while i + 1 < vinstrs.len() {
        if del.contains(&i) {
            i += 1;
            continue;
        }
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
        } // that's F4's job
        // Defensive (codex answer #5): only commute into a consumer that produces no
        // named value (all current Add/Mul folds have `defines: None`; guards against a
        // future arith-defining VInstr whose def identity we'd have to preserve).
        if vinstrs[i + 1].defines().is_some()
            || !op_commutes_with_seed(&vinstrs[i + 1])
            || !reads_value(&vinstrs[i + 1], v)
        {
            i += 1;
            continue;
        }
        if retarget_value_operand(&mut vinstrs[i + 1], v, w) {
            del.insert(i);
            i += 2;
        } else {
            i += 1;
        }
    }
    let changed = !del.is_empty();
    delete_indices(vinstrs, step_of, &del);
    changed
}

/// Replace the first `Value(from)` operand of `vi` (in ANY position) with `to`. Mirrors
/// `reads_value`'s position enumeration: `Mov.src`, `Add`/`Mul.reads`, `Fma.pairs` (both
/// sides). For a `Mov` src, also refreshes `is_dram_read` for the new source (inert
/// metadata, kept consistent). Returns true on a hit.
fn retarget_value_to_op(vi: &mut VInstr, from: ValueId, to: &VirtualOp) -> bool {
    let is_from = |op: &VirtualOp| matches!(op, VirtualOp::Value(x) if *x == from);
    match vi {
        VInstr::Mov { src, is_dram_read, .. } => {
            if src.as_ref().is_some_and(is_from) {
                *src = Some(to.clone());
                *is_dram_read = matches!(to, VirtualOp::Global { .. });
                true
            } else {
                false
            }
        }
        VInstr::Add { reads, .. } | VInstr::Mul { reads, .. } => {
            for op in reads.iter_mut() {
                if is_from(op) {
                    *op = to.clone();
                    return true;
                }
            }
            false
        }
        VInstr::Fma { pairs, .. } => {
            for (l, r) in pairs.iter_mut() {
                if is_from(l) {
                    *l = to.clone();
                    return true;
                }
                if is_from(r) {
                    *r = to.clone();
                    return true;
                }
            }
            false
        }
    }
}

/// F6: a leaf-copy define `DstFromSrc(Cell(v) <- leaf-src)` (leaf-src in
/// `Global`/`Special`/`Ldc`) whose value `v` is read EXACTLY ONCE anywhere in the program
/// → propagate that sole read to the leaf source (any operand position), leaving the define
/// dead for `drop_dead_admissions` (F5) to reclaim in the same fixpoint pass. Leaf sources
/// are immutable within a layer (value-identical re-read); the single-read gate keeps
/// source-reads flat (traffic-neutral). Cell-to-cell (`Value` src) and `DstFromAcc` spills
/// have no immutable re-readable source and are excluded. F6 itself does not delete (no
/// `step_of` change here); F5 performs the lockstep deletion.
fn propagate_single_use_leaf_copies(vinstrs: &mut Vec<VInstr>, step_of: &mut Vec<usize>) -> bool {
    // Collect leaf-copy defines: (def_idx, v, leaf op).
    let mut leaf_copies: Vec<(usize, ValueId, VirtualOp)> = Vec::new();
    for (i, vi) in vinstrs.iter().enumerate() {
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
                leaf_copies.push((i, *v, op.clone()));
            }
        }
    }
    let mut changed = false;
    for (def_idx, v, op) in leaf_copies {
        // Count OCCURRENCES of Value(v) across the whole program (not instructions that read
        // it); capture the sole reader index. A single instruction can read `Value(v)` in
        // two operand positions (e.g. `Fma` computing v*v), which must NOT count as
        // single-use — propagating both would double a Global's DRAM read (traffic-neutrality,
        // reviewer-caught).
        let mut reader: Option<usize> = None;
        let mut count = 0usize;
        for (k, vk) in vinstrs.iter().enumerate() {
            if k == def_idx {
                continue; // the define's src is `op`, not Value(v)
            }
            let n = count_value_reads(vk, v);
            if n > 0 {
                count += n;
                reader = Some(k);
                if count > 1 {
                    break;
                }
            }
        }
        if count != 1 {
            continue;
        }
        let j = reader.expect("count == 1 implies a reader");
        if retarget_value_to_op(&mut vinstrs[j], v, &op) {
            changed = true;
        }
    }
    let _ = step_of; // F6 retargets only; F5 reclaims the dead defines (lockstep delete there)
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
        changed |= hoist_reused_peek_materialize(&mut vinstrs, &mut step_of);
        changed |= fuse_leaf_loads(&mut vinstrs, &mut step_of);
        changed |= drop_redundant_reloads(&mut vinstrs, &mut step_of);
        changed |= commute_keep_in_acc(&mut vinstrs, &mut step_of);
        changed |= propagate_single_use_leaf_copies(&mut vinstrs, &mut step_of);
        changed |= drop_dead_admissions(&mut vinstrs, &mut step_of);
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
    fn f7_hoists_reused_peek_cache_materialize() {
        use crate::fwd::isa::LdcSub;
        let peek = || VirtualOp::Special { desc: 7 };
        // DstFromSrc cache<-PEEK ; AccFromSrc acc<-PEEK ; Add (reads acc => peek reused)
        let vinstrs = vec![
            VInstr::Mov {
                dir: MovDir::DstFromSrc,
                field: OperandField::Base,
                dst: Some(VDst::GlobalMaterialize { slot: 0, col: 5 }),
                src: Some(peek()),
                defines: None,
                is_dram_read: false,
            },
            VInstr::Mov {
                dir: MovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(peek()),
                defines: None,
                is_dram_read: false,
            },
            VInstr::Add {
                field: OperandField::Ext,
                sign: Sign::Plus,
                reads: vec![VirtualOp::Ldc { sub: LdcSub::ConstChallenge, idx: 0 }],
                defines: Some(ExprId(100)),
                is_dram_read: false,
            },
        ];
        let (out, step_of) = optimize_vinstrs(vinstrs, vec![0, 0, 0]);
        assert_eq!(out.len(), 3, "F7 reorders, does not delete");
        assert_eq!(step_of.len(), 3);
        // acc is seeded from the peek first, then the cache is materialized FROM ACC.
        assert!(
            matches!(&out[0], VInstr::Mov { dir: MovDir::AccFromSrc, src: Some(VirtualOp::Special { desc: 7 }), .. }),
            "acc load hoisted ahead: {:?}", out[0]
        );
        assert!(
            matches!(&out[1], VInstr::Mov { dir: MovDir::DstFromAcc, dst: Some(VDst::GlobalMaterialize { slot: 0, col: 5 }), src: None, .. }),
            "materialize now sources acc: {:?}", out[1]
        );
        // The resolution is gathered exactly ONCE (was twice).
        let peek_reads = out
            .iter()
            .filter(|vi| matches!(vi, VInstr::Mov { src: Some(VirtualOp::Special { .. }), .. }))
            .count();
        assert_eq!(peek_reads, 1, "resolution array read once, not twice");
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

    #[test]
    fn f5_drops_evict_never_read() {
        let v = ExprId(7);
        // DstFromSrc cellv <- GLOBAL (an admission), never read again -> dead, dropped.
        let mut vinstrs = vec![
            VInstr::Mov {
                dir: MovDir::DstFromSrc,
                field: OperandField::Base,
                dst: Some(VDst::Cell(v)),
                src: Some(VirtualOp::Global { slot: 2, col: 9 }),
                defines: Some(v),
                is_dram_read: false,
            },
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
        let mut step_of = vec![0, 0];
        let changed = drop_dead_admissions(&mut vinstrs, &mut step_of);
        assert!(changed);
        assert_eq!(vinstrs.len(), 1);
        assert!(matches!(vinstrs[0], VInstr::Mul { .. }));
    }

    #[test]
    fn f5_keeps_evict_that_is_read() {
        let v = ExprId(7);
        let mut vinstrs = vec![
            VInstr::Mov {
                dir: MovDir::DstFromSrc,
                field: OperandField::Base,
                dst: Some(VDst::Cell(v)),
                src: Some(VirtualOp::Global { slot: 2, col: 9 }),
                defines: Some(v),
                is_dram_read: false,
            },
            VInstr::Mul {
                field: OperandField::Base,
                reads: vec![VirtualOp::Value(v)],
                defines: None,
                is_dram_read: false,
            },
        ];
        let mut step_of = vec![0, 0];
        let changed = drop_dead_admissions(&mut vinstrs, &mut step_of);
        assert!(!changed);
    }

    #[test]
    fn f2_commutes_mul_to_keep_acc() {
        let (v, w) = (ExprId(1), ExprId(2));
        // acc aliases v (store), reload w, MUL *= v  ->  drop reload, MUL *= w (acc stays v)
        let mut vinstrs = vec![
            mov_store(v), // acc = Value(v)
            mov_load(w),  // reload w
            VInstr::Mul {
                field: OperandField::Base,
                reads: vec![VirtualOp::Value(v)],
                defines: None,
                is_dram_read: false,
            },
        ];
        let mut step_of = vec![0, 0, 0];
        let changed = commute_keep_in_acc(&mut vinstrs, &mut step_of);
        assert!(changed);
        assert_eq!(vinstrs.len(), 2);
        match &vinstrs[1] {
            VInstr::Mul { reads, .. } => assert!(matches!(reads[0], VirtualOp::Value(x) if x == w)),
            other => panic!("expected Mul reads=[w], got {other:?}"),
        }
    }

    #[test]
    fn f2_does_not_commute_minus_add() {
        let (v, w) = (ExprId(1), ExprId(2));
        let mut vinstrs = vec![
            mov_store(v),
            mov_load(w),
            VInstr::Add {
                field: OperandField::Base,
                sign: crate::fwd::isa::Sign::Minus,
                reads: vec![VirtualOp::Value(v)],
                defines: None,
                is_dram_read: false,
            },
        ];
        let mut step_of = vec![0, 0, 0];
        let changed = commute_keep_in_acc(&mut vinstrs, &mut step_of);
        assert!(!changed, "minus-Add must not commute seed with operand");
    }

    fn leaf_copy(v: ValueId, op: VirtualOp) -> VInstr {
        let dram = matches!(op, VirtualOp::Global { .. });
        VInstr::Mov {
            dir: MovDir::DstFromSrc,
            field: OperandField::Base,
            dst: Some(VDst::Cell(v)),
            src: Some(op),
            defines: Some(v),
            is_dram_read: dram,
        }
    }
    fn ldc0() -> VirtualOp {
        VirtualOp::Ldc {
            sub: crate::fwd::isa::LdcSub::Const,
            idx: 0,
        }
    }

    #[test]
    fn f6_propagates_single_use_leaf_copy_acc_reload() {
        let v = ExprId(9);
        // DstFromSrc $cellv <- GLOBAL(2,4) ; AccFromSrc acc <- Value(v)  (v single-use)
        let mut vinstrs = vec![
            leaf_copy(v, VirtualOp::Global { slot: 2, col: 4 }),
            mov_load(v), // AccFromSrc acc <- Value(v)
        ];
        let mut step_of = vec![0, 0];
        let changed = propagate_single_use_leaf_copies(&mut vinstrs, &mut step_of);
        assert!(changed);
        // reader now loads the GLOBAL leaf directly (define is left for F5 to reclaim)
        match &vinstrs[1] {
            VInstr::Mov {
                dir: MovDir::AccFromSrc,
                src: Some(VirtualOp::Global { slot, col }),
                ..
            } => {
                assert_eq!((*slot, *col), (2, 4));
            }
            other => panic!("expected AccFromSrc <- Global, got {other:?}"),
        }
        // Value(v) no longer read anywhere (define at [0] is now dead)
        assert!(!reads_value(&vinstrs[1], v));
    }

    #[test]
    fn f6_propagates_single_use_leaf_copy_into_arith_operand() {
        let v = ExprId(9);
        // DstFromSrc $cellv <- Ldc ; MUL acc *= Value(v)  (v single-use)
        let mut vinstrs = vec![
            leaf_copy(v, ldc0()),
            VInstr::Mul {
                field: OperandField::Base,
                reads: vec![VirtualOp::Value(v)],
                defines: None,
                is_dram_read: false,
            },
        ];
        let mut step_of = vec![0, 0];
        let changed = propagate_single_use_leaf_copies(&mut vinstrs, &mut step_of);
        assert!(changed);
        match &vinstrs[1] {
            VInstr::Mul { reads, .. } => {
                assert!(
                    matches!(reads[0], VirtualOp::Ldc { .. }),
                    "operand should be the Ldc leaf"
                )
            }
            other => panic!("expected Mul reads=[Ldc], got {other:?}"),
        }
    }

    #[test]
    fn f6_keeps_multi_read_leaf_copy() {
        let v = ExprId(9);
        // Value(v) read TWICE (acc reload + Mul operand) → not single-use → no fire
        let mut vinstrs = vec![
            leaf_copy(v, VirtualOp::Global { slot: 2, col: 4 }),
            mov_load(v),
            VInstr::Mul {
                field: OperandField::Base,
                reads: vec![VirtualOp::Value(v)],
                defines: None,
                is_dram_read: false,
            },
        ];
        let mut step_of = vec![0, 0, 0];
        let changed = propagate_single_use_leaf_copies(&mut vinstrs, &mut step_of);
        assert!(!changed, "multi-read leaf copy must keep its cell");
    }

    #[test]
    fn f6_keeps_value_read_twice_in_one_instruction() {
        let v = ExprId(9);
        // DstFromSrc $cellv <- GLOBAL ; MUL acc *= Value(v) * Value(v)  (v read TWICE in one instr = v^2)
        // Occurrence count is 2, so F6 must NOT fire (propagating both would double the Global DRAM read).
        let mut vinstrs = vec![
            leaf_copy(v, VirtualOp::Global { slot: 2, col: 4 }),
            VInstr::Mul {
                field: OperandField::Base,
                reads: vec![VirtualOp::Value(v), VirtualOp::Value(v)],
                defines: None,
                is_dram_read: false,
            },
        ];
        let mut step_of = vec![0, 0];
        let changed = propagate_single_use_leaf_copies(&mut vinstrs, &mut step_of);
        assert!(
            !changed,
            "a value read twice in one instruction is not single-use (would double a Global DRAM read)"
        );
    }

    #[test]
    fn f6_keeps_non_leaf_copy() {
        let (v, w) = (ExprId(9), ExprId(3));
        // DstFromSrc $cellv <- Value(w)  (cell-to-cell, not a leaf source) → no fire
        let mut vinstrs = vec![
            VInstr::Mov {
                dir: MovDir::DstFromSrc,
                field: OperandField::Base,
                dst: Some(VDst::Cell(v)),
                src: Some(VirtualOp::Value(w)),
                defines: Some(v),
                is_dram_read: false,
            },
            mov_load(v),
        ];
        let mut step_of = vec![0, 0];
        let changed = propagate_single_use_leaf_copies(&mut vinstrs, &mut step_of);
        assert!(!changed, "cell-to-cell copy source is not an immutable leaf");
    }

    #[test]
    fn f6_keeps_dstfromacc_cell_define() {
        let v = ExprId(9);
        // DstFromAcc $cellv <- acc (value from acc, no re-readable source) + one read → no fire
        let mut vinstrs = vec![mov_store(v), mov_load(v)];
        let mut step_of = vec![0, 0];
        let changed = propagate_single_use_leaf_copies(&mut vinstrs, &mut step_of);
        assert!(
            !changed,
            "DstFromAcc define has no re-readable source to propagate"
        );
    }

    #[test]
    fn f6_end_to_end_with_f5_reclaims_cell() {
        let v = ExprId(9);
        // Full pass: leaf-copy + sole reload + an acc consumer → F6 propagates, F5 drops define.
        let mut vinstrs = vec![
            leaf_copy(v, VirtualOp::Global { slot: 2, col: 4 }),
            mov_load(v),
            VInstr::Mul {
                field: OperandField::Base,
                reads: vec![ldc0()],
                defines: None,
                is_dram_read: false,
            },
        ];
        let step_of = vec![0, 0, 0];
        let (out, step) = optimize_vinstrs(vinstrs.clone(), step_of);
        assert_eq!(out.len(), 2, "define reclaimed by F5"); // [AccFromSrc<-Global, Mul]
        assert_eq!(step.len(), out.len());
        assert!(matches!(
            &out[0],
            VInstr::Mov {
                dir: MovDir::AccFromSrc,
                src: Some(VirtualOp::Global { slot: 2, col: 4 }),
                ..
            }
        ));
    }

    #[test]
    fn f5_keeps_evict_read_by_global_materialize() {
        // codex-R7: a value consumed ONLY by a later final-sweep materialize
        // (DstFromSrc GlobalMaterialize <- Value(v)) must NOT be dropped.
        let v = ExprId(7);
        let mut vinstrs = vec![
            VInstr::Mov {
                dir: MovDir::DstFromAcc,
                field: OperandField::Base,
                dst: Some(VDst::Cell(v)),
                src: None,
                defines: Some(v),
                is_dram_read: false,
            },
            VInstr::Mov {
                dir: MovDir::DstFromSrc,
                field: OperandField::Base,
                dst: Some(VDst::GlobalMaterialize { slot: 0, col: 8 }),
                src: Some(VirtualOp::Value(v)),
                defines: None,
                is_dram_read: false,
            },
        ];
        let mut step_of = vec![0, 0];
        let changed = drop_dead_admissions(&mut vinstrs, &mut step_of);
        assert!(
            !changed,
            "value read by a final-sweep GlobalMaterialize must be kept"
        );
    }
}
