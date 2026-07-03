//! Node classification, cone structure, and Sethi-Ullman cone peaks over an
//! `OracleInstance`. Pure; no oracle, no RNG. Mirrors solve.py's `_cone_peaks`
//! and cone-set logic so the planner shares the oracle's cost model.

use crate::s3_gap::instance::{NodeKind, OracleInstance};

/// Sorted node ids reachable from `root` via `children`, including `root`.
pub fn cone(inst: &OracleInstance, root: u32) -> Vec<u32> {
    let mut seen = vec![false; inst.nodes.len()];
    let mut stack = vec![root];
    while let Some(v) = stack.pop() {
        if seen[v as usize] {
            continue;
        }
        seen[v as usize] = true;
        for &c in &inst.nodes[v as usize].children {
            if !seen[c as usize] {
                stack.push(c);
            }
        }
    }
    (0..inst.nodes.len() as u32)
        .filter(|&v| seen[v as usize])
        .collect()
}

/// Distinct real-DRAM node ids inside `cone(root)`.
pub fn cone_dram_leaves(inst: &OracleInstance, root: u32) -> Vec<u32> {
    cone(inst, root)
        .into_iter()
        .filter(|&v| inst.nodes[v as usize].real_dram)
        .collect()
}

pub struct ForkInfo {
    pub consumers: Vec<u32>,
    pub is_fork: Vec<bool>,
    pub forks: Vec<u32>,
    pub peak: Vec<u32>,
    pub root_peak: Vec<u32>,
}

pub fn analyze(inst: &OracleInstance) -> ForkInfo {
    let n = inst.nodes.len();
    let mut consumers = vec![0u32; n];
    for node in &inst.nodes {
        for &c in &node.children {
            consumers[c as usize] += 1;
        }
    }
    // Root materialization is a use (matches the census s3_gap_experiment.rs:632-637).
    for &r in &inst.roots {
        consumers[r as usize] += 1;
    }
    // A fork is a multi-consumer node worth caching to avoid recompute. The
    // recomputable kinds are exactly the ones that cost an instr to produce —
    // Add, Mul, AND Special (a resolution-pruned gather terminal still costs 1
    // instr, mirroring the oracle's `is_recompute`). Excluding Special would force
    // the planner to recompute a shared Special in every consuming cone.
    let is_fork: Vec<bool> = inst
        .nodes
        .iter()
        .map(|node| {
            matches!(
                node.kind,
                NodeKind::Add | NodeKind::Mul | NodeKind::Special
            ) && consumers[node.id as usize] >= 2
        })
        .collect();
    let forks: Vec<u32> = (0..n as u32).filter(|&v| is_fork[v as usize]).collect();

    // Cell-budget peak under the single-accumulator streaming machine model:
    //   * one accumulator register, SEPARATE from the cell budget (free);
    //   * a leaf operand (Read/VirtualSetup/Special) streams directly from DRAM /
    //     the resolver into the fold — it never occupies cache;
    //   * a `Mul` whose operands all stream fuses as one FMA term (product is free),
    //     so it also streams; an `Add` is a sum that needs its own accumulator pass;
    //   * the result streams to its destination (cache only if deliberately kept
    //     resident — a residency decision, not part of this compute peak).
    // The only cache pressure during a cone is spilling the accumulator's partial
    // (width(v) cells, traffic-free) when a child needs its own accumulator pass: the
    // first such child is computed before the partial exists (no spill); each later
    // one costs width(v) on top of its own peak. Topo order (child < parent) lets one
    // ascending pass fill children first.
    let mut streamable = vec![false; n];
    let mut peak = vec![0u32; n];
    for v in 0..n {
        let node = &inst.nodes[v];
        if node.children.is_empty() {
            // Leaf: streams, occupies no cache.
            streamable[v] = true;
            peak[v] = 0;
            continue;
        }
        streamable[v] = matches!(node.kind, NodeKind::Mul)
            && node.children.iter().all(|&c| streamable[c as usize]);
        // Children that cannot stream force their own accumulator pass.
        let mut fold_peaks: Vec<u32> = node
            .children
            .iter()
            .filter(|&&c| !streamable[c as usize])
            .map(|&c| peak[c as usize])
            .collect();
        peak[v] = if fold_peaks.is_empty() {
            0
        } else if fold_peaks.len() == 1 {
            fold_peaks[0]
        } else {
            fold_peaks.sort_unstable_by(|a, b| b.cmp(a));
            fold_peaks[0].max(node.width as u32 + fold_peaks[1])
        };
    }
    let root_peak: Vec<u32> = inst.roots.iter().map(|&r| peak[r as usize]).collect();
    ForkInfo {
        consumers,
        is_fork,
        forks,
        peak,
        root_peak,
    }
}

/// Residency-aware cone peak. Identical to the `peak` computed in `analyze`
/// EXCEPT that every `cached[v]` value is a streaming LEAF (peak 0, streamable)
/// in its CONSUMERS' cones — it is read from a cell, 0 transient — while its OWN
/// entry `peak[v]` still holds the Sethi-Ullman peak of PRODUCING it
/// (`Mul(x,y)`→cell) with its factors handled normally. `cached[v] == resident[v]`.
/// Length == `inst.nodes.len()`; `peak_with_cached(inst, &vec![false; n]) ==
/// analyze(inst).peak` (the no-cache identity).
pub fn peak_with_cached(inst: &OracleInstance, cached: &[bool]) -> Vec<u32> {
    let n = inst.nodes.len();
    let mut streamable = vec![false; n];
    let mut peak = vec![0u32; n];
    for v in 0..n {
        let node = &inst.nodes[v];
        if node.children.is_empty() {
            streamable[v] = true;
            peak[v] = 0;
            continue;
        }
        // ── unchanged fold recurrence (its OWN production peak) ──────────────
        // Children that cannot stream force their own accumulator pass. This
        // filters CHILDREN's `streamable` only — never `v`'s own — so computing
        // it before `streamable[v]` (the reorder vs `analyze`) is behavior-
        // preserving for the non-cached case.
        let mut fold_peaks: Vec<u32> = node
            .children
            .iter()
            .filter(|&&c| !streamable[c as usize])
            .map(|&c| peak[c as usize])
            .collect();
        peak[v] = if fold_peaks.is_empty() {
            0
        } else if fold_peaks.len() == 1 {
            fold_peaks[0]
        } else {
            fold_peaks.sort_unstable_by(|a, b| b.cmp(a));
            fold_peaks[0].max(node.width as u32 + fold_peaks[1])
        };
        // ── ONLY change vs `analyze`: a cached node is a 0-transient leaf for
        //    its consumers (regardless of kind); a non-cached node keeps the
        //    streaming rule (Mul with all-streamable children fuses). ─────────
        streamable[v] = cached[v]
            || (matches!(node.kind, NodeKind::Mul)
                && node.children.iter().all(|&c| streamable[c as usize]));
    }
    peak
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::s3_gap::instance::{NodeKind, OracleInstance, OracleNode};

    pub(super) fn n(
        id: u32,
        kind: NodeKind,
        width: u8,
        real_dram: bool,
        children: Vec<u32>,
    ) -> OracleNode {
        OracleNode {
            id,
            kind,
            width,
            real_dram,
            children,
        }
    }

    // Add(root=3) over two ext Reads (4,4) and one base Read (1).
    pub(super) fn three_read_add() -> OracleInstance {
        OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![3],
            nodes: vec![
                n(0, NodeKind::Read, 4, true, vec![]),
                n(1, NodeKind::Read, 4, true, vec![]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Add, 4, false, vec![0, 1, 2]),
            ],
        }
    }

    #[test]
    fn cone_includes_root_and_all_reachable() {
        let inst = three_read_add();
        assert_eq!(cone(&inst, 3), vec![0, 1, 2, 3]);
        assert_eq!(cone(&inst, 0), vec![0]);
    }

    #[test]
    fn analyze_counts_consumers_with_root_sink_and_forks() {
        // shared product Mul{0,1}=2 consumed by Add{2,0}=3 and Add{2,1}=4 (both roots).
        let inst = OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![3, 4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Mul, 1, false, vec![0, 1]),
                n(3, NodeKind::Add, 1, false, vec![2, 0]),
                n(4, NodeKind::Add, 1, false, vec![2, 1]),
            ],
        };
        let fi = analyze(&inst);
        // child-edges: 0<-{2,3}, 1<-{2,4}, 2<-{3,4}, 3<-{}, 4<-{}; PLUS root-sink +1 for 3 and 4.
        assert_eq!(fi.consumers, vec![2, 2, 2, 1, 1]);
        assert_eq!(fi.is_fork, vec![false, false, true, false, false]); // only node 2 is a multi-consumer Add/Mul
        assert_eq!(fi.forks, vec![2]);
    }

    #[test]
    fn fold_over_reads_streams_with_zero_peak() {
        // Add over ext/base Reads: every operand streams directly from DRAM into
        // the accumulator (separate register, not in the cell budget), so no operand
        // ever occupies cache. The cone peak is 0 — the cost is pure read traffic.
        let inst = three_read_add();
        let fi = analyze(&inst);
        assert_eq!(fi.peak[3], 0);
        assert_eq!(fi.root_peak, vec![0]);
    }

    #[test]
    fn spill_only_from_the_second_nested_fold() {
        // v = g + h, where g and h are each a fold over reads (peak 0). The single
        // accumulator computes g into itself (no spill), then must spill g's partial
        // (width(v) = 1 cell, traffic-free) to compute h, then re-add. Peak = 1.
        let inst = OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![6],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]), // g, peak 0
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Read, 1, true, vec![]),
                n(5, NodeKind::Add, 1, false, vec![3, 4]), // h, peak 0
                n(6, NodeKind::Add, 1, false, vec![2, 5]), // v, two fold children
            ],
        };
        let fi = analyze(&inst);
        assert_eq!(fi.peak[2], 0);
        assert_eq!(fi.peak[5], 0);
        assert_eq!(fi.peak[6], 1); // max(peak(g)=0, width(v)=1 + peak(h)=0) = 1
    }

    #[test]
    fn single_nested_fold_child_does_not_spill() {
        // v = g + read, g a fold over reads. g is computed first into the acc, then
        // the read streams in — no partial to spill. Peak = peak(g) = 0.
        let inst = OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]), // g, peak 0
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Add, 1, false, vec![2, 3]), // single fold child
            ],
        };
        let fi = analyze(&inst);
        assert_eq!(fi.peak[4], 0);
    }

    #[test]
    fn fused_mul_child_streams_no_spill() {
        // Add(Mul(read, read), read): the Mul fuses into the parent Add as a single
        // FMA term (`acc += a*b`, product free), so it streams like a leaf and forces
        // no accumulator pass. Peak = 0.
        let inst = OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Mul, 1, false, vec![0, 1]), // streamable product
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Add, 1, false, vec![2, 3]),
            ],
        };
        let fi = analyze(&inst);
        assert_eq!(fi.peak[2], 0); // product of two reads streams
        assert_eq!(fi.peak[4], 0);
    }

    #[test]
    fn nested_spills_stack_one_acc_width_per_level() {
        // Two-level fold-of-folds: v = h1 + h2, each hi = gi1 + gi2 (folds over reads).
        // peak(hi) = 1 (one spill). peak(v) = max(peak(h1)=1, width(v)=1 + peak(h2)=1) = 2.
        let inst = OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![14],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]),
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Read, 1, true, vec![]),
                n(5, NodeKind::Add, 1, false, vec![3, 4]),
                n(6, NodeKind::Add, 1, false, vec![2, 5]), // h1, peak 1
                n(7, NodeKind::Read, 1, true, vec![]),
                n(8, NodeKind::Read, 1, true, vec![]),
                n(9, NodeKind::Add, 1, false, vec![7, 8]),
                n(10, NodeKind::Read, 1, true, vec![]),
                n(11, NodeKind::Read, 1, true, vec![]),
                n(12, NodeKind::Add, 1, false, vec![10, 11]),
                n(13, NodeKind::Add, 1, false, vec![9, 12]), // h2, peak 1
                n(14, NodeKind::Add, 1, false, vec![6, 13]), // v
            ],
        };
        let fi = analyze(&inst);
        assert_eq!(fi.peak[6], 1);
        assert_eq!(fi.peak[13], 1);
        assert_eq!(fi.peak[14], 2);
    }
}
