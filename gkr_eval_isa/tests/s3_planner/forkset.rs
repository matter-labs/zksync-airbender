//! Node classification, cone structure, and Sethi-Ullman cone peaks over an
//! `OracleInstance`. Pure; no oracle, no RNG. Mirrors solve.py's `_cone_peaks`
//! and cone-set logic so the planner shares the oracle's cost model.

use crate::s3_gap::instance::{NodeKind, OracleInstance};

/// Sorted node ids reachable from `root` via `children`, including `root`.
pub fn cone(inst: &OracleInstance, root: u32) -> Vec<u32> {
    let mut seen = vec![false; inst.nodes.len()];
    let mut stack = vec![root];
    while let Some(v) = stack.pop() {
        if seen[v as usize] { continue; }
        seen[v as usize] = true;
        for &c in &inst.nodes[v as usize].children {
            if !seen[c as usize] { stack.push(c); }
        }
    }
    (0..inst.nodes.len() as u32).filter(|&v| seen[v as usize]).collect()
}

/// Distinct real-DRAM node ids inside `cone(root)`.
pub fn cone_dram_leaves(inst: &OracleInstance, root: u32) -> Vec<u32> {
    cone(inst, root).into_iter().filter(|&v| inst.nodes[v as usize].real_dram).collect()
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
    let is_fork: Vec<bool> = inst.nodes.iter()
        .map(|node| matches!(node.kind, NodeKind::Add | NodeKind::Mul) && consumers[node.id as usize] >= 2)
        .collect();
    let forks: Vec<u32> = (0..n as u32).filter(|&v| is_fork[v as usize]).collect();

    // Sethi-Ullman peak; topo order (child < parent) => one ascending pass fills children first.
    let mut peak = vec![0u32; n];
    for v in 0..n {
        let node = &inst.nodes[v];
        if node.children.is_empty() {
            peak[v] = node.width as u32;
        } else {
            let mut ps: Vec<u32> = node.children.iter().map(|&c| peak[c as usize]).collect();
            ps.sort_unstable_by(|a, b| b.cmp(a));
            let second = ps.get(1).copied().unwrap_or(0);
            peak[v] = ps[0].max(node.width as u32 + second);
        }
    }
    let root_peak: Vec<u32> = inst.roots.iter().map(|&r| peak[r as usize]).collect();
    ForkInfo { consumers, is_fork, forks, peak, root_peak }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::s3_gap::instance::{NodeKind, OracleInstance, OracleNode};

    pub(super) fn n(id: u32, kind: NodeKind, width: u8, real_dram: bool, children: Vec<u32>) -> OracleNode {
        OracleNode { id, kind, width, real_dram, children }
    }

    // Add(root=3) over two ext Reads (4,4) and one base Read (1).
    pub(super) fn three_read_add() -> OracleInstance {
        OracleInstance {
            budget: 16,
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
    fn analyze_sethi_ullman_peak_three_ext_add() {
        let inst = three_read_add();
        let fi = analyze(&inst);
        assert_eq!(fi.peak[3], 8);     // 4 (width) + 4 (2nd-largest child peak) = 8
        assert_eq!(fi.root_peak, vec![8]);
    }
}
