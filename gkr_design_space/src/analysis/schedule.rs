//! Live-set simulation under different execution orders.
//!
//! Model: every non-constant node (including `Place` loads) occupies one live
//! slot from its schedule position until its last consumer is scheduled;
//! values that only feed output stores release immediately after the store.

use crate::graph::{AnalysisGraph, NodeIdx, Origin};
use cs::gkr_compiler::codegen_ir::Domain;
use serde::Serialize;

#[derive(Clone, Copy, Debug)]
pub enum Order {
    /// Arena (IR emission) order — the codegen baseline.
    Arena,
    /// Best of {greedy list scheduling, arena order} by max-live bytes. A real
    /// scheduler can always keep the baseline order, so the portfolio min is
    /// the honest "what scheduling can achieve" estimate.
    PressureAware,
}

#[derive(Debug, Serialize)]
pub struct LiveStats {
    pub max_live_bf: u32,
    pub max_live_e4: u32,
    pub max_live_bytes: u64,
}

pub fn simulate(g: &AnalysisGraph, order: Order) -> LiveStats {
    let arena = measure(g, &(0..g.nodes.len()).collect::<Vec<_>>());
    match order {
        Order::Arena => arena,
        Order::PressureAware => {
            let greedy = measure(g, &pressure_order(g));
            if greedy.max_live_bytes <= arena.max_live_bytes {
                greedy
            } else {
                arena
            }
        }
    }
}

/// `remaining[i]` = consumers not yet scheduled; a value dies at 0.
fn measure(g: &AnalysisGraph, seq: &[NodeIdx]) -> LiveStats {
    let mut remaining = vec![0u32; g.nodes.len()];
    for n in &g.nodes {
        for &c in &n.children {
            remaining[c] += 1;
        }
    }
    let mut live = vec![false; g.nodes.len()];
    let (mut bf, mut e4, mut bytes) = (0u32, 0u32, 0u64);
    let mut stats = LiveStats {
        max_live_bf: 0,
        max_live_e4: 0,
        max_live_bytes: 0,
    };
    fn kill(
        g: &AnalysisGraph,
        i: NodeIdx,
        live: &mut [bool],
        bf: &mut u32,
        e4: &mut u32,
        bytes: &mut u64,
    ) {
        if std::mem::replace(&mut live[i], false) {
            match g.nodes[i].domain {
                Domain::Base => *bf -= 1,
                Domain::Ext => *e4 -= 1,
            }
            *bytes -= g.nodes[i].width_bytes() as u64;
        }
    }
    for &i in seq {
        if matches!(g.nodes[i].origin, Origin::Constant) {
            continue; // immediates are free
        }
        live[i] = true;
        match g.nodes[i].domain {
            Domain::Base => bf += 1,
            Domain::Ext => e4 += 1,
        }
        bytes += g.nodes[i].width_bytes() as u64;
        stats.max_live_bf = stats.max_live_bf.max(bf);
        stats.max_live_e4 = stats.max_live_e4.max(e4);
        stats.max_live_bytes = stats.max_live_bytes.max(bytes);
        for &c in &g.nodes[i].children {
            remaining[c] -= 1;
            if remaining[c] == 0 {
                kill(g, c, &mut live, &mut bf, &mut e4, &mut bytes);
            }
        }
        if remaining[i] == 0 {
            // value only feeds stores: written out when computed, then dead
            kill(g, i, &mut live, &mut bf, &mut e4, &mut bytes);
        }
    }
    stats
}

fn pressure_order(g: &AnalysisGraph) -> Vec<NodeIdx> {
    let parents = g.parents();
    let n = g.nodes.len();
    let mut unscheduled_children: Vec<usize> = g.nodes.iter().map(|x| x.children.len()).collect();
    let mut remaining = vec![0u32; n];
    for node in &g.nodes {
        for &c in &node.children {
            remaining[c] += 1;
        }
    }
    let mut ready: Vec<NodeIdx> = (0..n).filter(|&i| unscheduled_children[i] == 0).collect();
    let mut seq = Vec::with_capacity(n);
    let mut scheduled = vec![false; n];
    while let Some(pos) = best_ready(g, &ready, &remaining, &parents, &unscheduled_children) {
        let i = ready.swap_remove(pos);
        scheduled[i] = true;
        seq.push(i);
        for &c in &g.nodes[i].children {
            remaining[c] -= 1;
        }
        for &p in &parents[i] {
            unscheduled_children[p] -= 1;
            if unscheduled_children[p] == 0 && !scheduled[p] {
                ready.push(p);
            }
        }
    }
    debug_assert_eq!(seq.len(), n);
    seq
}

/// Primary score: bytes freed (operands at last use) − bytes allocated (the
/// node itself, unless it dies immediately). When forced to grow the live set
/// (all scores negative), prefer the node whose scheduling brings the most
/// nearly-complete consumer closest to ready — this emulates depth-first
/// completion of one expression tree at a time instead of breadth-wise loads.
/// Then smaller width, then FIFO.
fn best_ready(
    g: &AnalysisGraph,
    ready: &[NodeIdx],
    remaining: &[u32],
    parents: &[Vec<NodeIdx>],
    unscheduled_children: &[usize],
) -> Option<usize> {
    ready
        .iter()
        .enumerate()
        .max_by_key(|&(pos, &i)| {
            let freed: i64 = g.nodes[i]
                .children
                .iter()
                .filter(|&&c| remaining[c] == 1)
                .map(|&c| g.nodes[c].width_bytes() as i64)
                .sum();
            let alloc = if remaining[i] == 0 {
                0
            } else {
                g.nodes[i].width_bytes() as i64
            };
            let nearest_parent: usize = parents[i]
                .iter()
                .map(|&p| unscheduled_children[p])
                .min()
                .unwrap_or(usize::MAX);
            (
                freed - alloc,
                std::cmp::Reverse(nearest_parent),
                std::cmp::Reverse(g.nodes[i].width_bytes()),
                std::cmp::Reverse(pos),
            )
        })
        .map(|(pos, _)| pos)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::AnalysisGraph;
    use cs::definitions::GKRAddress;
    use cs::gkr_compiler::codegen_ir::{
        CodegenGate, CodegenLayer, Domain, ExprArena, ExprNode, ForwardSource, GateKind, NodeHints,
        NodeId, OutputSlot, ProducerId,
    };

    /// Arena order loads all 4 places before any sum -> max live 5.
    /// A pressure-aware order (p0,p1,s01, p2,p3,s23, g) peaks at 4.
    fn wide_layer() -> CodegenLayer {
        let p = |i: usize| ExprNode::Place {
            addr: GKRAddress::BaseLayerWitness(i),
            domain: Domain::Base,
        };
        let nodes = vec![
            p(0),
            p(1),
            p(2),
            p(3),
            ExprNode::Sum {
                terms: vec![NodeId(0), NodeId(1)],
                domain: Domain::Base,
            },
            ExprNode::Sum {
                terms: vec![NodeId(2), NodeId(3)],
                domain: Domain::Base,
            },
            ExprNode::GateOutput {
                producer: ProducerId::Gate(0),
                out: 0,
                domain: Domain::Base,
            },
        ];
        let hints = nodes
            .iter()
            .map(|_| NodeHints {
                uses: 0,
                footprint: vec![],
            })
            .collect();
        CodegenLayer {
            arena: ExprArena { nodes, hints },
            gates_external: vec![],
            gates: vec![CodegenGate {
                kind: GateKind::TrivialProduct {
                    input: [NodeId(4), NodeId(5)],
                },
                dst: vec![OutputSlot {
                    node: NodeId(6),
                    addr: GKRAddress::InnerLayer {
                        layer: 1,
                        offset: 0,
                    },
                    forward_source: ForwardSource::Computed,
                }],
                batch_terms: vec![],
                num_challenges: 1,
            }],
            caches: vec![],
            intermediate_layer_width: None,
        }
    }

    #[test]
    fn pressure_aware_beats_arena_order() {
        let g = AnalysisGraph::from_layer(&wide_layer());
        let arena = simulate(&g, Order::Arena);
        let scheduled = simulate(&g, Order::PressureAware);
        assert_eq!(arena.max_live_bf, 5);
        assert!(scheduled.max_live_bf <= 4, "got {}", scheduled.max_live_bf);
        assert!(scheduled.max_live_bytes < arena.max_live_bytes);
    }
}
