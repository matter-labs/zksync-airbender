//! Per-layer analysis DAG distilled from `CodegenLayer`.

use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::{
    CodegenLayer, Domain, ExprNode, ForwardSource, ProducerId, gate_kind_input_nodes,
};

pub type NodeIdx = usize;

#[derive(Clone, Debug, PartialEq)]
pub enum Origin {
    Constant,
    /// Place reading a circuit input column (witness/memory/setup/virtual-setup/inner-layer).
    InputColumn(GKRAddress),
    /// Place reading a forward-materialized cache column.
    CachedColumn(GKRAddress),
    /// Place reading scratch space.
    Scratch(GKRAddress),
    /// Sum / Product / GateOutput — computed in-kernel.
    Computed,
}

#[derive(Clone, Debug)]
pub struct ANode {
    pub domain: Domain,
    pub origin: Origin,
    pub children: Vec<NodeIdx>,
    /// Fan-out recomputed from edges + output slots (IR `hints.uses` reported separately).
    pub uses: u32,
}

impl ANode {
    pub fn width_bytes(&self) -> u32 {
        match self.domain {
            Domain::Base => 4,
            Domain::Ext => 16,
        }
    }

    pub fn is_load(&self) -> bool {
        matches!(
            self.origin,
            Origin::InputColumn(_) | Origin::CachedColumn(_) | Origin::Scratch(_)
        )
    }
}

#[derive(Clone, Debug)]
pub struct OutputSlotInfo {
    pub node: NodeIdx,
    pub addr: GKRAddress,
    pub prefill: bool,
    /// True for cache-materialization outputs (no sumcheck claim / no c0 term).
    pub from_cache: bool,
}

pub struct AnalysisGraph {
    pub nodes: Vec<ANode>,
    /// Everything stored to global: gate dst slots + cache outs, in IR order.
    pub outputs: Vec<OutputSlotInfo>,
    /// The IR's own per-node fan-out estimate, for side-by-side reporting.
    pub hints_uses: Vec<u32>,
}

impl AnalysisGraph {
    pub fn from_layer(layer: &CodegenLayer) -> Self {
        let arena = &layer.arena;
        let mut nodes: Vec<ANode> = Vec::with_capacity(arena.nodes.len());
        for (i, n) in arena.nodes.iter().enumerate() {
            let (domain, origin, children) = match n {
                ExprNode::Constant(_) => (Domain::Base, Origin::Constant, vec![]),
                ExprNode::Place { addr, domain } => {
                    let origin = match addr {
                        GKRAddress::Cached { .. } => Origin::CachedColumn(*addr),
                        GKRAddress::ScratchSpace(_) => Origin::Scratch(*addr),
                        _ => Origin::InputColumn(*addr),
                    };
                    (*domain, origin, vec![])
                }
                ExprNode::Sum { terms, domain }
                | ExprNode::Product {
                    factors: terms,
                    domain,
                } => (
                    *domain,
                    Origin::Computed,
                    terms.iter().map(|t| t.0 as NodeIdx).collect(),
                ),
                ExprNode::GateOutput {
                    producer, domain, ..
                } => {
                    let operands: Vec<NodeIdx> = match producer {
                        ProducerId::Gate(g) => {
                            gate_kind_input_nodes(&layer.gates[*g as usize].kind)
                                .iter()
                                .map(|id| id.0 as NodeIdx)
                                .collect()
                        }
                        ProducerId::GateExternal(g) => {
                            gate_kind_input_nodes(&layer.gates_external[*g as usize].kind)
                                .iter()
                                .map(|id| id.0 as NodeIdx)
                                .collect()
                        }
                        ProducerId::Cache(c) => layer.caches[*c as usize]
                            .inputs
                            .iter()
                            .map(|id| id.0 as NodeIdx)
                            .collect(),
                    };
                    (*domain, Origin::Computed, operands)
                }
            };
            // Arena invariant: operands are interned before their consumer.
            debug_assert!(
                children.iter().all(|&c| c < i),
                "non-topological arena edge into node {i}"
            );
            nodes.push(ANode {
                domain,
                origin,
                children,
                uses: 0,
            });
        }

        let mut outputs = Vec::new();
        for gate in layer.gates_external.iter().chain(layer.gates.iter()) {
            for slot in &gate.dst {
                outputs.push(OutputSlotInfo {
                    node: slot.node.0 as NodeIdx,
                    addr: slot.addr,
                    prefill: matches!(slot.forward_source, ForwardSource::ScratchPrefill),
                    from_cache: false,
                });
            }
        }
        for cache in &layer.caches {
            outputs.push(OutputSlotInfo {
                node: cache.out.0.0 as NodeIdx,
                addr: cache.out.1,
                prefill: false,
                from_cache: true,
            });
        }

        let mut uses = vec![0u32; nodes.len()];
        for n in &nodes {
            for &c in &n.children {
                uses[c] += 1;
            }
        }
        for o in &outputs {
            uses[o.node] += 1;
        }
        for (n, u) in nodes.iter_mut().zip(&uses) {
            n.uses = *u;
        }

        let hints_uses = arena.hints.iter().map(|h| h.uses).collect();
        AnalysisGraph {
            nodes,
            outputs,
            hints_uses,
        }
    }

    /// Reverse edges, computed on demand by passes that need them.
    pub fn parents(&self) -> Vec<Vec<NodeIdx>> {
        let mut parents = vec![Vec::new(); self.nodes.len()];
        for (i, n) in self.nodes.iter().enumerate() {
            for &c in &n.children {
                parents[c].push(i);
            }
        }
        parents
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use cs::gkr_compiler::codegen_ir::{
        CodegenGate, ExprArena, GateKind, NodeHints, NodeId, OutputSlot,
    };

    /// p0 + p1 summed in base, multiplied with a cached ext column by one
    /// TrivialProduct gate whose output is stored to the next layer.
    pub(crate) fn mini_layer() -> CodegenLayer {
        let nodes = vec![
            ExprNode::Place {
                addr: GKRAddress::BaseLayerWitness(0),
                domain: Domain::Base,
            },
            ExprNode::Place {
                addr: GKRAddress::BaseLayerWitness(1),
                domain: Domain::Base,
            },
            ExprNode::Sum {
                terms: vec![NodeId(0), NodeId(1)],
                domain: Domain::Base,
            },
            ExprNode::Place {
                addr: GKRAddress::Cached {
                    layer: 0,
                    offset: 0,
                },
                domain: Domain::Ext,
            },
            ExprNode::GateOutput {
                producer: ProducerId::Gate(0),
                out: 0,
                domain: Domain::Ext,
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
                    input: [NodeId(2), NodeId(3)],
                },
                dst: vec![OutputSlot {
                    node: NodeId(4),
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
    fn builds_edges_origins_and_uses() {
        let g = AnalysisGraph::from_layer(&mini_layer());
        assert_eq!(g.nodes.len(), 5);
        assert_eq!(g.nodes[2].children, vec![0, 1]);
        assert_eq!(g.nodes[4].children, vec![2, 3]); // via gate_kind_input_nodes
        assert!(matches!(g.nodes[0].origin, Origin::InputColumn(_)));
        assert!(matches!(g.nodes[3].origin, Origin::CachedColumn(_)));
        assert!(matches!(g.nodes[2].origin, Origin::Computed));
        assert_eq!(
            g.nodes.iter().map(|n| n.uses).collect::<Vec<_>>(),
            vec![1, 1, 1, 1, 1]
        );
        assert_eq!(g.outputs.len(), 1);
        assert_eq!(g.outputs[0].node, 4);
        assert_eq!(g.nodes[0].width_bytes(), 4);
        assert_eq!(g.nodes[4].width_bytes(), 16);
    }
}
