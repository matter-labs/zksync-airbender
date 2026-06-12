//! Soundness guards for the forward native-program design (spec rev-3 §5):
//! (a) same-layer GateOutput nodes have ZERO readers (expression children,
//!     gate operands, cache inputs) — precondition for GateK dst-native-only
//!     and order-free trace comparison;
//! (b) every same-layer Cached-address Place resolves to exactly one
//!     producing cache (the CacheK aliasing rule), and at most one Place per
//!     cache;
//! (c) the cache-on-cache dependency relation is acyclic;
//! (d) at EVERY layer, the only computed operand in any output-bearing
//!     gate's canonical enumeration is the trailing MaxQuadratic `expr`
//!     lane (dropped under the native-flat contract); cache inputs and
//!     program outputs have none;
//! (e) MaxQuadratic flat lane counts stay <= 64 (escape hatch per spec §2a:
//!     per-gate expr-cone delivery, the IR carries both forms).
//! If (a) ever fires, GateK gains explicit precedence edges and the oracle
//! must start checking firing order. If (d)/(e) fire, the flat contract no
//! longer covers forward and the spec must be revisited.

use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::{CodegenGate, ExprNode, GateKind, gate_kind_input_nodes};
use gkr_design_space::import::load_circuit;
use std::collections::HashMap;

fn fixtures() -> Vec<std::path::PathBuf> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits");
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| {
            let p = e.unwrap().path();
            p.file_name()?.to_str()?.contains("codegen_ir").then_some(p)
        })
        .collect();
    paths.sort();
    assert_eq!(paths.len(), 22, "expected 22 IR fixtures");
    paths
}

/// Forward-eligible: output-bearing and not a host-side copy alias.
pub fn fwd_eligible(g: &CodegenGate) -> bool {
    !g.dst.is_empty()
        && !matches!(
            g.kind,
            GateKind::CopyInBaseField { .. } | GateKind::CopyInExtensionField { .. }
        )
}

/// All leaf descendants of `node` (cone leaves; `node` itself if leaf).
fn cone_leaves(arena: &[ExprNode], node: usize, out: &mut Vec<usize>) {
    match &arena[node] {
        ExprNode::Sum { terms, .. } => {
            for t in terms {
                cone_leaves(arena, t.0 as usize, out);
            }
        }
        ExprNode::Product { factors, .. } => {
            for f in factors {
                cone_leaves(arena, f.0 as usize, out);
            }
        }
        ExprNode::Constant(_) => {}
        _ => out.push(node),
    }
}

#[test]
fn native_dag_soundness() {
    for p in fixtures() {
        let c = load_circuit(&p).unwrap();
        let name = p.file_name().unwrap().to_str().unwrap().to_string();
        for (li, layer) in c.circuit.layers.iter().enumerate() {
            let arena = &layer.arena.nodes;
            let computed =
                |i: usize| matches!(arena[i], ExprNode::Sum { .. } | ExprNode::Product { .. });

            // Readers per node: expression children + ALL gate operand lanes
            // + cache inputs (the prior probe missed cache inputs).
            let mut readers = vec![0u32; arena.len()];
            for n in arena.iter() {
                match n {
                    ExprNode::Sum { terms, .. } => {
                        for t in terms {
                            readers[t.0 as usize] += 1;
                        }
                    }
                    ExprNode::Product { factors, .. } => {
                        for f in factors {
                            readers[f.0 as usize] += 1;
                        }
                    }
                    _ => {}
                }
            }
            for gate in layer.gates.iter().chain(&layer.gates_external) {
                for id in gate_kind_input_nodes(&gate.kind) {
                    readers[id.0 as usize] += 1;
                }
            }
            for cache in &layer.caches {
                for id in &cache.inputs {
                    readers[id.0 as usize] += 1;
                }
            }

            // (a) GateOutput nodes (same-layer products) are never read.
            for (i, n) in arena.iter().enumerate() {
                if matches!(n, ExprNode::GateOutput { .. }) {
                    assert_eq!(
                        readers[i], 0,
                        "{name} L{li} node {i}: same-layer GateOutput has a reader \
                         — GateK dst-native-only is unsound, spec needs precedence edges"
                    );
                }
            }

            // (b) Cached-address Place <-> producing cache, 1:1.
            let mut addr_to_cache: HashMap<GKRAddress, usize> = HashMap::new();
            for (ci, cache) in layer.caches.iter().enumerate() {
                let prev = addr_to_cache.insert(cache.out.1, ci);
                assert!(prev.is_none(), "{name} L{li}: two caches share out addr");
            }
            let mut place_per_cache: HashMap<usize, usize> = HashMap::new();
            for (i, n) in arena.iter().enumerate() {
                if let ExprNode::Place { addr, .. } = n {
                    if matches!(addr, GKRAddress::Cached { .. }) {
                        let ci = *addr_to_cache.get(addr).unwrap_or_else(|| {
                            panic!("{name} L{li} node {i}: Cached Place with no producing cache")
                        });
                        let prev = place_per_cache.insert(ci, i);
                        assert!(
                            prev.is_none(),
                            "{name} L{li}: two Place nodes for cache {ci} (CSE violation)"
                        );
                    }
                }
            }

            // (c) cache-on-cache dependencies are acyclic (a cache whose input
            // cone reaches another cache's Cached Place depends on it).
            let n_caches = layer.caches.len();
            let mut deps: Vec<Vec<usize>> = vec![Vec::new(); n_caches];
            for (ci, cache) in layer.caches.iter().enumerate() {
                for id in &cache.inputs {
                    let mut leaves = Vec::new();
                    cone_leaves(arena, id.0 as usize, &mut leaves);
                    for l in leaves {
                        if let ExprNode::Place { addr, .. } = &arena[l] {
                            if let Some(&dep) = addr_to_cache.get(addr) {
                                deps[ci].push(dep);
                            }
                        }
                    }
                }
            }
            // Kahn-style fixpoint: every cache must become resolvable.
            let mut resolved = vec![false; n_caches];
            loop {
                let mut progress = false;
                for ci in 0..n_caches {
                    if !resolved[ci] && deps[ci].iter().all(|&d| resolved[d]) {
                        resolved[ci] = true;
                        progress = true;
                    }
                }
                if !progress {
                    break;
                }
            }
            assert!(
                resolved.iter().all(|r| *r),
                "{name} L{li}: cyclic cache dependencies"
            );

            // (d) computed forward dependencies occur ONLY as the trailing
            // MaxQuadratic expr lane; (e) flat lane bound.
            for gate in layer.gates.iter().chain(&layer.gates_external) {
                if !fwd_eligible(gate) {
                    continue;
                }
                let ops = gate_kind_input_nodes(&gate.kind);
                for (k, id) in ops.iter().enumerate() {
                    if computed(id.0 as usize) {
                        assert!(
                            matches!(gate.kind, GateKind::MaxQuadratic { .. })
                                && k == ops.len() - 1,
                            "{name} L{li}: computed operand outside the MaxQuadratic \
                             expr lane — the flat contract no longer covers forward"
                        );
                    }
                }
                if matches!(gate.kind, GateKind::MaxQuadratic { .. }) {
                    let lanes = ops.len() - 1; // flat lanes after dropping expr
                    assert!(
                        lanes <= 64,
                        "{name} L{li}: MaxQuadratic flat width {lanes} > 64 — \
                         escape hatch: per-gate expr-cone delivery (spec §2a)"
                    );
                }
            }
            for cache in &layer.caches {
                for id in &cache.inputs {
                    assert!(
                        !computed(id.0 as usize),
                        "{name} L{li}: computed cache input"
                    );
                }
            }
            // Output slots are all GateOutput nodes by IR construction today
            // (gate dsts + cache outs — verified across fixtures), which made
            // a GateOutput-filtered check vacuous. Assert the underlying fact
            // directly over EVERY output node: none is computed, so a future
            // IR change putting a Sum/Product in an output slot fires here.
            for out in &c.graphs[li].outputs {
                assert!(
                    !computed(out.node),
                    "{name} L{li}: computed output slot node {}",
                    out.node
                );
            }
        }
    }
}
