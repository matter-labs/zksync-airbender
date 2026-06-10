//! Fan-out histogram + per-cache marginal-cost ingredients (spec principle 1:
//! ingredients only — selection over the coupled space is a later search pass).

use crate::analysis::working_set::closure_load_nodes;
use crate::graph::{AnalysisGraph, Origin};
use crate::import::LoadedCircuit;
use cs::definitions::GKRAddress;
use serde::Serialize;
use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Debug, Serialize)]
pub struct CacheIngredients {
    pub producing_layer: usize,
    pub addr: GKRAddress,
    pub store_bytes_per_row: u32,
    /// Consumers per layer: (layer, place-node fan-out in that layer's graph).
    pub uses_per_layer: Vec<(usize, u32)>,
    pub total_uses: u32,
    /// Distinct loaded columns in the cache's compute closure (recompute fan-in).
    pub fanin_cols: usize,
    pub fanin_bytes_per_row: u64,
    /// Per consumer layer: fan-in bytes NOT already in that layer's baseline
    /// loaded set — the marginal traffic if recomputed there instead of loaded.
    pub marginal_bytes_per_row: Vec<(usize, u64)>,
}

#[derive(Debug, Serialize)]
pub struct CircuitReuse {
    /// Fan-out histogram over computed nodes, all layers pooled: fanout -> count.
    pub fanout_histogram: BTreeMap<u32, u32>,
    pub caches: Vec<CacheIngredients>,
}

pub fn circuit_reuse(c: &LoadedCircuit) -> CircuitReuse {
    let mut fanout_histogram = BTreeMap::new();
    for g in &c.graphs {
        for n in &g.nodes {
            if matches!(n.origin, Origin::Computed) {
                *fanout_histogram.entry(n.uses).or_insert(0) += 1;
            }
        }
    }

    // Baseline loaded-column address set per layer (for marginal-cost overlap).
    let layer_loads: Vec<HashSet<GKRAddress>> = c
        .graphs
        .iter()
        .map(|g| {
            g.nodes
                .iter()
                .filter_map(|n| match n.origin {
                    Origin::InputColumn(a) | Origin::CachedColumn(a) | Origin::Scratch(a) => {
                        Some(a)
                    }
                    _ => None,
                })
                .collect()
        })
        .collect();

    // Cached-addr consumers: addr -> [(layer, uses)].
    let mut consumers: HashMap<GKRAddress, Vec<(usize, u32)>> = HashMap::new();
    for (li, g) in c.graphs.iter().enumerate() {
        for n in &g.nodes {
            if let Origin::CachedColumn(a) = n.origin {
                consumers.entry(a).or_default().push((li, n.uses));
            }
        }
    }

    let mut caches = Vec::new();
    for (li, (layer, g)) in c.circuit.layers.iter().zip(&c.graphs).enumerate() {
        for cache in &layer.caches {
            let out_node = cache.out.0.0 as usize;
            let fanin = closure_load_nodes(g, out_node);
            let fanin_cols = fanin.len();
            let fanin_bytes_per_row: u64 =
                fanin.iter().map(|&i| g.nodes[i].width_bytes() as u64).sum();
            let fanin_addrs: Vec<(GKRAddress, u64)> = fanin
                .iter()
                .filter_map(|&i| match g.nodes[i].origin {
                    Origin::InputColumn(a) | Origin::CachedColumn(a) | Origin::Scratch(a) => {
                        Some((a, g.nodes[i].width_bytes() as u64))
                    }
                    _ => None,
                })
                .collect();

            let uses_per_layer = consumers.get(&cache.out.1).cloned().unwrap_or_default();
            let total_uses = uses_per_layer.iter().map(|&(_, u)| u).sum();
            let marginal_bytes_per_row = uses_per_layer
                .iter()
                .map(|&(cl, _)| {
                    let missing: u64 = fanin_addrs
                        .iter()
                        .filter(|(a, _)| !layer_loads[cl].contains(a))
                        .map(|&(_, w)| w)
                        .sum();
                    (cl, missing)
                })
                .collect();

            caches.push(CacheIngredients {
                producing_layer: li,
                addr: cache.out.1,
                store_bytes_per_row: g.nodes[out_node].width_bytes(),
                uses_per_layer,
                total_uses,
                fanin_cols,
                fanin_bytes_per_row,
                marginal_bytes_per_row,
            });
        }
    }

    CircuitReuse {
        fanout_histogram,
        caches,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::import::load_circuit;
    use crate::import::tests::fixture;

    #[test]
    fn add_sub_cache_ingredients() {
        let c = load_circuit(&fixture("add_sub_lui_auipc_mop_codegen_ir_gkr.json")).unwrap();
        let r = circuit_reuse(&c);
        // layer-0 cache count is the verified number; later layers may add more
        assert_eq!(
            r.caches.iter().filter(|ci| ci.producing_layer == 0).count(),
            16
        );
        assert!(r.caches.len() >= 16);
        for ci in &r.caches {
            assert!(ci.store_bytes_per_row == 4 || ci.store_bytes_per_row == 16);
            // every cache the compiler materialized has at least one consumer
            assert!(ci.total_uses >= 1, "dead cache {:?}", ci.addr);
        }
        assert!(!r.fanout_histogram.is_empty());
    }
}
