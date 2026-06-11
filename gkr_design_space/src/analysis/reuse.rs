//! Fan-out histogram + per-cache marginal-cost ingredients (spec principle 1:
//! ingredients only — selection over the coupled space is a later search pass).

use crate::analysis::working_set::closure_load_nodes;
use crate::graph::{AnalysisGraph, Origin};
use crate::import::LoadedCircuit;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::{CacheKind, Domain, ExprNode};
use serde::Serialize;
use std::collections::{BTreeMap, HashMap, HashSet};

/// Relative op weights, mul-centric (bf mul = 1): mixed bf*e4 ~ 4 bf muls,
/// e4*e4 ~ 12 (Karatsuba + reduction). Coarse on purpose — reweight freely.
pub const BF_OP: u64 = 1;
pub const MIXED_OP: u64 = 4;
pub const E4_OP: u64 = 12;

#[derive(Debug, Default, Serialize)]
pub struct RecomputeOps {
    pub bf: u64,
    pub mixed: u64,
    pub e4: u64,
    /// BF_OP/MIXED_OP/E4_OP-weighted total, in bf-mul equivalents.
    pub weighted: u64,
}

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
    /// NO current cache kind is backward-rematerializable (audit
    /// 2026-06-11): lookup caches are table GATHERS t[mapping(x)] — the
    /// LinearComb in their CacheKind is the index computation, not the value —
    /// and fold(gather) != gather(fold); memory tuples are products (degree
    /// cap). The only sound variant is deferring materialization to backward
    /// round 0 (on-hypercube), which saves exactly the forward store below.
    pub recompute_ops: RecomputeOps,
    /// Backward fold-chain bytes/row of the materialized cache column —
    /// unavoidable for every current cache kind once it is consumed backward.
    pub bwd_materialize_bytes_per_row: u64,
}

#[derive(Debug, Serialize)]
pub struct CircuitReuse {
    /// Fan-out histogram over computed nodes, all layers pooled: fanout -> count.
    pub fanout_histogram: BTreeMap<u32, u32>,
    pub caches: Vec<CacheIngredients>,
}

/// Backward fold-chain bytes/row for one materialized column (per-original-row
/// units, geometric in trace length; mirrors `analysis::backward` formulas):
/// e4: r0 16 + r1 (16+8) + r2 (8+4) + tail ~12 ≈ 64; bf: r0 4 + r1 (4+8) +
/// r2 (4+4) + tail ~12 ≈ 36.
pub fn fold_chain_bytes_per_row(width: u32) -> u64 {
    match width {
        4 => 36,
        _ => 64,
    }
}

/// One-point evaluation cost of a cache value: graph-cone Sum/Product ops plus
/// the CacheKind's own combination (challenge FMAs per fan-in column; memory
/// tuples add the lhs*rhs e4 product).
fn cache_recompute_ops(
    g: &AnalysisGraph,
    layer: &cs::gkr_compiler::codegen_ir::CodegenLayer,
    arena: &[ExprNode],
    cache: &cs::gkr_compiler::codegen_ir::CodegenCache,
    fanin_cols: u64,
) -> RecomputeOps {
    let mut ops = RecomputeOps::default();
    let _ = layer;
    // Cone walk from the cache inputs through Computed Sum/Product nodes.
    let mut stack: Vec<usize> = cache.inputs.iter().map(|id| id.0 as usize).collect();
    let mut seen = HashSet::new();
    while let Some(n) = stack.pop() {
        if !seen.insert(n) {
            continue;
        }
        if let ExprNode::Sum { terms, domain }
        | ExprNode::Product {
            factors: terms,
            domain,
        } = &arena[n]
        {
            let k = terms.len().saturating_sub(1) as u64;
            let mixed = terms
                .iter()
                .any(|t| g.nodes[t.0 as usize].domain != *domain);
            match (domain, mixed) {
                (Domain::Base, _) => ops.bf += k,
                (Domain::Ext, true) => ops.mixed += k,
                (Domain::Ext, false) => ops.e4 += k,
            }
            stack.extend(terms.iter().map(|t| t.0 as usize));
        }
    }
    // Kind-level combination on top of the cone.
    match &cache.kind {
        CacheKind::SingleColumnLookup { .. }
        | CacheKind::VectorizedLookup { .. }
        | CacheKind::VectorizedLookupSetup => ops.mixed += fanin_cols,
        CacheKind::MemoryTuple { .. } => {
            ops.mixed += fanin_cols;
            ops.e4 += 1;
        }
    }
    ops.weighted = ops.bf * BF_OP + ops.mixed * MIXED_OP + ops.e4 * E4_OP;
    ops
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

            let recompute_ops =
                cache_recompute_ops(g, layer, &layer.arena.nodes, cache, fanin_cols as u64);
            let width = g.nodes[out_node].width_bytes();
            caches.push(CacheIngredients {
                producing_layer: li,
                addr: cache.out.1,
                store_bytes_per_row: width,
                uses_per_layer,
                total_uses,
                fanin_cols,
                fanin_bytes_per_row,
                marginal_bytes_per_row,
                recompute_ops,
                bwd_materialize_bytes_per_row: fold_chain_bytes_per_row(width),
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
            assert!(ci.recompute_ops.weighted > 0, "zero-op cache {:?}", ci.addr);
            assert!(ci.bwd_materialize_bytes_per_row > 0);
        }
        assert!(!r.fanout_histogram.is_empty());
    }
}
