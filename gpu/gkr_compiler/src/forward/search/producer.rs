//! Search each claim-bearing layer and assemble a circuit schedule.

use std::collections::HashMap;

use gkr_eval_ir::{DagCircuit, FieldKind, ReadPlace};

use crate::analysis::build_cross_layer_field_map;
use crate::forward::artifact::{ForwardLayerArtifact, ForwardSearchArtifact};
use crate::forward::BF_LANES_PER_E4_BUCKET;
use crate::search::SearchConfig;

use super::scorer::LayerCtx;
use super::search::search_layer;

pub(crate) fn produce_circuit_schedule(
    dag: &DagCircuit,
    budget_buckets: usize,
    cfg: &SearchConfig,
    seed: u64,
    incumbent: Option<&ForwardSearchArtifact>,
) -> ForwardSearchArtifact {
    let budget_lanes = budget_buckets * BF_LANES_PER_E4_BUCKET;
    let cross: HashMap<ReadPlace, FieldKind> = build_cross_layer_field_map(dag);
    let mut layers: Vec<ForwardLayerArtifact> = Vec::with_capacity(dag.layers.len());

    for li in 0..dag.layers.len() {
        let ctx = LayerCtx::new(dag, li, &cross, budget_lanes);
        if ctx.n_order_keys() == 0 {
            layers.push(ForwardLayerArtifact {
                units: vec![],
                sites: vec![],
                predicted_traffic: 0,
            });
            continue;
        }

        let layer_incumbent = incumbent.and_then(|s| s.layers.get(li));
        layers.push(search_layer(&ctx, cfg, seed, layer_incumbent));
    }

    let sched = ForwardSearchArtifact {
        circuit: String::new(),
        budget_buckets,
        layers,
    };

    sched
}
