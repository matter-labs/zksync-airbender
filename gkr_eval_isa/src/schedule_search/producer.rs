//! On-demand `CircuitSchedule` producer (Task 6): run [`super::search::search_layer`]
//! against every layer that has atom roots, and stitch the winning per-layer
//! schedules into one `CircuitSchedule` at `budget`.
//!
//! Layer gating: a layer with zero atom roots (`structure::relation_units`
//! empty — no `materialize.is_some() && claim.is_some()` root) has nothing to
//! schedule; it gets the trivial `LayerSchedule{order: [], sites: [], ...}`
//! `compile_circuit` already special-cases (its own
//! `ls.order.is_empty() && layer.roots.iter().all(|r| r.materialize.is_none())`
//! skip). Earlier drafts of this producer (deleted alongside the v1
//! `StepPlan` schema in Task 4 — see the tombstone in
//! `gkr_eval_isa/tests/s3_gap_experiment.rs`) referred to this gate as
//! `layer_is_compiled`; that name no longer exists anywhere in the tree, so
//! this promotion re-establishes the predicate directly against Task 5's
//! `relation_units` rather than resurrecting a name with no surviving
//! definition to mirror.

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{
    build_cross_layer_field_map, CircuitSchedule, DagCircuit, FieldKind, LayerSchedule, ReadPlace,
};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;

use super::floor::dag_traffic_floor;
use super::scorer::LayerCtx;
use super::search::{search_layer, SearchConfig};
use super::structure::relation_units;

/// Build a `CircuitSchedule` for `dag` at `budget` by searching every
/// compiled (atom-root-bearing) layer with `cfg`. Prints one line per layer to
/// stdout (RR's desired perf-envelope visibility): node/site counts, evals
/// performed, compiles/sec, and wall time.
pub fn produce_circuit_schedule(
    dag: &DagCircuit,
    artifact: &GKRCircuitArtifact<BabyBearField>,
    budget: usize,
    cfg: &SearchConfig,
) -> CircuitSchedule {
    let cross: HashMap<ReadPlace, FieldKind> = build_cross_layer_field_map(dag);
    let mut layers: Vec<LayerSchedule> = Vec::with_capacity(dag.layers.len());

    for (li, layer) in dag.layers.iter().enumerate() {
        if relation_units(layer).is_empty() {
            layers.push(LayerSchedule {
                order: vec![],
                sites: vec![],
                predicted_traffic: 0,
                floor: dag_traffic_floor(layer, &cross),
            });
            println!(
                "schedule_search: layer {li}: no atom roots, skipped (nodes={}, sites=0)",
                layer.exprs.len()
            );
            continue;
        }

        let ctx = LayerCtx::new(layer, &artifact.layers[li], artifact, &cross, budget);
        let n_sites = ctx.n_sites();
        let node_count = layer.exprs.len();

        let outcome = search_layer(&ctx, cfg);
        let secs = outcome.wall.as_secs_f64().max(1e-9);
        let compiles_per_sec = outcome.compiles as f64 / secs;
        println!(
            "schedule_search: layer {li}: nodes={node_count} sites={n_sites} evals={} \
             compiles/s={compiles_per_sec:.1} wall={:.3}s predicted_traffic={} floor={}",
            outcome.compiles,
            outcome.wall.as_secs_f64(),
            outcome.schedule.predicted_traffic,
            outcome.schedule.floor,
        );
        layers.push(outcome.schedule);
    }

    // `DagCircuit` carries no fixture-name metadata (it's a pure post-lowering IR;
    // the name lives one layer up, on the `.json` fixture stem) and the brief's
    // signature takes no separate name parameter, so `circuit` is left empty here
    // — the caller (the fixture-regen entry point in `tests/schedule_search_gates.rs`)
    // sets it to the fixture stem before serializing, exactly as `load_dag_sched`
    // already expects a `CircuitSchedule.circuit` field to exist for the record.
    CircuitSchedule { circuit: String::new(), budget, layers }
}
