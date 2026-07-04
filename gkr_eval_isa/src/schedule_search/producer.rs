//! On-demand `CircuitSchedule` producer (Task 6): run [`super::search::search_layer`]
//! against every layer that has atom roots, and stitch the winning per-layer
//! schedules into one `CircuitSchedule` at `budget`.
//!
//! Layer gating: a layer with zero atom roots (`structure::relation_units`
//! empty, i.e. its schedule's `order` will be empty) is only skipped as a
//! trivial `LayerSchedule{order: [], sites: [], ...}` if it ALSO has no
//! materialize-bearing root at all — the exact same
//! `fwd::compile::layer_needs_compile` predicate `compile_circuit` uses to
//! decide whether to run `compile_layer`. A layer can have zero atom roots
//! (e.g. no `claim`-bearing root) yet still carry a materialize-only root
//! (a `Cache` root with no `claim`); such a layer still needs a real
//! `search_layer` pass so its cache placement gets decided for real, so this
//! producer must NOT skip it — using a separate, looser gate here previously
//! let the producer emit an empty schedule for a layer `compile_circuit`
//! would refuse to skip, which `compile_layer_with_policy` would then choke
//! on at compile time (Task 6 review finding). Sharing one predicate makes
//! the two skip decisions structurally unable to drift.

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{CircuitSchedule, DagCircuit, FieldKind, LayerSchedule, ReadPlace};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;

use crate::fwd::compile::{build_cross_layer_field_map, layer_needs_compile};

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
        let order_would_be_empty = relation_units(layer).is_empty();
        if !layer_needs_compile(order_would_be_empty, layer) {
            // No atom roots AND no materialize-bearing root: trivial empty
            // schedule, mirroring `compile_circuit`'s own skip exactly (see
            // `layer_needs_compile`). `floor: 0`, NOT `dag_traffic_floor` —
            // nothing was searched, and the validator requires
            // `floor <= predicted_traffic` (0 here); this also mirrors the
            // deleted v1 producer's empty branch exactly.
            layers.push(LayerSchedule { order: vec![], sites: vec![], predicted_traffic: 0, floor: 0 });
            println!(
                "schedule_search: layer {li}: no atom roots, no materialize roots, skipped (nodes={}, sites=0)",
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
    let sched = CircuitSchedule { circuit: String::new(), budget, layers };

    // Structural self-check before handing the schedule back (the v1 producer ran
    // the cs validator on every produced schedule too): order-permutation, exact
    // site-domain match, finite priorities, floor <= predicted_traffic.
    cs::gkr_compiler::dag_ir::validate_circuit_schedule(dag, &sched)
        .unwrap_or_else(|e| panic!("produce_circuit_schedule: schedule fails validation: {e}"));
    sched
}
