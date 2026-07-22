#[cfg(all(test, feature = "bench"))]
use std::path::PathBuf;

#[cfg(all(test, feature = "bench"))]
use cs::gkr_compiler::dag_ir::{lower_dag, BwdRegime, DagCircuit, DagLayer};
#[cfg(all(test, feature = "bench"))]
use gkr_eval_isa::bwd::distill::{distill, DistilledLayer};
#[cfg(all(test, feature = "bench"))]
use gkr_eval_isa::eval_plan::{
    compile_backward_plan_artifact, load_backward_evaluation_artifact, select_backward_plan,
    CompiledBackwardEvaluation,
};
#[cfg(all(test, feature = "bench"))]
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;

/// Fully replayed, artifact-certified backward-VM input for add/sub layer 0.
///
/// This loader deliberately consumes only published artifacts: it does not
/// invoke a schedule or pager solver. `compile_backward_plan_artifact` rebuilds
/// and certifies the selected plan against its published digest and score.
#[cfg(all(test, feature = "bench"))]
pub(crate) struct AddSubBwdVmCase {
    pub(crate) dag: DagCircuit,
    pub(crate) canonical: DagLayer,
    pub(crate) distilled: DistilledLayer,
    pub(crate) compiled: CompiledBackwardEvaluation,
    pub(crate) trace_len: usize,
    pub(crate) regime: BwdRegime,
    pub(crate) budget_cells: usize,
}

#[cfg(all(test, feature = "bench"))]
const ADD_SUB_LAYOUT: &str = "add_sub_lui_auipc_mop_layout_gkr.json";
#[cfg(all(test, feature = "bench"))]
const ADD_SUB_BACKWARD_PLAN: &str = "add_sub_lui_auipc_mop_bwd_eval_plan_c2-c16_gkr.json";

#[cfg(all(test, feature = "bench"))]
fn compiled_circuit_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits")
        .join(name)
}

/// Reconstruct one layer-0 backward VM case from the committed add/sub
/// layout and backward-plan artifacts.
#[cfg(all(test, feature = "bench"))]
pub(crate) fn load_add_sub_l0_case(regime: BwdRegime, budget_cells: usize) -> AddSubBwdVmCase {
    let layout_path = compiled_circuit_path(ADD_SUB_LAYOUT);
    let layout_bytes = std::fs::read(&layout_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", layout_path.display()));
    let layout: crate::upstream::GKRCircuitArtifact<crate::primitives::field::BF> =
        serde_json::from_slice(&layout_bytes)
            .unwrap_or_else(|error| panic!("parse {}: {error}", layout_path.display()));
    let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("lower add/sub DAG: {error}"));
    let cross = build_cross_layer_field_map(&dag);
    let canonical = dag
        .layers
        .first()
        .cloned()
        .expect("add/sub artifact must have canonical layer 0");
    let distilled = distill(&canonical, regime, &cross, None);
    let trace_len = dag.globals.trace_len;

    let plan_path = compiled_circuit_path(ADD_SUB_BACKWARD_PLAN);
    let plans = load_backward_evaluation_artifact(&plan_path)
        .unwrap_or_else(|error| panic!("load {}: {error:?}", plan_path.display()));
    let plan = select_backward_plan(&plans, 0, regime, budget_cells)
        .unwrap_or_else(|error| panic!("select add/sub L0 {regime:?} c{budget_cells}: {error:?}"));
    let compiled =
        compile_backward_plan_artifact(&plans.circuit, 0, &canonical, &distilled, trace_len, plan)
            .unwrap_or_else(|error| {
                panic!("replay add/sub L0 {regime:?} c{budget_cells}: {error:?}")
            })
            .compiled;

    AddSubBwdVmCase {
        dag,
        canonical,
        distilled,
        compiled,
        trace_len,
        regime,
        budget_cells,
    }
}

#[cfg(all(test, feature = "bench"))]
mod tests;
