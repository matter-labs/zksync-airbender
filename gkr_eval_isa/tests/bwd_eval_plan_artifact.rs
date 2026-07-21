mod common;

use cs::gkr_compiler::dag_ir::BwdRegime;
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::eval_plan::backward_search::problem::build_backward_search_problem;
use gkr_eval_isa::eval_plan::backward_search::{
    ProductionPagingSolver, ProductionSearchIdentity, search_production_backward,
    solve_production_paging,
};

const R0_FEASIBILITY_FIXTURES: &[&str] = &[
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

#[test]
#[ignore = "Plan 4 R0 exact-solver feasibility gate"]
fn plan4_r0_exact_solver_feasibility_2_to_16() {
    let mut solved = 0usize;
    for fixture in R0_FEASIBILITY_FIXTURES {
        let artifact = common::load_fixture(fixture);
        let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact).unwrap();
        let trace_len = dag.globals.trace_len;
        let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
            .find(|(layer, _, _)| *layer == 0)
            .expect("review-pinned layer zero exists");
        let distilled = distill(&layer, BwdRegime::R0, &cross, None);
        for budget_cells in 2..=16 {
            let (_, problem) =
                build_backward_search_problem(&layer, &distilled, trace_len, budget_cells).unwrap();
            let result = solve_production_paging(&problem.unwrap().demands).unwrap();
            assert!(matches!(
                result.solver,
                ProductionPagingSolver::UniformIntervals | ProductionPagingSolver::RetainAll
            ));
            solved += 1;
            eprintln!("PLAN4-FEASIBLE {fixture} L{layer_index} R0 c{budget_cells} {solved}/60");
        }
    }
    assert_eq!(solved, 60);
}

#[test]
fn production_order_searches_a_representative_real_layer() {
    let fixture = common::FIXTURES[0];
    let artifact = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact).unwrap();
    let trace_len = dag.globals.trace_len;
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
        .next()
        .expect("fixture has a backward-bearing layer");
    let distilled = distill(&layer, BwdRegime::R0, &cross, None);
    let result = search_production_backward(
        &ProductionSearchIdentity {
            circuit: "add_sub_lui_auipc_mop".to_owned(),
            layout_fixture: fixture.to_owned(),
            layer: layer_index,
            regime: BwdRegime::R0,
        },
        &layer,
        &distilled,
        trace_len,
        4,
        None,
    )
    .unwrap();
    assert_eq!(result.order.len(), result.problem.fragment_domain.len());
    assert_eq!(result.telemetry.completed_tiers[0], 128);
    assert!(!result.telemetry.solver_kinds.is_empty());
}
