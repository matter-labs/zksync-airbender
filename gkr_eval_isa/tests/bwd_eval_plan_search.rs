mod common;

use std::collections::{BTreeMap, HashMap};

use common::assert_bwd_value_parity;
use cs::gkr_compiler::dag_ir::{
    BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup,
    RootId, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
};
use gkr_eval_isa::bwd::distill::{DistilledLayer, distill};
use gkr_eval_isa::eval_plan::backward_search::experiment::{
    AcceptedIncumbent, ExperimentReport, render_markdown, run_instance,
};
use gkr_eval_isa::eval_plan::backward_search::problem::build_backward_search_problem;
use gkr_eval_isa::eval_plan::backward_search::{
    CertifiedBackwardCandidate, MAX_PAGER_STATES, PagerOutcome, compile_and_certify_paging,
    solve_exact_paging,
};
use gkr_eval_isa::fwd::encode::{decode, encode};

#[test]
#[ignore = "Plan 3 full 342-instance release experiment"]
fn full_plan3_backward_paging_search_experiment() {
    let mut report = ExperimentReport::default();
    for fixture in common::FIXTURES {
        let artifact = common::load_fixture(fixture);
        let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
            .unwrap_or_else(|error| panic!("[{fixture}] lower DAG: {error}"));
        for (layer_index, layer, cross) in common::layers_with_bwd_roots(fixture) {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let distilled = distill(&layer, regime, &cross, None);
                let incumbent = gkr_eval_isa::bwd::compile::compile_distilled(&distilled, 16, None)
                    .ok()
                    .and_then(|_| {
                        let current = gkr_eval_isa::bwd::engine::cs_schedule_bwd_layer(
                            &layer, regime, &cross, 16,
                        );
                        current.fragment_order.zip(current.plan)
                    })
                    .map(|(order, plan)| AcceptedIncumbent { order, plan });
                for budget_cells in [2usize, 3, 4] {
                    report.push(
                        run_instance(
                            fixture,
                            layer_index,
                            &layer,
                            &distilled,
                            dag.globals.trace_len,
                            budget_cells,
                            (budget_cells == 4).then_some(incumbent.as_ref()).flatten(),
                        )
                        .expect("Plan 3 instance must classify or succeed"),
                    );
                }
            }
        }
    }
    assert_eq!(report.instances.len(), 342);
    let markdown = render_markdown(&report);
    let output = std::env::var("GKR_PLAN3_REPORT")
        .expect("GKR_PLAN3_REPORT must name the ignored audit output");
    std::fs::write(output, markdown).expect("write Plan 3 audit");
}

#[test]
#[ignore = "Plan 3 add_sub exact-paging release smoke"]
fn plan3_add_sub_release_smoke() {
    let fixture = "add_sub_lui_auipc_mop_layout_gkr.json";
    let artifact = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
        .unwrap_or_else(|error| panic!("[{fixture}] lower DAG: {error}"));
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
        .next()
        .expect("add_sub has a backward layer");
    let distilled = distill(&layer, BwdRegime::Ext, &cross, None);
    let result = run_instance(
        fixture,
        layer_index,
        &layer,
        &distilled,
        dag.globals.trace_len,
        4,
        None,
    )
    .expect("add_sub Ext c4 must classify or succeed");
    assert_eq!(result.key.budget_cells, 4);
    assert_eq!(result.key.regime, BwdRegime::Ext);
    assert_eq!(result.certificate_failures(), 0);
}

#[test]
fn paging_replay_has_r0_and_ext_cpu_value_parity_at_c4() {
    for (layer, distilled, candidate) in certified_r0_and_ext_candidates() {
        assert_bwd_value_parity(&candidate.compiled.compiled, &distilled, &layer);
    }
}

#[test]
fn paging_replay_encoded_lanes_decode_and_round_trip_exactly() {
    for (_, _, candidate) in certified_r0_and_ext_candidates() {
        let decoded = decode(&candidate.compiled.encoded).expect("decode certified lanes");
        assert_eq!(decoded, candidate.compiled.compiled.program);
        assert_eq!(
            encode(&decoded).expect("re-encode certified program"),
            candidate.compiled.encoded
        );
    }
}

fn certified_r0_and_ext_candidates() -> Vec<(DagLayer, DistilledLayer, CertifiedBackwardCandidate)>
{
    [BwdRegime::R0, BwdRegime::Ext]
        .into_iter()
        .map(|regime| {
            let layer = synthetic_shared_read_layer();
            let distilled = distill(&layer, regime, &HashMap::new(), None);
            let (_, problem) = build_backward_search_problem(&layer, &distilled, 8, 4).unwrap();
            let problem = problem.expect("synthetic shared-read problem");
            let exact = match solve_exact_paging(&problem.demands, MAX_PAGER_STATES).unwrap() {
                PagerOutcome::Solved(exact) => exact,
                outcome => panic!("expected solved paging problem, got {outcome:?}"),
            };
            let candidate = compile_and_certify_paging(&distilled, &problem, &exact, 0).unwrap();
            (layer, distilled, candidate)
        })
        .collect()
}

fn synthetic_shared_read_layer() -> DagLayer {
    DagLayer {
        sources: (0..3).map(read_source).collect(),
        exprs: vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
            Expr::Mul(vec![ExprId(0), ExprId(1)]),
            Expr::Mul(vec![ExprId(0), ExprId(2)]),
        ],
        batching: BatchingOrder {
            roots: vec![RootId(0), RootId(1)],
        },
        roots: vec![claim_root(ExprId(3), 0), claim_root(ExprId(4), 1)],
        resolutions: BTreeMap::new(),
    }
}

fn read_source(column: usize) -> SourceInfo {
    SourceInfo {
        kind: SourceKind::Read {
            place: ReadPlace::BaseLayerWitness { column },
        },
    }
}

fn claim_root(expr: ExprId, relation_index: usize) -> Root {
    Root {
        expr,
        materialize: None,
        claim: Some(ClaimInfo {
            origin: RootOrigin {
                group: RootGroup::Gates,
                relation_index,
                slot: RootSlot::Constraint(0),
            },
        }),
    }
}
