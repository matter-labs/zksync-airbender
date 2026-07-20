mod common;

use std::collections::{BTreeMap, HashMap};

use common::assert_bwd_value_parity;
use cs::gkr_compiler::dag_ir::{
    BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup,
    RootId, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
};
use gkr_eval_isa::bwd::distill::{DistilledLayer, distill};
use gkr_eval_isa::eval_plan::backward_search::experiment::{
    AcceptedIncumbent, ArmClassification, ExperimentReport, render_markdown, run_instance,
};
use gkr_eval_isa::eval_plan::backward_search::problem::{
    ProblemClassification, build_backward_search_problem,
};
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
                        .unwrap_or_else(|error| {
                            panic!(
                                "Plan 3 instance must classify or succeed: {fixture} L{layer_index} {regime:?} c{budget_cells}: {error:?}"
                            )
                        }),
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
    let current =
        gkr_eval_isa::bwd::engine::cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);
    let incumbent = current
        .fragment_order
        .zip(current.plan)
        .map(|(order, plan)| AcceptedIncumbent { order, plan })
        .expect("add_sub Ext c4 ships a fragment-plan incumbent");
    let result = run_instance(
        fixture,
        layer_index,
        &layer,
        &distilled,
        dag.globals.trace_len,
        4,
        Some(&incumbent),
    )
    .expect("add_sub Ext c4 must classify or succeed");
    assert_eq!(result.key.budget_cells, 4);
    assert_eq!(result.key.regime, BwdRegime::Ext);
    assert!(matches!(
        result.incumbent.classification,
        ArmClassification::Searched
    ));
    assert!(result.incumbent.score.is_some());
    assert_eq!(result.certificate_failures(), 0);
}

#[test]
#[ignore = "Plan 3 inits-and-teardowns c2 classification regression"]
fn plan3_inits_and_teardowns_r0_c2_classifies() {
    let fixture = "inits_and_teardowns_preprocessed_layout_gkr.json";
    let artifact = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
        .unwrap_or_else(|error| panic!("[{fixture}] lower DAG: {error}"));
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
        .find(|(layer_index, _, _)| *layer_index == 0)
        .expect("inits-and-teardowns has backward layer zero");
    let distilled = distill(&layer, BwdRegime::R0, &cross, None);
    let (classification, problem) =
        build_backward_search_problem(&layer, &distilled, dag.globals.trace_len, 2)
            .expect("inits-and-teardowns c2 problem must classify");
    assert!(matches!(
        classification,
        ProblemClassification::Trivial { .. }
    ));
    let problem = problem.expect("trivial c2 problem retains its replay surface");
    assert!(problem.stream_reductions);
    assert!(
        problem
            .demands
            .iter()
            .all(|demand| matches!(layer.exprs[demand.expr.0 as usize], Expr::Source(_)))
    );
    let exact = match solve_exact_paging(&problem.demands, MAX_PAGER_STATES)
        .expect("trivial c2 paging solve")
    {
        PagerOutcome::Solved(exact) => exact,
        PagerOutcome::SolverCapped { .. } => panic!("trivial c2 paging must not cap"),
    };
    let candidate = compile_and_certify_paging(&distilled, &problem, &exact, 0)
        .expect("trivial c2 all-bypass replay must consume its logical stream");
    let decoded = decode(&candidate.compiled.encoded).expect("decode c2 replay lanes");
    assert_eq!(decoded, candidate.compiled.compiled.program);
    assert_eq!(
        encode(&decoded).expect("re-encode c2 replay lanes"),
        candidate.compiled.encoded
    );
    assert_eq!(
        candidate.certificate.predicted_read_cost,
        candidate.certificate.realized_read_cost
    );
    assert_bwd_value_parity(&candidate.compiled.compiled, &distilled, &layer);
    let result = run_instance(
        fixture,
        layer_index,
        &layer,
        &distilled,
        dag.globals.trace_len,
        2,
        None,
    )
    .expect("inits-and-teardowns L0 R0 c2 must classify or succeed");
    assert_eq!(result.key.budget_cells, 2);
    assert_eq!(result.key.regime, BwdRegime::R0);
}

#[test]
#[ignore = "Plan 3 unsigned-mul-div Ext c4 replay regression"]
fn plan3_unsigned_mul_div_l1_ext_c4_classifies() {
    let fixture = "unsigned_mul_div_layout_gkr.json";
    let artifact = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
        .unwrap_or_else(|error| panic!("[{fixture}] lower DAG: {error}"));
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
        .find(|(layer_index, _, _)| *layer_index == 1)
        .expect("unsigned-mul-div has backward layer one");
    let distilled = distill(&layer, BwdRegime::Ext, &cross, None);
    let current =
        gkr_eval_isa::bwd::engine::cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);
    let incumbent = current
        .fragment_order
        .zip(current.plan)
        .map(|(order, plan)| AcceptedIncumbent { order, plan });
    assert!(
        incumbent.is_some(),
        "fixture must expose its production incumbent"
    );
    let result = run_instance(
        fixture,
        layer_index,
        &layer,
        &distilled,
        dag.globals.trace_len,
        4,
        incumbent.as_ref(),
    )
    .expect("unsigned-mul-div L1 Ext c4 must classify or succeed");
    assert_eq!(result.key.budget_cells, 4);
    assert_eq!(result.key.regime, BwdRegime::Ext);
    assert!(matches!(
        result.incumbent.classification,
        ArmClassification::UnavailableIncumbent
    ));
    for arm in [&result.arm1, &result.arm2, &result.arm3, &result.arm4] {
        assert!(matches!(arm.classification, ArmClassification::Searched));
        assert!(arm.score.is_some());
    }
    assert_eq!(result.certificate_failures(), 0);
    let report = ExperimentReport::from_instances(vec![result]);
    assert_eq!(report.incumbent_comparable, 0);
    assert_eq!(report.counts_by_budget[&4].matching_incumbent, 0);
    assert_eq!(report.paged_computed, 1);
}

#[test]
fn backward_uncached_and_replay_share_leaf_only_fused_stream() {
    let mut layer = common::synthetic_fma_compound_products_layer(1, 2).layer;
    let products = layer
        .exprs
        .iter()
        .enumerate()
        .filter_map(|(index, expr)| matches!(expr, Expr::Mul(_)).then_some(ExprId(index as u32)))
        .collect::<Vec<_>>();
    let direct = products
        .iter()
        .copied()
        .find(|product| match &layer.exprs[product.0 as usize] {
            Expr::Mul(children) => children
                .iter()
                .all(|child| matches!(layer.exprs[child.0 as usize], Expr::Source(_))),
            _ => false,
        })
        .expect("synthetic FMA layer has a direct product");
    let compound = products
        .iter()
        .copied()
        .find(|product| match &layer.exprs[product.0 as usize] {
            Expr::Mul(children) => children
                .iter()
                .any(|child| matches!(layer.exprs[child.0 as usize], Expr::Add(_))),
            _ => false,
        })
        .expect("synthetic FMA layer has a compound product");
    let repeated_add = layer
        .exprs
        .iter_mut()
        .find_map(|expr| match expr {
            Expr::Add(children) if children.contains(&direct) && children.contains(&compound) => {
                Some(children)
            }
            _ => None,
        })
        .expect("synthetic FMA layer has an Add containing both product kinds");
    repeated_add.extend([direct, compound]);
    let distilled = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
    let replay_domain = gkr_eval_isa::bwd::distill::distilled_site_domain(&distilled)
        .into_iter()
        .map(|site| site.value)
        .collect::<std::collections::BTreeSet<_>>();
    assert!(replay_domain.contains(&direct));
    assert!(replay_domain.contains(&compound));
    let uncached =
        gkr_eval_isa::eval_plan::compile_backward_fragments_uncached(&distilled, None, 4, true)
            .expect("streaming mixed FMA reference compile");
    let entries = uncached
        .trace
        .events
        .iter()
        .filter_map(|event| match event {
            gkr_eval_isa::bwd::trace::BwdEvent::Serve { fp, .. }
                if replay_domain.contains(&fp.value) =>
            {
                Some(gkr_eval_isa::bwd::plan::PlanEntry {
                    fp: *fp,
                    action: gkr_eval_isa::bwd::plan::PlanAction::Bypass,
                })
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        entries
            .iter()
            .all(|entry| entry.fp.value != direct && entry.fp.value != compound)
    );
    let replay_plan = gkr_eval_isa::bwd::plan::BwdOccurrencePlan {
        epoch: uncached.trace.epoch,
        entries_fnv: gkr_eval_isa::bwd::plan::plan_entries_fnv(&entries),
        stream_reductions: true,
        entries,
    };
    let replayed = gkr_eval_isa::eval_plan::compile_backward_fragments_replayed(
        &distilled,
        &replay_plan,
        None,
        4,
    )
    .expect("streaming mixed FMA reference must replay exactly");
    assert_eq!(replayed.encoded, uncached.encoded);
    assert_eq!(replayed.compiled.stats_ext, uncached.compiled.stats_ext);
    let (_, problem) = build_backward_search_problem(&layer, &distilled, 8, 4)
        .expect("mixed direct/compound FMA problem must build");
    let problem = problem.expect("mixed direct/compound FMA problem retains its replay surface");
    assert!(
        problem
            .demands
            .iter()
            .all(|demand| matches!(layer.exprs[demand.expr.0 as usize], Expr::Source(_)))
    );
    assert!(
        problem
            .all_domain_serves
            .iter()
            .all(|serve| serve.value != direct && serve.value != compound)
    );
    let exact = match solve_exact_paging(&problem.demands, MAX_PAGER_STATES)
        .expect("mixed direct/compound FMA paging solve")
    {
        PagerOutcome::Solved(exact) => exact,
        PagerOutcome::SolverCapped { .. } => panic!("small mixed FMA paging must not cap"),
    };
    let candidate = compile_and_certify_paging(&distilled, &problem, &exact, 0)
        .expect("mixed direct/compound FMA replay must consume its logical stream");
    let decoded = decode(&candidate.compiled.encoded).expect("decode mixed FMA replay lanes");
    assert_eq!(decoded, candidate.compiled.compiled.program);
    assert_eq!(
        encode(&decoded).expect("re-encode mixed FMA replay lanes"),
        candidate.compiled.encoded
    );
    assert_eq!(
        candidate.certificate.predicted_read_cost,
        candidate.certificate.realized_read_cost
    );
    assert_bwd_value_parity(&candidate.compiled.compiled, &distilled, &layer);
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
