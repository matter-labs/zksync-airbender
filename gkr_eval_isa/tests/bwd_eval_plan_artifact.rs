mod common;

use cs::gkr_compiler::dag_ir::BwdRegime;
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::eval_plan::backward_search::problem::build_backward_search_problem;
use gkr_eval_isa::eval_plan::backward_search::{
    ProductionPagingSolver, ProductionSearchIdentity, search_production_backward,
    solve_production_paging,
};
use gkr_eval_isa::eval_plan::{
    BackwardEvaluationCircuitArtifact, BackwardLayerArtifact, BackwardPlanArtifact,
    BackwardRegimeArtifact, BackwardScoreArtifact, CanonicalU128, DomainCertificate,
    SourceCostArtifact, load_backward_evaluation_artifact,
};

const R0_FEASIBILITY_FIXTURES: &[&str] = &[
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

fn sample_plan(budget_cells: usize) -> BackwardPlanArtifact {
    BackwardPlanArtifact {
        budget_cells,
        problem: DomainCertificate {
            count: 0,
            digest: [0; 4],
        },
        fragment_order: vec![],
        retained_demands: vec![],
        expected_score: BackwardScoreArtifact {
            infeasible: false,
            whole_pass_dram_bytes: 0.into(),
            primitive_source_ops: 0.into(),
            instructions: 0,
            encoded_lanes: 0,
            arithmetic_ops: 0,
        },
        expected_paging: gkr_eval_isa::eval_plan::BackwardPagingCertificateArtifact {
            actions_consumed: 0,
            diverged: None,
            refused_retains: 0,
            predicted_source_reads: 0,
            realized_source_reads: 0,
            predicted_read_cost: SourceCostArtifact::default(),
            realized_read_cost: SourceCostArtifact::default(),
            fixed_write_cost: SourceCostArtifact::default(),
            peak_live_lanes: 0,
            placement_relocations: 0,
        },
        instruction_digest: [0; 4],
        encoded_digest: [0; 4],
    }
}

fn sample_regime() -> BackwardRegimeArtifact {
    BackwardRegimeArtifact {
        plans: (2..=16).map(sample_plan).collect(),
    }
}

fn sample_artifact(layers: Vec<BackwardLayerArtifact>) -> BackwardEvaluationCircuitArtifact {
    BackwardEvaluationCircuitArtifact {
        circuit: "fixture".to_owned(),
        layout_fixture: "fixture_layout".to_owned(),
        layers,
    }
}

#[test]
fn canonical_u128_json_is_a_decimal_string_and_round_trips_the_maximum() {
    let maximum = CanonicalU128::from(u128::MAX);
    assert_eq!(
        serde_json::to_string(&maximum).unwrap(),
        format!("\"{}\"", u128::MAX)
    );
    assert_eq!(
        serde_json::from_str::<CanonicalU128>(&serde_json::to_string(&maximum).unwrap()).unwrap(),
        maximum
    );
}

#[test]
fn canonical_u128_rejects_noncanonical_decimal_spellings() {
    for spelling in ["-1", "+1", "01", "", " 1"] {
        assert!(serde_json::from_str::<CanonicalU128>(&format!("\"{spelling}\"")).is_err());
    }
}

#[test]
fn backward_artifact_requires_strictly_increasing_layers() {
    let regime = sample_regime();
    let artifact = sample_artifact(vec![
        BackwardLayerArtifact {
            layer: 1,
            r0: regime.clone(),
            ext: regime.clone(),
        },
        BackwardLayerArtifact {
            layer: 1,
            r0: regime.clone(),
            ext: regime,
        },
    ]);
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(gkr_eval_isa::eval_plan::BackwardArtifactError::DuplicateOrUnorderedLayer { layer: 1 })
    ));
}

#[test]
fn backward_artifact_requires_every_budget_from_two_through_sixteen() {
    let mut regime = sample_regime();
    regime.plans.pop();
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 0,
        r0: regime.clone(),
        ext: regime,
    }]);
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(
            gkr_eval_isa::eval_plan::BackwardArtifactError::InvalidBudgetCoverage {
                layer: 0,
                regime: BwdRegime::R0,
            }
        )
    ));
}

#[test]
fn backward_artifact_requires_nonempty_identity_fields() {
    let regime = sample_regime();
    let mut artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 0,
        r0: regime.clone(),
        ext: regime,
    }]);
    artifact.circuit.clear();
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(gkr_eval_isa::eval_plan::BackwardArtifactError::CircuitMismatch { .. })
    ));

    artifact.circuit = "fixture".to_owned();
    artifact.layout_fixture.clear();
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(gkr_eval_isa::eval_plan::BackwardArtifactError::LayoutFixtureMismatch { .. })
    ));
}

#[test]
fn backward_artifact_requires_strictly_increasing_retained_demand_indices() {
    let mut regime = sample_regime();
    regime.plans[0].retained_demands = vec![3, 3];
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 0,
        r0: regime.clone(),
        ext: regime,
    }]);
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(
            gkr_eval_isa::eval_plan::BackwardArtifactError::InvalidRetainedDemand {
                layer: 0,
                regime: BwdRegime::R0,
                budget_cells: 2,
                position: 1,
            }
        )
    ));
}

#[test]
fn backward_artifact_rejects_unknown_schema_fields() {
    let regime = sample_regime();
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 0,
        r0: regime.clone(),
        ext: regime,
    }]);
    let mut json = serde_json::to_value(artifact).unwrap();
    json.as_object_mut()
        .unwrap()
        .insert("version".to_owned(), serde_json::json!(1));
    assert!(serde_json::from_value::<BackwardEvaluationCircuitArtifact>(json).is_err());
}

#[test]
fn backward_artifact_loader_rejects_malformed_json() {
    let path = std::env::temp_dir().join(format!(
        "gkr-eval-plan-artifact-malformed-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, b"{").unwrap();
    assert!(matches!(
        load_backward_evaluation_artifact(&path),
        Err(gkr_eval_isa::eval_plan::BackwardArtifactError::Load(_))
    ));
    std::fs::remove_file(path).unwrap();
}

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
    assert_eq!(
        result.telemetry.exact_solver_calls,
        result.telemetry.evaluations
    );
    assert!(!result.telemetry.solver_kinds.is_empty());
}
