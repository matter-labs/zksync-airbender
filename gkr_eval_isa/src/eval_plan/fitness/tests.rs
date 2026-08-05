use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::{DagLayer, ExprId, FieldKind, RootId, lower_dag, validate};

use crate::eval_plan::{
    EvaluationGenome, EvaluationLayoutVariant, LANES_PER_STORAGE_CELL, PackConfig,
    PlanSearchContext, bind_packed_plan, compile_layer_with_evaluation_genome,
    load_evaluation_genome_artifact, pack_plan,
};
use crate::fwd::compile::{build_cross_layer_field_map, expr_operand_field};
use crate::fwd::context::{ForwardAction, build_forward_actions};
use crate::fwd::isa::OperandField;
use crate::schedule::relation_units_with_caches;

use super::{
    EvaluationUnit, EvaluationUnitKey, FitnessError, adapt_forward_relations, root_key, sort_roots,
    unit_cmp,
};

const CORPUS: &[(&str, &str)] = &[
    (
        "add_sub_lui_auipc_mop",
        "add_sub_lui_auipc_mop_layout_gkr.json",
    ),
    (
        "bigint_with_extended_control",
        "bigint_with_extended_control_layout_gkr.json",
    ),
    ("blake2_g_function", "blake2_g_function_layout_gkr.json"),
    (
        "blake2_with_extended_control",
        "blake2_with_extended_control_layout_gkr.json",
    ),
    (
        "inits_and_teardowns",
        "inits_and_teardowns_preprocessed_layout_gkr.json",
    ),
    ("jump_branch_slt", "jump_branch_slt_layout_gkr.json"),
    ("keccak_special5", "keccak_special5_layout_gkr.json"),
    ("mem_subword_only", "mem_subword_only_layout_gkr.json"),
    ("mem_word_only", "mem_word_only_layout_gkr.json"),
    ("shift_binop", "shift_binop_layout_gkr.json"),
    ("unsigned_mul_div", "unsigned_mul_div_layout_gkr.json"),
];

fn compiled_circuit_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits")
}

fn load_fixture(name: &str) -> GKRCircuitArtifact<BabyBearField> {
    let path = compiled_circuit_dir().join(name);
    let bytes =
        std::fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    serde_json::from_slice(&bytes)
        .unwrap_or_else(|error| panic!("parse {}: {error}", path.display()))
}

fn expr_fields(
    layer: &DagLayer,
    cross: &std::collections::HashMap<gkr_eval_ir::ReadPlace, FieldKind>,
) -> Vec<FieldKind> {
    (0..layer.exprs.len())
        .map(
            |index| match expr_operand_field(layer, ExprId(index as u32), cross) {
                OperandField::Base => FieldKind::Base,
                OperandField::Ext => FieldKind::Ext,
            },
        )
        .collect()
}

// Frozen pre-Plan-1 constructor. This is deliberately test-local: production
// planning must have exactly one forward-unit boundary, the relation adapter.
fn pre_plan1_units(layer: &DagLayer) -> Result<Vec<EvaluationUnit>, FitnessError> {
    let fingerprints = super::structural_fingerprints(layer)
        .map_err(super::PlanError::from)
        .map_err(FitnessError::Plan)?;
    let canonical = relation_units_with_caches(layer).map_err(FitnessError::UnitConstruction)?;
    let mut included = vec![false; layer.roots.len()];
    let mut units = Vec::with_capacity(canonical.len());

    for relation in canonical {
        let mut cache_roots = relation.cache_roots;
        let mut atom_roots = relation.atom_roots;
        sort_roots(layer, &fingerprints, &mut cache_roots);
        sort_roots(layer, &fingerprints, &mut atom_roots);
        for root in cache_roots.iter().chain(&atom_roots) {
            included[root.0 as usize] = true;
        }
        units.push(EvaluationUnit {
            key: EvaluationUnitKey::Relation {
                group: relation.group,
                relation_index: relation.relation_index,
            },
            roots: atom_roots,
        });
    }

    for (index, root) in layer.roots.iter().enumerate() {
        if root.materialize.is_none() || included[index] {
            continue;
        }
        let root_id = RootId(index as u32);
        units.push(EvaluationUnit {
            key: EvaluationUnitKey::Standalone(root_key(layer, &fingerprints, root_id)),
            roots: vec![root_id],
        });
    }
    units.sort_by(unit_cmp);
    Ok(units)
}

#[test]
fn forward_adapter_corpus_parity() {
    for &(circuit, fixture) in CORPUS {
        let layout = load_fixture(fixture);
        let dag =
            lower_dag(&layout).unwrap_or_else(|error| panic!("{fixture}: lower DAG: {error}"));
        validate(&dag).unwrap_or_else(|error| panic!("{fixture}: validate DAG: {error}"));
        let cross = build_cross_layer_field_map(&dag);
        let artifact_path =
            compiled_circuit_dir().join(format!("{circuit}_with_caches_fwd_eval_plan_c4_gkr.json"));
        let committed = load_evaluation_genome_artifact(&artifact_path).unwrap_or_else(|error| {
            panic!("{fixture}: load {}: {error:?}", artifact_path.display())
        });

        assert_eq!(
            layout.layers.len(),
            dag.layers.len(),
            "{fixture}: layout layer count"
        );
        assert_eq!(
            committed.layout_variant,
            EvaluationLayoutVariant::WithCaches,
            "{fixture}: artifact variant"
        );
        assert_eq!(committed.budget_cells, 4, "{fixture}: committed c4 budget");
        assert_eq!(
            committed.layers.len(),
            dag.layers.len(),
            "{fixture}: artifact layer count"
        );

        for (layer_index, ((layer, layout_layer), committed_layer)) in dag
            .layers
            .iter()
            .zip(&layout.layers)
            .zip(&committed.layers)
            .enumerate()
        {
            let expected = pre_plan1_units(layer).unwrap();
            let actual = adapt_forward_relations(layer).unwrap();
            assert_eq!(actual, expected, "{fixture} L{layer_index}");

            let actions = build_forward_actions(layer, layout_layer, &layout.scratch_space_mapping)
                .unwrap_or_else(|error| panic!("{fixture} L{layer_index}: actions: {error:?}"));
            let compute_roots = actions
                .iter()
                .filter_map(|(&root, action)| {
                    matches!(action, ForwardAction::Compute).then_some(root)
                })
                .collect::<Vec<_>>();
            let fields = expr_fields(layer, &cross);

            for budget_cells in [2, 3, 4] {
                let old_context = PlanSearchContext::build_selected_with_units(
                    layer,
                    &fields,
                    layout_layer.layer,
                    budget_cells,
                    Some(&compute_roots),
                    expected.clone(),
                )
                .unwrap_or_else(|error| {
                    panic!("{fixture} L{layer_index} c{budget_cells}: old context: {error:?}")
                });
                let new_context = PlanSearchContext::build_for_roots(
                    layer,
                    &fields,
                    layout_layer.layer,
                    budget_cells,
                    &compute_roots,
                )
                .unwrap_or_else(|error| {
                    panic!("{fixture} L{layer_index} c{budget_cells}: new context: {error:?}")
                });
                let old_genome = EvaluationGenome::neutral(&old_context);
                let new_genome = EvaluationGenome::neutral(&new_context);
                assert_eq!(
                    new_genome, old_genome,
                    "{fixture} L{layer_index} c{budget_cells}: neutral genome"
                );

                let old_score = old_context.score(&old_genome).unwrap();
                let new_score = new_context.score(&new_genome).unwrap();
                assert_eq!(
                    new_score.root_order, old_score.root_order,
                    "{fixture} L{layer_index} c{budget_cells}: root order"
                );
                assert_eq!(
                    new_score.fitness, old_score.fitness,
                    "{fixture} L{layer_index} c{budget_cells}: fitness"
                );
                assert_eq!(
                    new_score.placement, old_score.placement,
                    "{fixture} L{layer_index} c{budget_cells}: placement"
                );

                match (old_score.plan.as_ref(), new_score.plan.as_ref()) {
                    (None, None) => {}
                    (Some(old_plan), Some(new_plan)) => {
                        let old_packed = pack_plan(old_plan, layer, PackConfig::default()).unwrap();
                        let new_packed = pack_plan(new_plan, layer, PackConfig::default()).unwrap();
                        assert_eq!(
                            new_packed, old_packed,
                            "{fixture} L{layer_index} c{budget_cells}: packed plan"
                        );
                        let old_concrete = bind_packed_plan(
                            &old_packed,
                            layer,
                            old_context.materialized_roots(),
                            layout_layer.layer,
                            budget_cells * LANES_PER_STORAGE_CELL,
                        )
                        .unwrap();
                        let new_concrete = bind_packed_plan(
                            &new_packed,
                            layer,
                            new_context.materialized_roots(),
                            layout_layer.layer,
                            budget_cells * LANES_PER_STORAGE_CELL,
                        )
                        .unwrap();
                        assert_eq!(
                            new_concrete.encoded, old_concrete.encoded,
                            "{fixture} L{layer_index} c{budget_cells}: encoded program"
                        );
                    }
                    _ => panic!("{fixture} L{layer_index} c{budget_cells}: plan feasibility drift"),
                }
                if budget_cells == 4 {
                    let compiled = compile_layer_with_evaluation_genome(
                        circuit,
                        layer,
                        layout_layer,
                        &layout.scratch_space_mapping,
                        &cross,
                        budget_cells,
                        committed_layer,
                    )
                    .unwrap_or_else(|error| {
                        panic!("{fixture} L{layer_index}: committed artifact: {error:?}")
                    });
                    assert_eq!(
                        compiled.fitness, committed_layer.expected_fitness,
                        "{fixture} L{layer_index}: fitness certificate"
                    );
                    assert_eq!(
                        compiled.concrete.compiled.stats.program_lanes,
                        committed_layer.expected_fitness.program_instructions,
                        "{fixture} L{layer_index}: instruction certificate"
                    );
                    assert_eq!(
                        compiled.concrete.stats.encoded_lanes,
                        committed_layer.expected_fitness.encoded_lanes,
                        "{fixture} L{layer_index}: encoding certificate"
                    );
                    assert_eq!(
                        compiled.concrete.compiled.stats.dram_traffic,
                        committed_layer.expected_fitness.dram_read_lanes,
                        "{fixture} L{layer_index}: traffic certificate"
                    );

                    let adapter_context = PlanSearchContext::build_for_roots(
                        layer,
                        &fields,
                        layout_layer.layer,
                        budget_cells,
                        &compute_roots,
                    )
                    .unwrap();
                    committed_layer
                        .validate_against(circuit, &adapter_context, &actions)
                        .unwrap_or_else(|error| {
                            panic!("{fixture} L{layer_index}: domain certificates: {error:?}")
                        });
                    let artifact_score = adapter_context.score(&committed_layer.genome).unwrap();
                    assert_eq!(
                        artifact_score.fitness.arithmetic_ops,
                        committed_layer.expected_fitness.arithmetic_ops,
                        "{fixture} L{layer_index}: arithmetic certificate"
                    );
                }
            }
        }
    }
}

#[test]
fn forward_adapter_rejects_invalid_selected_root() {
    let layout = load_fixture(CORPUS[0].1);
    let dag = lower_dag(&layout).unwrap();
    let layer = &dag.layers[0];
    let error = match PlanSearchContext::build_for_roots(
        layer,
        &vec![FieldKind::Base; layer.exprs.len()],
        0,
        2,
        &[RootId(layer.roots.len() as u32)],
    ) {
        Err(error) => error,
        Ok(_) => panic!("out-of-range root must be rejected"),
    };
    assert!(
        matches!(error, FitnessError::UnitConstruction(message) if message.contains(&layer.roots.len().to_string()))
    );
}

#[test]
fn forward_adapter_rejects_unmaterialized_selected_root() {
    let layout = load_fixture(CORPUS[0].1);
    let dag = lower_dag(&layout).unwrap();
    let layer = &dag.layers[0];
    let root = layer
        .roots
        .iter()
        .position(|root| root.materialize.is_none() && root.claim.is_some())
        .expect("fixture has a claim-only root");
    let error = match PlanSearchContext::build_for_roots(
        layer,
        &vec![FieldKind::Base; layer.exprs.len()],
        0,
        2,
        &[RootId(root as u32)],
    ) {
        Err(error) => error,
        Ok(_) => panic!("claim-only root must be rejected"),
    };
    assert!(
        matches!(error, FitnessError::UnitConstruction(message) if message.contains(&root.to_string()))
    );
}

#[test]
fn plan_search_context_exposes_cells_and_derives_lanes() {
    let layout = load_fixture(CORPUS[0].1);
    let dag = lower_dag(&layout).expect("lower fixture");
    let layer = &dag.layers[0];
    let cross = build_cross_layer_field_map(&dag);
    let fields = expr_fields(layer, &cross);
    let context = PlanSearchContext::build(layer, &fields, 0, 4).expect("build four-cell context");

    assert_eq!(context.budget_cells(), 4);
    assert_eq!(context.budget_lanes(), 16);
}

#[test]
fn plan_search_context_rejects_invalid_cell_budgets() {
    let layout = load_fixture(CORPUS[0].1);
    let dag = lower_dag(&layout).expect("lower fixture");
    let layer = &dag.layers[0];
    let cross = build_cross_layer_field_map(&dag);
    let fields = expr_fields(layer, &cross);

    for budget_cells in [0, crate::fwd::isa::MAX_CELL as usize / 4 + 1, usize::MAX] {
        assert!(matches!(
            PlanSearchContext::build(layer, &fields, 0, budget_cells),
            Err(FitnessError::BudgetCellsOutOfRange {
                budget_cells: actual,
            }) if actual == budget_cells
        ));
    }
}
