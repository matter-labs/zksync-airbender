use std::collections::BTreeMap;

use gkr_eval_ir::{
    BatchingOrder, DagCircuit, DagLayer, Expr, ExprId, FieldKind, ReadPlace, Root, RootGroup,
    RootId, RootOrigin, SinkInfo, SinkKind, SourceId, SourceKind,
};
use gpu_gkr_compiler::{compile_forward, search_forward, ForwardSearchRequest, SearchConfig};

fn tiny_dag() -> DagCircuit {
    DagCircuit {
        layers: vec![DagLayer {
            sources: vec![SourceKind::Read {
                place: ReadPlace::BaseLayerWitness { column: 0 },
            }],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Add(vec![ExprId(0), ExprId(0)]),
            ],
            roots: vec![Root {
                expr: ExprId(1),
                materialize: Some(SinkInfo {
                    kind: SinkKind::Inner {
                        layer: 0,
                        offset: 0,
                    },
                    field: FieldKind::Base,
                }),
                claim: Some(RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                }),
            }],
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            resolutions: BTreeMap::new(),
            forward_skip_roots: Default::default(),
        }],
    }
}

fn shared_expr_dag() -> DagCircuit {
    let mut dag = tiny_dag();
    let mut second = dag.layers[0].roots[0];
    second.materialize.as_mut().unwrap().kind = SinkKind::Inner {
        layer: 0,
        offset: 1,
    };
    second.claim.as_mut().unwrap().relation_index = 1;
    dag.layers[0].roots.push(second);
    dag.layers[0].batching.roots.push(RootId(1));
    dag
}

fn with_claim_only_root(mut dag: DagCircuit) -> DagCircuit {
    dag.layers[0].roots.push(Root {
        expr: ExprId(1),
        materialize: None,
        claim: Some(RootOrigin {
            group: RootGroup::Gates,
            relation_index: 1,
        }),
    });
    dag.layers[0].batching.roots.push(RootId(1));
    dag
}

fn config() -> SearchConfig {
    SearchConfig {
        population: 2,
        evaluations: 8,
        tournament: 2,
        elitism: 1,
        crossover_rate: 0.9,
        mutation_rate: 0.1,
        mutation_sigma: 0.15,
    }
}

#[test]
fn fixed_inputs_produce_identical_artifacts() {
    let dag = tiny_dag();
    let run = || {
        search_forward(ForwardSearchRequest {
            circuit: "tiny",
            dag: &dag,
            cache_buckets: 4,
            config: config(),
            seed: 7,
            incumbent: None,
        })
        .unwrap()
    };
    assert_eq!(run(), run());
}

#[test]
fn shared_expressions_allow_reordered_relations() {
    search_forward(ForwardSearchRequest {
        circuit: "shared",
        dag: &shared_expr_dag(),
        cache_buckets: 4,
        config: config(),
        seed: 7,
        incumbent: None,
    })
    .unwrap();
}

#[test]
fn claim_only_roots_are_not_forward_units() {
    search_forward(ForwardSearchRequest {
        circuit: "claim-only",
        dag: &with_claim_only_root(tiny_dag()),
        cache_buckets: 4,
        config: config(),
        seed: 7,
        incumbent: None,
    })
    .unwrap();
}

#[test]
fn search_does_not_regress_a_valid_incumbent() {
    let dag = tiny_dag();
    let incumbent = search_forward(ForwardSearchRequest {
        circuit: "tiny",
        dag: &dag,
        cache_buckets: 4,
        config: config(),
        seed: 3,
        incumbent: None,
    })
    .unwrap();
    let result = search_forward(ForwardSearchRequest {
        circuit: "tiny",
        dag: &dag,
        cache_buckets: 4,
        config: config(),
        seed: 11,
        incumbent: Some(&incumbent),
    })
    .unwrap();
    let score = |artifact| {
        let layer = &compile_forward(&dag, artifact).unwrap().layers[0];
        (
            artifact.layers[0].predicted_traffic,
            layer.program.instrs.len(),
        )
    };
    assert!(score(&result) <= score(&incumbent));
}

#[test]
fn a_stale_incumbent_is_rejected_before_search() {
    let dag = tiny_dag();
    let mut incumbent = search_forward(ForwardSearchRequest {
        circuit: "tiny",
        dag: &dag,
        cache_buckets: 4,
        config: config(),
        seed: 7,
        incumbent: None,
    })
    .unwrap();
    incumbent.layers[0].units[0].relation_index = 9;
    assert!(search_forward(ForwardSearchRequest {
        circuit: "tiny",
        dag: &dag,
        cache_buckets: 4,
        config: config(),
        seed: 7,
        incumbent: Some(&incumbent),
    })
    .is_err());
}

#[test]
fn a_materialize_only_layer_is_rejected_before_search() {
    let mut dag = tiny_dag();
    dag.layers[0].roots[0].claim = None;
    dag.layers[0].batching.roots.clear();
    assert!(search_forward(ForwardSearchRequest {
        circuit: "tiny",
        dag: &dag,
        cache_buckets: 4,
        config: config(),
        seed: 7,
        incumbent: None,
    })
    .is_err());
}
