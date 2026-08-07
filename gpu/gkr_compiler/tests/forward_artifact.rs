use std::collections::BTreeMap;

use gkr_eval_ir::{
    BatchingOrder, DagCircuit, DagLayer, Expr, ExprId, FieldKind, ReadPlace, Root, RootGroup,
    RootId, RootOrigin, SinkInfo, SinkKind, SourceId, SourceKind,
};
use gpu_gkr_compiler::{
    compile_forward, parse_forward_artifact, ForwardLayerArtifact, ForwardSearchArtifact,
    RelationUnit, SiteConsumer, SiteKey,
};

fn repeated_source_dag() -> DagCircuit {
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

fn valid_artifact(dag: &DagCircuit) -> ForwardSearchArtifact {
    assert_eq!(dag.layers.len(), 1);
    ForwardSearchArtifact {
        circuit: "tiny".into(),
        budget_buckets: 4,
        layers: vec![ForwardLayerArtifact {
            units: vec![RelationUnit {
                group: RootGroup::Gates,
                relation_index: 0,
            }],
            sites: (0..2)
                .map(|input_index| {
                    (
                        SiteKey {
                            root: RootId(0),
                            consumer: SiteConsumer::Expr {
                                expr: ExprId(1),
                                input_index,
                            },
                            value: ExprId(0),
                        },
                        0.5,
                    )
                })
                .collect(),
            predicted_traffic: 1,
        }],
    }
}

#[test]
fn malformed_bytes_are_a_hard_error() {
    assert!(parse_forward_artifact(b"not json", "test").is_err());
}

#[test]
fn unknown_artifact_fields_are_rejected() {
    let mut artifact = serde_json::to_value(valid_artifact(&repeated_source_dag())).unwrap();
    artifact
        .as_object_mut()
        .unwrap()
        .insert("unexpected".into(), 1.into());
    assert!(parse_forward_artifact(&serde_json::to_vec(&artifact).unwrap(), "test").is_err());
}

#[test]
fn a_mutated_site_identity_is_rejected() {
    let dag = repeated_source_dag();
    let mut artifact = valid_artifact(&dag);
    artifact.layers[0].sites[0].0.root = RootId(9);
    assert!(compile_forward(&dag, &artifact).is_err());
}

#[test]
fn a_priority_outside_the_search_domain_is_rejected() {
    let dag = repeated_source_dag();
    let mut artifact = valid_artifact(&dag);
    artifact.layers[0].sites[0].1 = 2.0;
    assert!(compile_forward(&dag, &artifact).is_err());
}

#[test]
fn an_artifact_for_another_dag_is_rejected() {
    let dag = repeated_source_dag();
    let artifact = valid_artifact(&dag);
    let mut other = dag.clone();
    other.layers[0].roots[0].expr = ExprId(0);
    assert!(compile_forward(&other, &artifact).is_err());
}

#[test]
fn artifact_compiles_and_checks_its_retained_cost() {
    let dag = repeated_source_dag();
    let artifact = valid_artifact(&dag);
    let program = compile_forward(&dag, &artifact).unwrap();
    assert!(!program.layers[0].program.instrs.is_empty());

    let mut stale = artifact;
    stale.layers[0].predicted_traffic += 1;
    assert!(compile_forward(&dag, &stale).is_err());
}
