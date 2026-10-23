use std::collections::BTreeMap;

use field::baby_bear::base::BabyBearField;
use field::proth120::Proth120;
use field::PrimeField;
use gkr_eval_ir::{
    BatchingOrder, DagCircuit, DagLayer, Expr, ExprId, FieldKind, ReadPlace, Root, RootGroup,
    RootId, RootOrigin, SinkInfo, SinkKind, SourceId, SourceKind,
};
use gpu_gkr_compiler::{
    compile_forward, parse_forward_artifact, ElementModel, FieldTag, ForwardLayerArtifact,
    ForwardSearchArtifact, RelationUnit, SiteConsumer, SiteKey,
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
        modulus: BabyBearField::CHARACTERISTICS_U128,
    }
}

fn valid_artifact(dag: &DagCircuit) -> ForwardSearchArtifact {
    assert_eq!(dag.layers.len(), 1);
    ForwardSearchArtifact {
        circuit: "tiny".into(),
        budget_buckets: 4,
        field: None,
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

#[test]
fn field_tag_round_trip_and_untagged_identity() {
    let dag = repeated_source_dag();
    let mut artifact = valid_artifact(&dag);
    let bytes = serde_json::to_vec(&artifact).unwrap();
    assert!(!String::from_utf8(bytes.clone())
        .unwrap()
        .contains("\"field\""));
    assert_eq!(
        parse_forward_artifact(&bytes, "untagged").unwrap().field,
        None
    );
    artifact.field = Some(FieldTag::Proth120);
    let bytes = serde_json::to_vec(&artifact).unwrap();
    assert_eq!(parse_forward_artifact(&bytes, "tagged").unwrap(), artifact);
    assert!(String::from_utf8(bytes)
        .unwrap()
        .contains("\"field\":\"proth120\""));
}

#[test]
fn field_tag_mismatch_names_both_fields() {
    let mut dag = repeated_source_dag();
    let mut artifact = valid_artifact(&dag);
    artifact.field = Some(FieldTag::Proth120);
    let failure = format!("{:?}", compile_forward(&dag, &artifact).unwrap_err());
    assert!(
        failure.contains("Some(Proth120)") && failure.contains("None"),
        "{failure}"
    );
    dag.modulus = Proth120::CHARACTERISTICS_U128;
    artifact.field = None;
    let failure = format!("{:?}", compile_forward(&dag, &artifact).unwrap_err());
    assert!(
        failure.contains("Some(Proth120)") && failure.contains("None"),
        "{failure}"
    );
}

#[test]
fn proth120_constants_use_the_model_minus_one() {
    let mut dag = repeated_source_dag();
    dag.modulus = Proth120::CHARACTERISTICS_U128;
    let layer = &mut dag.layers[0];
    layer.sources = vec![
        SourceKind::Constant {
            value: ElementModel::BABYBEAR.minus_one,
        },
        SourceKind::Constant {
            value: (1u128 << 80) + 7,
        },
        SourceKind::Constant {
            value: ElementModel::PROTH120.minus_one,
        },
    ];
    layer.exprs = (0..3).map(|index| Expr::Source(SourceId(index))).collect();
    layer
        .exprs
        .push(Expr::Add(vec![ExprId(0), ExprId(1), ExprId(2)]));
    layer.roots[0].expr = ExprId(3);
    let mut artifact = valid_artifact(&dag);
    artifact.field = Some(FieldTag::Proth120);
    artifact.layers[0].sites.clear();
    artifact.layers[0].predicted_traffic = 0;
    let program = compile_forward(&dag, &artifact).unwrap();
    assert_eq!(
        program.layers[0].consts.values(),
        &[ElementModel::BABYBEAR.minus_one, (1u128 << 80) + 7]
    );
    assert_eq!(ElementModel::for_dag(&dag), ElementModel::PROTH120);
}

#[test]
#[should_panic(expected = "ElementModel: unsupported DAG modulus 17")]
fn unsupported_modulus_has_a_named_panic() {
    let mut dag = repeated_source_dag();
    dag.modulus = 17;
    ElementModel::for_dag(&dag);
}
