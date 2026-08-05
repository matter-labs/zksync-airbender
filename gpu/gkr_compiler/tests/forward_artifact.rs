use std::collections::BTreeMap;

use gkr_eval_ir::{
    BatchingOrder, ClaimInfo, DagCircuit, DagGlobals, DagLayer, Expr, ExprId, FieldKind, ReadPlace,
    Root, RootGroup, RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceId, SourceInfo,
    SourceKind,
};
use gpu_gkr_compiler::forward::artifact::{enumerate_site_domain, relation_units_with_caches};
use gpu_gkr_compiler::{
    ForwardArtifactError, ForwardLayerArtifact, ForwardSearchArtifact, parse_forward_artifact,
    validate_forward_artifact,
};

fn repeated_source_dag() -> DagCircuit {
    DagCircuit {
        layers: vec![DagLayer {
            sources: vec![SourceInfo {
                kind: SourceKind::Read {
                    place: ReadPlace::BaseLayerWitness { column: 0 },
                },
            }],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Add(vec![ExprId(0), ExprId(0)]),
            ],
            roots: vec![Root {
                expr: ExprId(1),
                materialize: Some(SinkInfo {
                    kind: SinkKind::Export { slot: 0 },
                    field: FieldKind::Base,
                }),
                claim: Some(ClaimInfo {
                    origin: RootOrigin {
                        group: RootGroup::Gates,
                        relation_index: 0,
                        slot: RootSlot::Output(0),
                    },
                }),
            }],
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            resolutions: BTreeMap::new(),
        }],
        globals: DagGlobals::default(),
    }
}

fn valid_artifact(dag: &DagCircuit) -> ForwardSearchArtifact {
    let layer = &dag.layers[0];
    ForwardSearchArtifact {
        circuit: "tiny".into(),
        budget: 16,
        layers: vec![ForwardLayerArtifact {
            units: relation_units_with_caches(layer).unwrap(),
            sites: enumerate_site_domain(layer)
                .into_iter()
                .map(|site| (site, 0.5))
                .collect(),
            predicted_traffic: 1,
            floor: 1,
        }],
    }
}

#[test]
fn malformed_bytes_are_a_hard_error() {
    assert!(parse_forward_artifact(b"not json", "test").is_err());
}

#[test]
fn a_mutated_site_identity_is_rejected() {
    let dag = repeated_source_dag();
    let mut artifact = valid_artifact(&dag);
    artifact.layers[0].sites[0].0.root = RootId(9);
    assert!(matches!(
        validate_forward_artifact(&dag, &artifact),
        Err(ForwardArtifactError::SiteDomainMismatch(_))
    ));
}

#[test]
fn a_non_finite_priority_is_rejected() {
    let dag = repeated_source_dag();
    let mut artifact = valid_artifact(&dag);
    artifact.layers[0].sites[0].1 = f64::NAN;
    assert!(matches!(
        validate_forward_artifact(&dag, &artifact),
        Err(ForwardArtifactError::NonFinitePriority(_))
    ));
}

#[test]
fn an_artifact_for_another_dag_is_rejected() {
    let dag = repeated_source_dag();
    let artifact = valid_artifact(&dag);
    let mut other = dag.clone();
    other.layers[0].roots[0].expr = ExprId(0);
    assert!(validate_forward_artifact(&other, &artifact).is_err());
}
