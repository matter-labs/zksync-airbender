use std::collections::BTreeMap;

use gkr_eval_ir::{
    BatchingOrder, ClaimInfo, DagCircuit, DagGlobals, DagLayer, Expr, ExprId, FieldKind, ReadPlace,
    Root, RootGroup, RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceId, SourceInfo,
    SourceKind,
};
use gpu_gkr_compiler::forward::artifact::{enumerate_site_domain, relation_units_with_caches};
use gpu_gkr_compiler::{ForwardLayerArtifact, ForwardSearchArtifact, compile_forward};

fn tiny_dag() -> DagCircuit {
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

#[test]
fn artifact_compiles_without_a_cs_compiler_input() {
    let dag = tiny_dag();
    let layer = &dag.layers[0];
    let artifact = ForwardSearchArtifact {
        circuit: "tiny".into(),
        budget_buckets: 4,
        layers: vec![ForwardLayerArtifact {
            units: relation_units_with_caches(layer).unwrap(),
            sites: enumerate_site_domain(layer)
                .into_iter()
                .map(|site| (site, 0.5))
                .collect(),
            predicted_traffic: 1,
            floor: 1,
        }],
    };

    let program = compile_forward(&dag, &artifact).unwrap();
    assert_eq!(program.layers.len(), dag.layers.len());
    assert!(!program.layers[0].instructions().is_empty());

    let mut stale_cost = artifact;
    stale_cost.layers[0].predicted_traffic += 1;
    assert!(compile_forward(&dag, &stale_cost).is_err());
}
