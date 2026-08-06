use std::collections::BTreeMap;

use gkr_eval_ir::{
    BatchingOrder, ClaimInfo, DagCircuit, DagGlobals, DagLayer, Expr, ExprId, FieldKind, ReadPlace,
    Root, RootGroup, RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceId, SourceInfo,
    SourceKind,
};
use gpu_gkr_compiler::{
    CrossoverKind, ForwardResourceProfile, ForwardSearchRequest, SearchConfig, search_forward,
};

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

fn config() -> SearchConfig {
    SearchConfig {
        population: 2,
        evaluations: 8,
        tournament: 2,
        elitism: 1,
        crossover_rate: 0.9,
        mutation_rate: 0.1,
        mutation_sigma: 0.15,
        local_steps: 0,
        local_elite: 0,
        crossover: CrossoverKind::Order,
    }
}

#[test]
fn fixed_inputs_produce_identical_artifacts() {
    let dag = tiny_dag();
    let run = || {
        search_forward(ForwardSearchRequest {
            circuit: "tiny",
            dag: &dag,
            resources: ForwardResourceProfile { cache_buckets: 4 },
            config: config(),
            seed: 7,
            incumbent: None,
        })
        .unwrap()
    };
    assert_eq!(run(), run());
}

#[test]
fn a_valid_incumbent_cannot_be_silently_ignored() {
    let dag = tiny_dag();
    let request = |incumbent| ForwardSearchRequest {
        circuit: "tiny",
        dag: &dag,
        resources: ForwardResourceProfile { cache_buckets: 4 },
        config: config(),
        seed: 7,
        incumbent,
    };
    let incumbent = search_forward(request(None)).unwrap();
    let refined = search_forward(request(Some(&incumbent))).unwrap();
    let objective = |artifact: &gpu_gkr_compiler::ForwardSearchArtifact| {
        artifact
            .layers
            .iter()
            .map(|layer| layer.predicted_traffic)
            .sum::<usize>()
    };
    assert!(objective(&refined) <= objective(&incumbent));
}

#[test]
fn a_stale_incumbent_is_rejected_before_search() {
    let dag = tiny_dag();
    let mut incumbent = search_forward(ForwardSearchRequest {
        circuit: "tiny",
        dag: &dag,
        resources: ForwardResourceProfile { cache_buckets: 4 },
        config: config(),
        seed: 7,
        incumbent: None,
    })
    .unwrap();
    incumbent.layers[0].units[0].atom_roots[0] = RootId(9);
    assert!(
        search_forward(ForwardSearchRequest {
            circuit: "tiny",
            dag: &dag,
            resources: ForwardResourceProfile { cache_buckets: 4 },
            config: config(),
            seed: 7,
            incumbent: Some(&incumbent),
        })
        .is_err()
    );
}
