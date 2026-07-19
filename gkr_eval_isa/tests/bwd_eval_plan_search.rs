mod common;

use std::collections::{BTreeMap, HashMap};

use common::assert_bwd_value_parity;
use cs::gkr_compiler::dag_ir::{
    BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup,
    RootId, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
};
use gkr_eval_isa::bwd::distill::{DistilledLayer, distill};
use gkr_eval_isa::eval_plan::backward_search::problem::build_backward_search_problem;
use gkr_eval_isa::eval_plan::backward_search::{
    CertifiedBackwardCandidate, MAX_PAGER_STATES, PagerOutcome, compile_and_certify_paging,
    solve_exact_paging,
};
use gkr_eval_isa::fwd::encode::{decode, encode};

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
