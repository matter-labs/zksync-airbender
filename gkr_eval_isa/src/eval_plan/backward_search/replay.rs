use std::collections::{BTreeMap, BTreeSet, VecDeque};

use cs::gkr_compiler::dag_ir::ExprId;

use crate::bwd::distill::DistilledLayer;
use crate::bwd::plan::{BwdOccurrencePlan, PlanAction, PlanEntry, plan_entries_fnv};
use crate::bwd::trace::{
    BwdEvent, BwdFingerprint, BwdServeKind, positioned_physical_traffic_events,
};
use crate::eval_plan::backward::{
    BackwardEvaluationError, CompiledBackwardEvaluation, compile_backward_fragments_replayed,
};
use crate::fwd::stats::{OP_ADD, OP_FMA, OP_MUL};

use super::pager::{ExactPagingPlan, PagingAction};
use super::problem::{BackwardDemand, BackwardSearchProblem};
use super::{BackwardScore, BackwardSearchError, SourceCost, miss_cost};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PagingCertificate {
    pub actions_consumed: usize,
    pub diverged: Option<usize>,
    pub refused_retains: usize,
    pub predicted_source_reads: u64,
    pub realized_source_reads: u64,
    pub predicted_read_cost: SourceCost,
    pub realized_read_cost: SourceCost,
    pub fixed_write_cost: SourceCost,
    pub peak_live_lanes: usize,
    pub placement_relocations: usize,
}

pub struct CertifiedBackwardCandidate {
    pub paging: ExactPagingPlan,
    pub occurrence_plan: BwdOccurrencePlan,
    pub compiled: CompiledBackwardEvaluation,
    pub certificate: PagingCertificate,
    pub score: BackwardScore,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct BwdFingerprintOrderKey {
    term: u32,
    kind: u8,
    value: u32,
    consumer: Option<u32>,
}

impl From<BwdFingerprint> for BwdFingerprintOrderKey {
    fn from(fp: BwdFingerprint) -> Self {
        Self {
            term: fp.term,
            kind: match fp.kind {
                BwdServeKind::RootOutput => 0,
                BwdServeKind::Operand => 1,
            },
            value: fp.value.0,
            consumer: fp.consumer.map(|expr| expr.0),
        }
    }
}

pub fn occurrence_plan_from_paging(
    problem: &BackwardSearchProblem,
    paging: &ExactPagingPlan,
) -> Result<BwdOccurrencePlan, BackwardSearchError> {
    if paging.actions.len() != problem.demands.len() {
        return Err(BackwardSearchError::PagingActionCount {
            expected: problem.demands.len(),
            actual: paging.actions.len(),
        });
    }

    let mut actions = BTreeMap::<BwdFingerprintOrderKey, VecDeque<PagingAction>>::new();
    for (demand, action) in problem.demands.iter().zip(&paging.actions) {
        actions
            .entry(demand.fp.into())
            .or_default()
            .push_back(*action);
    }
    let eligible = actions.keys().copied().collect::<BTreeSet<_>>();
    let mut entries = Vec::with_capacity(problem.all_domain_serves.len());
    for (serve, &fp) in problem.all_domain_serves.iter().enumerate() {
        let key = fp.into();
        let action = if eligible.contains(&key) {
            actions
                .get_mut(&key)
                .and_then(VecDeque::pop_front)
                .ok_or(BackwardSearchError::PagingActionUnderflow { serve })?
        } else {
            PagingAction::Bypass
        };
        entries.push(PlanEntry {
            fp,
            action: match action {
                PagingAction::Bypass => PlanAction::Bypass,
                PagingAction::Retain => PlanAction::Retain,
            },
        });
    }
    let remaining = actions.values().try_fold(0usize, |count, queue| {
        count
            .checked_add(queue.len())
            .ok_or(BackwardSearchError::CostOverflow)
    })?;
    if remaining != 0 {
        return Err(BackwardSearchError::PagingActionLeftover { remaining });
    }

    Ok(BwdOccurrencePlan {
        epoch: problem.epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions: problem.stream_reductions,
        entries,
    })
}

pub fn compile_and_certify_paging(
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    paging: &ExactPagingPlan,
    ordinal: usize,
) -> Result<CertifiedBackwardCandidate, BackwardSearchError> {
    let occurrence_plan = occurrence_plan_from_paging(problem, paging)?;
    let predicted = predict_paging(problem, paging)?;
    let compiled = compile_backward_fragments_replayed(
        d,
        &occurrence_plan,
        Some(&problem.selected_order_indices),
        problem.budget_cells,
    )
    .map_err(map_replay_error)?;

    let diverged = compiled.trace.events.iter().find_map(|event| match event {
        BwdEvent::Diverge { at_entry } => Some(*at_entry),
        _ => None,
    });
    if let Some(at_entry) = diverged {
        return Err(BackwardSearchError::PagingReplayDiverged { at_entry });
    }
    let refused_retains = compiled
        .trace
        .events
        .iter()
        .filter(|event| matches!(event, BwdEvent::Refuse { .. }))
        .count();
    if refused_retains != 0 {
        return Err(BackwardSearchError::PagingReplayRefused {
            count: refused_retains,
        });
    }

    let (realized_profile, peak_live_lanes) = realized_occupancy_profile(problem, &compiled)?;
    if realized_profile.len() != paging.live_lanes_after.len() {
        return Err(BackwardSearchError::PagingCertificateMismatch {
            observable: "occupancy profile length",
        });
    }
    for (position, (&predicted_live, &realized_live)) in paging
        .live_lanes_after
        .iter()
        .zip(&realized_profile)
        .enumerate()
    {
        if usize::from(predicted_live) != realized_live {
            return Err(BackwardSearchError::PagingOccupancyMismatch {
                position,
                predicted: usize::from(predicted_live),
                realized: realized_live,
            });
        }
        if realized_live > problem.budget_lanes {
            return Err(BackwardSearchError::PagingOccupancyMismatch {
                position,
                predicted: problem.budget_lanes,
                realized: realized_live,
            });
        }
    }

    let physical = positioned_physical_traffic_events(
        &d.layer,
        &compiled.compiled.program,
        &compiled.compiled.specials,
        &d.leaf_descs,
        &compiled.compiled.backings,
    )
    .ok_or(BackwardSearchError::PagingCertificateMismatch {
        observable: "physical traffic source mapping",
    })?;
    let sources = controlled_sources(&problem.demands)?;
    let realized_reads = physical
        .iter()
        .filter_map(|positioned| match positioned.event {
            BwdEvent::TrafficRead { value, cells } if sources.contains_key(&value) => {
                Some((value, cells))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let realized_width_lanes = realized_reads.iter().try_fold(0u64, |total, (_, cells)| {
        total
            .checked_add(u64::from(*cells))
            .ok_or(BackwardSearchError::CostOverflow)
    })?;
    let predicted_width_lanes = predicted
        .accesses
        .iter()
        .try_fold(0u64, |total, (_, width)| {
            total
                .checked_add(u64::from(*width))
                .ok_or(BackwardSearchError::CostOverflow)
        })?;
    let predicted_accesses = access_histogram(
        predicted
            .accesses
            .iter()
            .map(|&(value, width)| (value, u32::from(width))),
    )?;
    let realized_accesses = access_histogram(realized_reads.iter().copied())?;
    if realized_accesses != predicted_accesses {
        return Err(BackwardSearchError::PagingSourceAccessMismatch {
            predicted_reads: predicted.reads,
            realized_reads: realized_reads
                .len()
                .try_into()
                .map_err(|_| BackwardSearchError::CostOverflow)?,
            predicted_width_lanes,
            realized_width_lanes,
        });
    }
    let realized_read_cost =
        realized_reads
            .iter()
            .try_fold(SourceCost::default(), |cost, (value, cells)| {
                let (width, source_desc) = sources[value];
                if u32::from(width) != *cells {
                    return Err(BackwardSearchError::PagingSourceAccessMismatch {
                        predicted_reads: predicted.reads,
                        realized_reads: realized_reads
                            .len()
                            .try_into()
                            .map_err(|_| BackwardSearchError::CostOverflow)?,
                        predicted_width_lanes,
                        realized_width_lanes,
                    });
                }
                cost.checked_add(reprice_source_read(problem, source_desc, width)?)
            })?;
    if realized_read_cost != predicted.cost {
        return Err(BackwardSearchError::PagingReadCostMismatch {
            predicted: predicted.cost,
            realized: realized_read_cost,
        });
    }

    let fixed_write_cost = problem.materialization.fixed_writes;
    if problem.fixed_cost != fixed_write_cost {
        return Err(BackwardSearchError::PagingWriteCostMismatch {
            predicted: problem.fixed_cost,
            realized: fixed_write_cost,
        });
    }
    if compiled.binding_stats.max_live_lanes > problem.budget_lanes {
        return Err(BackwardSearchError::PlacementIntegrationFailure);
    }

    let whole_pass_read_cost =
        physical
            .iter()
            .try_fold(SourceCost::default(), |cost, positioned| {
                let BwdEvent::TrafficRead { value, cells } = positioned.event else {
                    unreachable!("the physical traffic scan emits only TrafficRead events");
                };
                let width_lanes = cells
                    .try_into()
                    .map_err(|_| BackwardSearchError::CostOverflow)?;
                cost.checked_add(reprice_source_read(
                    problem,
                    d.leaf_descs.get(&value).copied(),
                    width_lanes,
                )?)
            })?;
    let whole_pass_cost = whole_pass_read_cost.checked_add(fixed_write_cost)?;
    let arithmetic_ops =
        [OP_ADD, OP_MUL, OP_FMA]
            .into_iter()
            .try_fold(0usize, |count, opcode| {
                count
                    .checked_add(compiled.compiled.stats.op_counts[opcode])
                    .ok_or(BackwardSearchError::CostOverflow)
            })?;
    let score = BackwardScore {
        infeasible: false,
        whole_pass_dram_bytes: whole_pass_cost.dram_bytes()?,
        primitive_source_ops: whole_pass_cost.ops.primitive_equivalents()?,
        instructions: compiled.compiled.program.instrs.len(),
        encoded_lanes: compiled.encoded.len(),
        arithmetic_ops,
        ordinal,
    };
    let certificate = PagingCertificate {
        actions_consumed: paging.actions.len(),
        diverged,
        refused_retains,
        predicted_source_reads: predicted.reads,
        realized_source_reads: realized_reads
            .len()
            .try_into()
            .map_err(|_| BackwardSearchError::CostOverflow)?,
        predicted_read_cost: predicted.cost,
        realized_read_cost,
        fixed_write_cost,
        peak_live_lanes,
        placement_relocations: compiled.binding_stats.relocation_moves,
    };
    Ok(CertifiedBackwardCandidate {
        paging: paging.clone(),
        occurrence_plan,
        compiled,
        certificate,
        score,
    })
}

struct PredictedPaging {
    reads: u64,
    accesses: Vec<(ExprId, u8)>,
    cost: SourceCost,
}

fn predict_paging(
    problem: &BackwardSearchProblem,
    paging: &ExactPagingPlan,
) -> Result<PredictedPaging, BackwardSearchError> {
    if paging.live_lanes_after.len() != problem.demands.len() {
        return Err(BackwardSearchError::PagingCertificateMismatch {
            observable: "pager occupancy length",
        });
    }
    let mut residents = BTreeMap::<ExprId, u8>::new();
    let mut reads = 0u64;
    let mut accesses = Vec::new();
    let mut cost = SourceCost::default();
    let mut admissions = 0u32;
    let mut evictions = 0u32;
    for (position, (demand, action)) in problem.demands.iter().zip(&paging.actions).enumerate() {
        if residents.remove(&demand.expr).is_some() {
            evictions = evictions
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
        } else {
            reads = reads
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
            accesses.push((demand.expr, demand.width_lanes));
            cost = cost.checked_add(demand.miss_cost)?;
        }
        if *action == PagingAction::Retain {
            if !demand.has_next {
                return Err(BackwardSearchError::PagingCertificateMismatch {
                    observable: "terminal retain",
                });
            }
            residents.insert(demand.expr, demand.width_lanes);
            admissions = admissions
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
        }
        let live = residents.values().try_fold(0u8, |total, width| {
            total
                .checked_add(*width)
                .ok_or(BackwardSearchError::CostOverflow)
        })?;
        if paging.live_lanes_after[position] != live {
            return Err(BackwardSearchError::PagingCertificateMismatch {
                observable: "pager occupancy",
            });
        }
    }
    let read_bytes = cost.dram_bytes()?;
    let primitive_ops = cost.ops.primitive_equivalents()?;
    if reads != u64::from(paging.predicted_misses)
        || read_bytes != paging.objective.dram_bytes
        || primitive_ops != paging.objective.primitive_source_ops
        || admissions != paging.objective.admissions
        || evictions != paging.objective.evictions
    {
        return Err(BackwardSearchError::PagingCertificateMismatch {
            observable: "pager objective",
        });
    }
    Ok(PredictedPaging {
        reads,
        accesses,
        cost,
    })
}

fn access_histogram(
    accesses: impl Iterator<Item = (ExprId, u32)>,
) -> Result<BTreeMap<(ExprId, u32), usize>, BackwardSearchError> {
    let mut histogram = BTreeMap::<(ExprId, u32), usize>::new();
    for access in accesses {
        let count = histogram.entry(access).or_default();
        *count = count
            .checked_add(1)
            .ok_or(BackwardSearchError::CostOverflow)?;
    }
    Ok(histogram)
}

fn controlled_sources(
    demands: &[BackwardDemand],
) -> Result<BTreeMap<ExprId, (u8, Option<u16>)>, BackwardSearchError> {
    let mut sources = BTreeMap::new();
    for demand in demands {
        match sources.insert(demand.expr, (demand.width_lanes, demand.source_desc)) {
            Some(previous) if previous != (demand.width_lanes, demand.source_desc) => {
                return Err(BackwardSearchError::PagingCertificateMismatch {
                    observable: "source cost binding",
                });
            }
            _ => {}
        }
    }
    Ok(sources)
}

fn reprice_source_read(
    problem: &BackwardSearchProblem,
    source_desc: Option<u16>,
    width_lanes: u8,
) -> Result<SourceCost, BackwardSearchError> {
    let Some(desc) = source_desc else {
        return Ok(SourceCost {
            plain_read_bytes: u128::from(width_lanes)
                .checked_mul(4)
                .ok_or(BackwardSearchError::CostOverflow)?,
            ..SourceCost::default()
        });
    };
    let uses = problem
        .source_round_uses
        .iter()
        .copied()
        .filter(|source_use| source_use.desc == desc)
        .collect::<Vec<_>>();
    if uses.is_empty() {
        return Err(BackwardSearchError::PagingCertificateMismatch {
            observable: "source round pricing input",
        });
    }
    let mut cost = miss_cost(&uses, &problem.round_profiles, &problem.materialization)?;
    cost.materialization_write_bytes = cost
        .materialization_write_bytes
        .checked_sub(
            problem
                .materialization
                .fixed_writes
                .materialization_write_bytes,
        )
        .ok_or(BackwardSearchError::CostOverflow)?;
    Ok(cost)
}

fn realized_occupancy_profile(
    problem: &BackwardSearchProblem,
    compiled: &CompiledBackwardEvaluation,
) -> Result<(Vec<usize>, usize), BackwardSearchError> {
    let mut eligible = BTreeMap::<BwdFingerprintOrderKey, usize>::new();
    for demand in &problem.demands {
        let count = eligible.entry(demand.fp.into()).or_default();
        *count = count
            .checked_add(1)
            .ok_or(BackwardSearchError::CostOverflow)?;
    }
    let mut resident = BTreeMap::<ExprId, usize>::new();
    let mut live = 0usize;
    let mut peak = 0usize;
    let mut profile = Vec::with_capacity(problem.demands.len());
    let mut seen_eligible_serve = false;
    for event in &compiled.trace.events {
        match event {
            BwdEvent::Serve { fp, .. } => {
                let key = (*fp).into();
                let is_eligible = eligible.get_mut(&key).is_some_and(|remaining| {
                    if *remaining == 0 {
                        false
                    } else {
                        *remaining -= 1;
                        true
                    }
                });
                if is_eligible {
                    if seen_eligible_serve {
                        profile.push(live);
                    }
                    seen_eligible_serve = true;
                }
            }
            BwdEvent::Admit { value, width } => {
                if resident.insert(*value, usize::from(*width)).is_some() {
                    return Err(BackwardSearchError::PagingCertificateMismatch {
                        observable: "duplicate admission",
                    });
                }
                live = live
                    .checked_add(usize::from(*width))
                    .ok_or(BackwardSearchError::CostOverflow)?;
                peak = peak.max(live);
            }
            BwdEvent::Evict { value, .. } => {
                let width = resident.remove(value).ok_or(
                    BackwardSearchError::PagingCertificateMismatch {
                        observable: "eviction without admission",
                    },
                )?;
                live = live
                    .checked_sub(width)
                    .ok_or(BackwardSearchError::CostOverflow)?;
            }
            BwdEvent::TrafficRead { .. } | BwdEvent::Refuse { .. } | BwdEvent::Diverge { .. } => {}
        }
    }
    if seen_eligible_serve {
        profile.push(live);
    }
    if eligible.values().any(|remaining| *remaining != 0) {
        return Err(BackwardSearchError::PagingCertificateMismatch {
            observable: "eligible serve count",
        });
    }
    Ok((profile, peak))
}

fn map_replay_error(error: BackwardEvaluationError) -> BackwardSearchError {
    match error {
        BackwardEvaluationError::ReplayInfeasible => {
            BackwardSearchError::PlacementIntegrationFailure
        }
        BackwardEvaluationError::ReplayDiverged { at_entry }
        | BackwardEvaluationError::ReplayNotFullyConsumed { at_entry } => {
            BackwardSearchError::PagingReplayDiverged { at_entry }
        }
        error => BackwardSearchError::BackwardEvaluation(error),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup,
        RootId, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
    };

    use crate::bwd::distill::{DistilledLayer, distill};
    use crate::bwd::plan::PlanAction;
    use crate::eval_plan::backward_search::pager::{
        ExactPagingPlan, PagerOutcome, PagingAction, solve_exact_paging,
    };
    use crate::eval_plan::backward_search::problem::{
        BackwardSearchProblem, build_backward_search_problem,
    };
    use crate::eval_plan::backward_search::{BackwardSearchError, MAX_PAGER_STATES};

    use super::{compile_and_certify_paging, occurrence_plan_from_paging};

    struct SyntheticFixture {
        distilled: DistilledLayer,
        problem: BackwardSearchProblem,
        exact: ExactPagingPlan,
    }

    #[test]
    fn paging_actions_fill_only_eligible_leaf_occurrences() {
        let fixture = synthetic_shared_read_fixture();
        let plan = occurrence_plan_from_paging(&fixture.problem, &fixture.exact).unwrap();
        assert_eq!(plan.entries.len(), fixture.problem.all_domain_serves.len());
        assert_eq!(
            plan.entries
                .iter()
                .filter(|entry| entry.action == PlanAction::Retain)
                .count(),
            fixture
                .exact
                .actions
                .iter()
                .filter(|action| **action == PagingAction::Retain)
                .count()
        );
    }

    #[test]
    fn exact_paging_replay_certifies_accesses_costs_and_occupancy() {
        let fixture = synthetic_shared_read_fixture();
        let candidate =
            compile_and_certify_paging(&fixture.distilled, &fixture.problem, &fixture.exact, 0)
                .unwrap();
        assert_eq!(candidate.certificate.diverged, None);
        assert_eq!(candidate.certificate.refused_retains, 0);
        assert_eq!(
            candidate.certificate.predicted_source_reads,
            candidate.certificate.realized_source_reads
        );
        assert_eq!(
            candidate.certificate.predicted_read_cost,
            candidate.certificate.realized_read_cost
        );
        assert!(candidate.certificate.peak_live_lanes <= fixture.problem.budget_lanes);
        assert_eq!(candidate.score.ordinal, 0);
        let controlled_bytes = candidate
            .certificate
            .predicted_read_cost
            .checked_add(candidate.certificate.fixed_write_cost)
            .unwrap()
            .dram_bytes()
            .unwrap();
        assert!(
            candidate.score.whole_pass_dram_bytes > controlled_bytes,
            "whole-pass score must include non-paged physical reads"
        );
    }

    #[test]
    fn duplicate_fingerprints_consume_actions_in_demand_order() {
        let fixture = synthetic_shared_read_fixture();
        let mut problem = fixture.problem;
        let mut exact = fixture.exact;
        assert_eq!(problem.demands.len(), 2);
        let fp = problem.demands[0].fp;
        problem.demands[1].fp = fp;
        problem.all_domain_serves = vec![fp, fp];
        exact.actions = vec![PagingAction::Retain, PagingAction::Bypass];

        let plan = occurrence_plan_from_paging(&problem, &exact).unwrap();
        assert_eq!(
            plan.entries
                .iter()
                .map(|entry| entry.action)
                .collect::<Vec<_>>(),
            vec![PlanAction::Retain, PlanAction::Bypass]
        );
    }

    #[test]
    fn duplicate_fingerprint_queue_fails_on_underflow_and_leftover() {
        let fixture = synthetic_shared_read_fixture();
        let mut problem = fixture.problem;
        let exact = fixture.exact;
        assert_eq!(problem.demands.len(), 2);
        let fp = problem.demands[0].fp;
        problem.demands[1].fp = fp;
        problem.all_domain_serves = vec![fp, fp, fp];
        assert!(matches!(
            occurrence_plan_from_paging(&problem, &exact),
            Err(BackwardSearchError::PagingActionUnderflow { serve: 2 })
        ));

        problem.all_domain_serves = vec![fp];
        assert!(matches!(
            occurrence_plan_from_paging(&problem, &exact),
            Err(BackwardSearchError::PagingActionLeftover { remaining: 1 })
        ));
    }

    #[test]
    fn certificate_mismatch_is_an_error_not_candidate_infeasibility() {
        let fixture = synthetic_shared_read_fixture();
        let mut exact = fixture.exact;
        exact.predicted_misses += 1;
        assert!(matches!(
            compile_and_certify_paging(&fixture.distilled, &fixture.problem, &exact, 0),
            Err(BackwardSearchError::PagingCertificateMismatch { .. })
        ));
    }

    fn synthetic_shared_read_fixture() -> SyntheticFixture {
        let layer = synthetic_shared_read_layer();
        let distilled = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
        let (_, problem) = build_backward_search_problem(&layer, &distilled, 8, 4).unwrap();
        let problem = problem.expect("synthetic shared-read problem");
        let exact = match solve_exact_paging(&problem.demands, MAX_PAGER_STATES).unwrap() {
            PagerOutcome::Solved(exact) => exact,
            outcome => panic!("expected solved paging problem, got {outcome:?}"),
        };
        SyntheticFixture {
            distilled,
            problem,
            exact,
        }
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
}
