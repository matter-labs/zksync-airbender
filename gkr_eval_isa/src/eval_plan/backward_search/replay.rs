use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::time::{Duration, Instant};

use cs::gkr_compiler::dag_ir::{ExprId, FieldKind};

use crate::bwd::distill::DistilledLayer;
use crate::bwd::plan::{BwdOccurrencePlan, PlanAction, PlanEntry, plan_entries_fnv};
use crate::bwd::trace::{
    BwdEvent, BwdFingerprint, BwdServeKind, BwdServedFrom, positioned_physical_traffic_events,
};
use crate::eval_plan::backward::{
    BackwardEvaluationError, CompiledBackwardEvaluation, compile_backward_fragments_replayed,
};
use crate::eval_plan::{ValueFingerprint, structural_fingerprints};
use crate::fwd::stats::{OP_ADD, OP_FMA, OP_MUL};

use super::pager::{ExactPagingPlan, PagingAction, PhysicalPagingState};
use super::problem::{BackwardDemand, BackwardSearchProblem};
use super::{BackwardScore, BackwardSearchError, SourceCost, miss_cost, native_read_cost};

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

pub struct ScoredAcceptedBackwardCandidate {
    pub occurrence_plan: BwdOccurrencePlan,
    pub compiled: CompiledBackwardEvaluation,
    pub score: BackwardScore,
    pub compile_time: Duration,
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

    let mut demands = ordered_demand_queues(problem);
    let eligible = demands.keys().copied().collect::<BTreeSet<_>>();
    let mut entries = Vec::with_capacity(problem.all_domain_serves.len());
    for (serve, &fp) in problem.all_domain_serves.iter().enumerate() {
        let key = fp.into();
        let action = if eligible.contains(&key) {
            let demand = demands
                .get_mut(&key)
                .and_then(VecDeque::pop_front)
                .ok_or(BackwardSearchError::PagingActionUnderflow { serve })?;
            paging.actions[demand]
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
    let remaining = demands.values().try_fold(0usize, |count, queue| {
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

    let (diverged, refused_retains) = validate_replay_trace(&compiled)?;

    let physical_values = structural_fingerprints(&d.layer).map_err(|error| {
        BackwardSearchError::BackwardEvaluation(BackwardEvaluationError::Plan(error.into()))
    })?;
    let (realized_profile, peak_live_lanes) =
        realized_occupancy_profile(problem, &compiled, &physical_values)?;
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
        &compiled.compiled.source_windows,
    )
    .ok_or(BackwardSearchError::PagingCertificateMismatch {
        observable: "physical traffic source mapping",
    })?;
    let sources = controlled_sources(&problem.demands)?;
    let realized_misses = certify_demand_misses(problem, &predicted, &compiled)?;
    let predicted_width_lanes = demand_width_lanes(problem, &predicted.misses)?;
    let mut realized_reads = physical
        .iter()
        .filter_map(|positioned| match positioned.event {
            BwdEvent::TrafficRead { value, cells } => physical_values
                .get(value.0 as usize)
                .copied()
                .filter(|physical| sources.contains_key(physical))
                .map(|physical| (physical, cells)),
            _ => None,
        })
        .collect::<Vec<_>>();
    realized_reads.sort_unstable();
    let realized_width_lanes = realized_reads.iter().try_fold(0u64, |total, (_, width)| {
        total
            .checked_add(u64::from(*width))
            .ok_or(BackwardSearchError::CostOverflow)
    })?;
    let mut anchored_reads = realized_misses
        .iter()
        .map(|&index| {
            let demand = &problem.demands[index];
            (demand.physical, u32::from(demand.width_lanes))
        })
        .collect::<Vec<_>>();
    anchored_reads.sort_unstable();
    if realized_reads != anchored_reads {
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
    let score = score_compiled_backward(d, problem, &compiled, ordinal)?;
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

/// Replay and score an already accepted production occurrence plan exactly.
///
/// Unlike [`compile_and_certify_paging`], this path does not project the plan
/// into the real-leaf pager domain: compound retains and their suppressed serve
/// stream remain authoritative. The replay backend validates epoch/FNV/count,
/// and this helper additionally requires a clean replay and concrete placement.
pub fn compile_and_score_occurrence_plan(
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    occurrence_plan: &BwdOccurrencePlan,
    order: &[usize],
    ordinal: usize,
) -> Result<ScoredAcceptedBackwardCandidate, BackwardSearchError> {
    let started = Instant::now();
    let compiled =
        compile_backward_fragments_replayed(d, occurrence_plan, Some(order), problem.budget_cells)
            .map_err(map_replay_error)?;
    let compile_time = started.elapsed();
    validate_replay_trace(&compiled)?;
    let score = score_compiled_backward(d, problem, &compiled, ordinal)?;
    Ok(ScoredAcceptedBackwardCandidate {
        occurrence_plan: occurrence_plan.clone(),
        compiled,
        score,
        compile_time,
    })
}

fn validate_replay_trace(
    compiled: &CompiledBackwardEvaluation,
) -> Result<(Option<usize>, usize), BackwardSearchError> {
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
    Ok((diverged, refused_retains))
}

fn score_compiled_backward(
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    compiled: &CompiledBackwardEvaluation,
    ordinal: usize,
) -> Result<BackwardScore, BackwardSearchError> {
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
    let physical = positioned_physical_traffic_events(
        &d.layer,
        &compiled.compiled.program,
        &compiled.compiled.specials,
        &d.leaf_descs,
        &compiled.compiled.backings,
        &compiled.compiled.source_windows,
    )
    .ok_or(BackwardSearchError::PagingCertificateMismatch {
        observable: "physical traffic source mapping",
    })?;
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
    Ok(BackwardScore {
        infeasible: false,
        whole_pass_dram_bytes: whole_pass_cost.dram_bytes()?,
        primitive_source_ops: whole_pass_cost.ops.primitive_equivalents()?,
        instructions: compiled.compiled.program.instrs.len(),
        encoded_lanes: compiled.encoded.len(),
        arithmetic_ops,
        ordinal,
    })
}

struct PredictedPaging {
    reads: u64,
    misses: Vec<usize>,
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
    let mut residents = PhysicalPagingState::default();
    let mut reads = 0u64;
    let mut misses = Vec::new();
    let mut cost = SourceCost::default();
    let mut admissions = 0u32;
    let mut evictions = 0u32;
    for (position, (demand, action)) in problem.demands.iter().zip(&paging.actions).enumerate() {
        let served = residents.serve(demand)?;
        if served.closed_owner {
            evictions = evictions
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
        }
        if !served.hit {
            reads = reads
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
            misses.push(position);
            cost = cost.checked_add(demand.miss_cost)?;
        }
        if *action == PagingAction::Retain {
            if !demand.has_next {
                return Err(BackwardSearchError::PagingCertificateMismatch {
                    observable: "terminal retain",
                });
            }
            residents.retain(demand)?;
            admissions = admissions
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
        }
        let live = residents.live_lanes()?;
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
        misses,
        cost,
    })
}

fn controlled_sources(
    demands: &[BackwardDemand],
) -> Result<BTreeMap<ValueFingerprint, (u8, Option<u16>)>, BackwardSearchError> {
    let mut sources = BTreeMap::new();
    for demand in demands {
        match sources.insert(demand.physical, (demand.width_lanes, demand.source_desc)) {
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

pub(super) fn reprice_source_read(
    problem: &BackwardSearchProblem,
    source_desc: Option<u16>,
    width_lanes: u8,
) -> Result<SourceCost, BackwardSearchError> {
    let Some(desc) = source_desc else {
        let field = match width_lanes {
            1 => FieldKind::Base,
            4 => FieldKind::Ext,
            _ => return Err(BackwardSearchError::CostOverflow),
        };
        return native_read_cost(field, &problem.round_profiles);
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

fn ordered_demand_queues(
    problem: &BackwardSearchProblem,
) -> BTreeMap<BwdFingerprintOrderKey, VecDeque<usize>> {
    let mut eligible = BTreeMap::<BwdFingerprintOrderKey, Vec<(usize, usize, usize)>>::new();
    for (index, demand) in problem.demands.iter().enumerate() {
        eligible.entry(demand.fp.into()).or_default().push((
            demand.instruction,
            demand.physical_ordinal,
            index,
        ));
    }
    eligible
        .into_iter()
        .map(|(fp, mut identities)| {
            identities.sort();
            (
                fp,
                identities.into_iter().map(|(_, _, index)| index).collect(),
            )
        })
        .collect()
}

fn realized_demand_misses(
    problem: &BackwardSearchProblem,
    compiled: &CompiledBackwardEvaluation,
) -> Result<Vec<usize>, BackwardSearchError> {
    let mut eligible = ordered_demand_queues(problem);
    let mut misses = Vec::new();
    for event in &compiled.trace.events {
        let BwdEvent::Serve { fp, from } = event else {
            continue;
        };
        let key = (*fp).into();
        let Some(queue) = eligible.get_mut(&key) else {
            continue;
        };
        let index = queue
            .pop_front()
            .ok_or(BackwardSearchError::PagingCertificateMismatch {
                observable: "extra eligible serve",
            })?;
        if *from == BwdServedFrom::Recomputed {
            misses.push(index);
        }
    }
    if eligible.values().any(|remaining| !remaining.is_empty()) {
        return Err(BackwardSearchError::PagingCertificateMismatch {
            observable: "eligible serve count",
        });
    }
    misses.sort_unstable();
    Ok(misses)
}

fn demand_width_lanes(
    problem: &BackwardSearchProblem,
    demands: &[usize],
) -> Result<u64, BackwardSearchError> {
    demands.iter().try_fold(0u64, |total, &index| {
        total
            .checked_add(u64::from(problem.demands[index].width_lanes))
            .ok_or(BackwardSearchError::CostOverflow)
    })
}

fn certify_demand_misses(
    problem: &BackwardSearchProblem,
    predicted: &PredictedPaging,
    compiled: &CompiledBackwardEvaluation,
) -> Result<Vec<usize>, BackwardSearchError> {
    let realized = realized_demand_misses(problem, compiled)?;
    if realized != predicted.misses {
        return Err(BackwardSearchError::PagingSourceAccessMismatch {
            predicted_reads: predicted.reads,
            realized_reads: realized
                .len()
                .try_into()
                .map_err(|_| BackwardSearchError::CostOverflow)?,
            predicted_width_lanes: demand_width_lanes(problem, &predicted.misses)?,
            realized_width_lanes: demand_width_lanes(problem, &realized)?,
        });
    }
    Ok(realized)
}

fn realized_occupancy_profile(
    problem: &BackwardSearchProblem,
    compiled: &CompiledBackwardEvaluation,
    physical_values: &[ValueFingerprint],
) -> Result<(Vec<usize>, usize), BackwardSearchError> {
    let mut eligible = ordered_demand_queues(problem);
    let mut resident = BTreeMap::<ValueFingerprint, (usize, usize)>::new();
    let mut intervals = Vec::new();
    let mut active_demand = None;
    for event in &compiled.trace.events {
        match event {
            BwdEvent::Serve { fp, .. } => {
                let key = (*fp).into();
                if let Some(index) = eligible.get_mut(&key).and_then(VecDeque::pop_front) {
                    active_demand = Some(index);
                }
            }
            BwdEvent::Admit { value, width } => {
                let demand_position =
                    active_demand.ok_or(BackwardSearchError::PagingCertificateMismatch {
                        observable: "admission without eligible demand",
                    })?;
                let demand = problem.demands.get(demand_position).ok_or(
                    BackwardSearchError::PagingCertificateMismatch {
                        observable: "admission without eligible demand",
                    },
                )?;
                let physical = physical_values.get(value.0 as usize).copied().ok_or(
                    BackwardSearchError::PagingCertificateMismatch {
                        observable: "admission physical identity",
                    },
                )?;
                if demand.physical != physical || demand.width_lanes != *width {
                    return Err(BackwardSearchError::PagingCertificateMismatch {
                        observable: "admission demand identity",
                    });
                }
                if resident
                    .insert(physical, (usize::from(*width), demand_position))
                    .is_some()
                {
                    return Err(BackwardSearchError::PagingCertificateMismatch {
                        observable: "duplicate admission",
                    });
                }
            }
            BwdEvent::Evict { value, .. } => {
                let demand_position =
                    active_demand.ok_or(BackwardSearchError::PagingCertificateMismatch {
                        observable: "eviction without eligible demand",
                    })?;
                let physical = physical_values.get(value.0 as usize).copied().ok_or(
                    BackwardSearchError::PagingCertificateMismatch {
                        observable: "eviction physical identity",
                    },
                )?;
                let (width, admitted_at) = resident.remove(&physical).ok_or(
                    BackwardSearchError::PagingCertificateMismatch {
                        observable: "eviction without admission",
                    },
                )?;
                if demand_position < admitted_at {
                    return Err(BackwardSearchError::PagingCertificateMismatch {
                        observable: "reversed physical retention interval",
                    });
                }
                intervals.push((admitted_at, demand_position, width));
            }
            BwdEvent::TrafficRead { .. } | BwdEvent::Refuse { .. } | BwdEvent::Diverge { .. } => {}
        }
    }
    if eligible.values().any(|remaining| !remaining.is_empty()) {
        return Err(BackwardSearchError::PagingCertificateMismatch {
            observable: "eligible serve count",
        });
    }
    intervals.extend(
        resident
            .into_values()
            .map(|(width, admitted_at)| (admitted_at, problem.demands.len(), width)),
    );
    let mut deltas = vec![0isize; problem.demands.len() + 1];
    for (start, end, width) in intervals {
        let width = isize::try_from(width).map_err(|_| BackwardSearchError::CostOverflow)?;
        deltas[start] = deltas[start]
            .checked_add(width)
            .ok_or(BackwardSearchError::CostOverflow)?;
        deltas[end] = deltas[end]
            .checked_sub(width)
            .ok_or(BackwardSearchError::CostOverflow)?;
    }
    let mut live = 0isize;
    let mut profile = Vec::with_capacity(problem.demands.len());
    for delta in deltas.into_iter().take(problem.demands.len()) {
        live = live
            .checked_add(delta)
            .ok_or(BackwardSearchError::CostOverflow)?;
        profile.push(usize::try_from(live).map_err(|_| BackwardSearchError::CostOverflow)?);
    }
    let peak = profile.iter().copied().max().unwrap_or(0);
    Ok((profile, peak))
}

fn map_replay_error(error: BackwardEvaluationError) -> BackwardSearchError {
    match error {
        BackwardEvaluationError::ReplayPlacementFailed { .. } => {
            BackwardSearchError::PlacementIntegrationFailure
        }
        BackwardEvaluationError::ReplayDiverged { at_entry } => {
            BackwardSearchError::PagingReplayDiverged { at_entry }
        }
        BackwardEvaluationError::ReplayNotFullyConsumed { at_entry } => {
            BackwardSearchError::PagingReplayIncomplete { at_entry }
        }
        BackwardEvaluationError::ReplayRefused { .. } => {
            BackwardSearchError::PagingReplayRefused { count: 1 }
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
    use crate::bwd::trace::{BwdEvent, positioned_physical_traffic_events};
    use crate::eval_plan::backward::BackwardEvaluationError;
    use crate::eval_plan::backward_search::pager::{
        ExactPagingPlan, PagerOutcome, PagingAction, solve_exact_paging,
    };
    use crate::eval_plan::backward_search::problem::{
        BackwardSearchProblem, build_backward_search_problem,
    };
    use crate::eval_plan::backward_search::{BackwardSearchError, MAX_PAGER_STATES};
    use crate::eval_plan::structural_fingerprints;

    use super::{
        certify_demand_misses, compile_and_certify_paging, controlled_sources, map_replay_error,
        occurrence_plan_from_paging, predict_paging, realized_occupancy_profile,
    };

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
    fn controlled_sources_collapse_matching_physical_aliases() {
        let fixture = synthetic_shared_read_fixture();
        let mut demands = fixture.problem.demands;
        assert_eq!(demands.len(), 2);
        demands[1].expr = ExprId(demands[0].expr.0 + 100);
        demands[1].physical = demands[0].physical;

        let sources = controlled_sources(&demands).unwrap();

        assert_eq!(sources.len(), 1);
    }

    #[test]
    fn controlled_sources_reject_alias_binding_disagreement() {
        let fixture = synthetic_shared_read_fixture();
        let mut demands = fixture.problem.demands;
        demands[1].expr = ExprId(demands[0].expr.0 + 100);
        demands[1].physical = demands[0].physical;
        demands[1].source_desc = demands[0]
            .source_desc
            .map_or(Some(0), |desc| Some(desc + 1));

        assert!(matches!(
            controlled_sources(&demands),
            Err(BackwardSearchError::PagingCertificateMismatch {
                observable: "source cost binding"
            })
        ));
    }

    #[test]
    fn replayed_positions_may_compress_after_an_earlier_hit() {
        let layer = synthetic_two_shared_sources_layer();
        let distilled = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
        let (_, problem) = build_backward_search_problem(&layer, &distilled, 8, 4).unwrap();
        let problem = problem.expect("two shared-source problem");
        let demand_values = problem
            .demands
            .iter()
            .map(|demand| demand.expr)
            .collect::<Vec<_>>();
        assert_eq!(demand_values.len(), 4);
        assert_eq!(demand_values[0], demand_values[1]);
        assert_eq!(demand_values[2], demand_values[3]);
        assert_ne!(demand_values[0], demand_values[2]);
        let exact = match solve_exact_paging(&problem.demands, MAX_PAGER_STATES).unwrap() {
            PagerOutcome::Solved(exact) => exact,
            outcome => panic!("expected solved paging problem, got {outcome:?}"),
        };
        assert_eq!(
            exact.actions,
            vec![
                PagingAction::Retain,
                PagingAction::Bypass,
                PagingAction::Retain,
                PagingAction::Bypass,
            ]
        );

        let candidate = compile_and_certify_paging(&distilled, &problem, &exact, 0).unwrap();
        let replayed_b = positioned_physical_traffic_events(
            &distilled.layer,
            &candidate.compiled.compiled.program,
            &candidate.compiled.compiled.specials,
            &distilled.leaf_descs,
            &candidate.compiled.compiled.backings,
            &candidate.compiled.compiled.source_windows,
        )
        .unwrap()
        .into_iter()
        .find(|positioned| {
            matches!(
                positioned.event,
                BwdEvent::TrafficRead { value, .. } if value == problem.demands[2].expr
            )
        })
        .unwrap();
        assert_ne!(
            (
                problem.demands[2].instruction,
                problem.demands[2].physical_ordinal,
            ),
            (replayed_b.instruction, replayed_b.physical_ordinal),
            "the later B miss must exercise compressed replay coordinates"
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

    #[test]
    fn certificate_accepts_reordered_equivalent_all_miss_identities() {
        let fixture = synthetic_shared_read_fixture();
        let mut problem = fixture.problem;
        let mut paging = fixture.exact;
        assert_eq!(problem.demands.len(), 2);
        assert_eq!(problem.demands[0].expr, problem.demands[1].expr);
        paging.actions.fill(PagingAction::Bypass);
        paging.live_lanes_after.fill(0);
        paging.predicted_misses = 2;
        paging.refused_retains = 0;
        paging.objective.dram_bytes = problem
            .demands
            .iter()
            .map(|demand| demand.miss_cost.dram_bytes().unwrap())
            .sum();
        paging.objective.primitive_source_ops = problem
            .demands
            .iter()
            .map(|demand| demand.miss_cost.ops.primitive_equivalents().unwrap())
            .sum();
        paging.objective.admissions = 0;
        paging.objective.evictions = 0;
        let mut candidate =
            compile_and_certify_paging(&fixture.distilled, &problem, &paging, 0).unwrap();
        let fp = problem.demands[0].fp;
        problem.demands[1].fp = fp;
        for event in &mut candidate.compiled.trace.events {
            if let BwdEvent::Serve { fp: served, .. } = event
                && served.value == problem.demands[0].expr
            {
                *served = fp;
            }
        }
        let first = (
            problem.demands[0].instruction,
            problem.demands[0].physical_ordinal,
        );
        let second = (
            problem.demands[1].instruction,
            problem.demands[1].physical_ordinal,
        );
        (
            problem.demands[0].instruction,
            problem.demands[0].physical_ordinal,
        ) = second;
        (
            problem.demands[1].instruction,
            problem.demands[1].physical_ordinal,
        ) = first;

        let predicted = predict_paging(&problem, &paging).unwrap();
        assert_eq!(
            certify_demand_misses(&problem, &predicted, &candidate.compiled).unwrap(),
            predicted.misses
        );
    }

    #[test]
    fn occupancy_rejects_reversed_authoritative_demand_interval() {
        let fixture = synthetic_shared_read_fixture();
        let mut candidate =
            compile_and_certify_paging(&fixture.distilled, &fixture.problem, &fixture.exact, 0)
                .unwrap();
        let mut problem = fixture.problem;
        let fp = problem.demands[0].fp;
        problem.demands[1].fp = fp;
        for event in &mut candidate.compiled.trace.events {
            if let BwdEvent::Serve { fp: served, .. } = event
                && served.value == problem.demands[0].expr
            {
                *served = fp;
            }
        }
        let first = (
            problem.demands[0].instruction,
            problem.demands[0].physical_ordinal,
        );
        let second = (
            problem.demands[1].instruction,
            problem.demands[1].physical_ordinal,
        );
        (
            problem.demands[0].instruction,
            problem.demands[0].physical_ordinal,
        ) = second;
        (
            problem.demands[1].instruction,
            problem.demands[1].physical_ordinal,
        ) = first;

        let physical_values = structural_fingerprints(&fixture.distilled.layer).unwrap();
        assert!(matches!(
            realized_occupancy_profile(&problem, &candidate.compiled, &physical_values),
            Err(BackwardSearchError::PagingCertificateMismatch {
                observable: "reversed physical retention interval"
            })
        ));
    }

    #[test]
    fn replay_error_taxonomy_remains_distinct() {
        assert!(matches!(
            map_replay_error(BackwardEvaluationError::ReplayRefused {
                value: ExprId(7),
                need: 4,
            }),
            BackwardSearchError::PagingReplayRefused { count: 1 }
        ));
        assert!(matches!(
            map_replay_error(BackwardEvaluationError::ReplayDiverged { at_entry: 2 }),
            BackwardSearchError::PagingReplayDiverged { at_entry: 2 }
        ));
        assert!(matches!(
            map_replay_error(BackwardEvaluationError::ReplayNotFullyConsumed { at_entry: 3 }),
            BackwardSearchError::PagingReplayIncomplete { at_entry: 3 }
        ));
        assert!(matches!(
            map_replay_error(BackwardEvaluationError::ReplayPlacementFailed {
                budget_lanes: 4,
                peak_live_lanes: 8,
            }),
            BackwardSearchError::PlacementIntegrationFailure
        ));
    }

    #[test]
    fn r0_global_reads_include_exact_t2_role_combine_ops() {
        let layer = synthetic_shared_read_layer();
        let distilled = distill(&layer, BwdRegime::R0, &HashMap::new(), None);
        let (_, problem) = build_backward_search_problem(&layer, &distilled, 8, 4).unwrap();
        let problem = problem.unwrap();
        assert!(problem.demands.iter().all(|demand| {
            demand.source_desc.is_none()
                && demand.miss_cost.ops.bf_add == 30
                && demand.miss_cost.ops.ext_add == 0
        }));
        let exact = match solve_exact_paging(&problem.demands, MAX_PAGER_STATES).unwrap() {
            PagerOutcome::Solved(exact) => exact,
            outcome => panic!("expected solved paging problem, got {outcome:?}"),
        };
        let candidate = compile_and_certify_paging(&distilled, &problem, &exact, 0).unwrap();
        assert_eq!(candidate.score.primitive_source_ops, 90);
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

    fn synthetic_two_shared_sources_layer() -> DagLayer {
        let sources = (0..6).map(read_source).collect::<Vec<_>>();
        let mut exprs = (0..6)
            .map(|source| Expr::Source(SourceId(source)))
            .collect::<Vec<_>>();
        for children in [[0, 2], [0, 3], [1, 4], [1, 5]] {
            exprs.push(Expr::Mul(children.map(ExprId).into_iter().collect()));
        }
        DagLayer {
            sources,
            exprs,
            batching: BatchingOrder {
                roots: (0..4).map(RootId).collect(),
            },
            roots: (0..4)
                .map(|index| claim_root(ExprId(6 + index), index as usize))
                .collect(),
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
