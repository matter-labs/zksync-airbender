use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::ExprId;

use super::BackwardSearchError;
use super::problem::BackwardDemand;
use super::uniform_pager::solve_uniform_exact_paging_observed;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PagingAction {
    Bypass,
    Retain,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct PagingObjective {
    pub dram_bytes: u128,
    pub primitive_source_ops: u128,
    pub admissions: u32,
    pub evictions: u32,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PagingTelemetry {
    pub peak_live_states: usize,
    pub generated_states: u64,
    pub merged_states: u64,
    pub peak_live_lanes: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactPagingPlan {
    pub actions: Vec<PagingAction>,
    pub live_lanes_after: Vec<u8>,
    pub objective: PagingObjective,
    pub predicted_misses: u32,
    pub refused_retains: u32,
    pub telemetry: PagingTelemetry,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PagerOutcome {
    Solved(ExactPagingPlan),
    SolverCapped {
        cap: usize,
        demand_position: usize,
        peak_states: usize,
        generated_states: u64,
        merged_states: u64,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProductionPagingSolver {
    RetainAll,
    UniformIntervals,
    ResidentSets,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductionPagingResult {
    pub solver: ProductionPagingSolver,
    pub plan: ExactPagingPlan,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ProductionPagingProgress {
    pub solver: ProductionPagingSolver,
    pub current_states: usize,
    pub peak_states: usize,
}

#[derive(Clone, Debug)]
struct Node {
    objective: PagingObjective,
    predicted_misses: u32,
    refused_retains: u32,
    live_lanes: u8,
    parent_lex_rank: u64,
    action: PagingAction,
    lex_rank: u64,
    predecessor: usize,
    arena_index: usize,
}

#[derive(Clone, Copy, Debug)]
struct ArenaEntry {
    predecessor: Option<usize>,
    action: Option<PagingAction>,
    live_lanes_after: u8,
}

fn node_key(node: &Node) -> (u128, u128, u32, u32, u64, PagingAction) {
    (
        node.objective.dram_bytes,
        node.objective.primitive_source_ops,
        node.objective.admissions,
        node.objective.evictions,
        node.parent_lex_rank,
        node.action,
    )
}

fn canonical_plan_key(plan: &ExactPagingPlan) -> (PagingObjective, &[PagingAction]) {
    (plan.objective, &plan.actions)
}

pub fn reconstruct_paging_plan(
    demands: &[BackwardDemand],
    actions: &[PagingAction],
) -> Result<ExactPagingPlan, BackwardSearchError> {
    if actions.len() != demands.len() {
        return Err(BackwardSearchError::PagingActionCount {
            expected: demands.len(),
            actual: actions.len(),
        });
    }
    let mut residents = BTreeMap::<ExprId, u8>::new();
    let mut live_lanes = 0u8;
    let mut objective = PagingObjective::default();
    let mut predicted_misses = 0u32;
    let mut refused_retains = 0u32;
    let mut live_lanes_after = Vec::with_capacity(demands.len());
    let mut peak_live_lanes = 0u8;

    for (position, (demand, action)) in demands.iter().zip(actions).enumerate() {
        if residents.remove(&demand.expr).is_some() {
            live_lanes = live_lanes
                .checked_sub(demand.width_lanes)
                .ok_or(BackwardSearchError::CostOverflow)?;
            objective.evictions = checked_increment(objective.evictions)?;
        } else {
            objective.dram_bytes = objective
                .dram_bytes
                .checked_add(demand.miss_cost.dram_bytes()?)
                .ok_or(BackwardSearchError::CostOverflow)?;
            objective.primitive_source_ops = objective
                .primitive_source_ops
                .checked_add(demand.miss_cost.ops.primitive_equivalents()?)
                .ok_or(BackwardSearchError::CostOverflow)?;
            predicted_misses = checked_increment(predicted_misses)?;
        }

        match action {
            PagingAction::Retain => {
                let next = live_lanes
                    .checked_add(demand.width_lanes)
                    .ok_or(BackwardSearchError::CostOverflow)?;
                if !demand.has_next || next > demand.gap_capacity_lanes {
                    return Err(BackwardSearchError::IllegalPagingRetain {
                        demand_position: position,
                    });
                }
                residents.insert(demand.expr, demand.width_lanes);
                live_lanes = next;
                objective.admissions = checked_increment(objective.admissions)?;
            }
            PagingAction::Bypass => {
                let retain_fits = demand.has_next
                    && live_lanes
                        .checked_add(demand.width_lanes)
                        .ok_or(BackwardSearchError::CostOverflow)?
                        <= demand.gap_capacity_lanes;
                if demand.has_next && !retain_fits {
                    refused_retains = checked_increment(refused_retains)?;
                }
                if live_lanes > demand.gap_capacity_lanes {
                    return Err(BackwardSearchError::PagingLiveSetOverCapacity {
                        demand_position: position,
                    });
                }
            }
        }
        peak_live_lanes = peak_live_lanes.max(live_lanes);
        live_lanes_after.push(live_lanes);
    }

    Ok(ExactPagingPlan {
        actions: actions.to_vec(),
        live_lanes_after,
        objective,
        predicted_misses,
        refused_retains,
        telemetry: PagingTelemetry {
            peak_live_states: usize::from(!demands.is_empty()),
            generated_states: demands
                .len()
                .try_into()
                .map_err(|_| BackwardSearchError::CostOverflow)?,
            merged_states: 0,
            peak_live_lanes,
        },
    })
}

pub fn solve_retain_all_if_exact(
    demands: &[BackwardDemand],
) -> Result<Option<ExactPagingPlan>, BackwardSearchError> {
    let actions = demands
        .iter()
        .map(|demand| {
            let nonzero_miss_cost = demand.miss_cost.dram_bytes()? != 0
                || demand.miss_cost.ops.primitive_equivalents()? != 0;
            Ok(if demand.has_next && nonzero_miss_cost {
                PagingAction::Retain
            } else {
                PagingAction::Bypass
            })
        })
        .collect::<Result<Vec<_>, BackwardSearchError>>()?;

    match reconstruct_paging_plan(demands, &actions) {
        Ok(plan) => Ok(Some(plan)),
        Err(
            BackwardSearchError::IllegalPagingRetain { .. }
            | BackwardSearchError::PagingLiveSetOverCapacity { .. },
        ) => Ok(None),
        Err(error) => Err(error),
    }
}

pub fn solve_production_paging(
    demands: &[BackwardDemand],
) -> Result<ProductionPagingResult, BackwardSearchError> {
    solve_production_paging_observed(demands, |_| {})
}

pub(crate) fn solve_production_paging_observed(
    demands: &[BackwardDemand],
    mut observe: impl FnMut(ProductionPagingProgress),
) -> Result<ProductionPagingResult, BackwardSearchError> {
    if let Some(plan) = solve_retain_all_if_exact(demands)? {
        observe(ProductionPagingProgress {
            solver: ProductionPagingSolver::RetainAll,
            current_states: usize::from(!demands.is_empty()),
            peak_states: usize::from(!demands.is_empty()),
        });
        return Ok(ProductionPagingResult {
            solver: ProductionPagingSolver::RetainAll,
            plan,
        });
    }
    if demands.iter().all(|demand| demand.width_lanes == 1) {
        observe(ProductionPagingProgress {
            solver: ProductionPagingSolver::UniformIntervals,
            current_states: 0,
            peak_states: 0,
        });
        let mut observe_uniform = |current_states, peak_states| {
            observe(ProductionPagingProgress {
                solver: ProductionPagingSolver::UniformIntervals,
                current_states,
                peak_states,
            });
        };
        return Ok(ProductionPagingResult {
            solver: ProductionPagingSolver::UniformIntervals,
            plan: solve_uniform_exact_paging_observed(demands, &mut observe_uniform)?,
        });
    }
    const CAPS: &[usize] = &[250_000, 500_000, 1_000_000, 2_000_000, 4_000_000];
    for &cap in CAPS {
        observe(ProductionPagingProgress {
            solver: ProductionPagingSolver::ResidentSets,
            current_states: 0,
            peak_states: 0,
        });
        let mut observe_resident_sets = |current_states, peak_states| {
            observe(ProductionPagingProgress {
                solver: ProductionPagingSolver::ResidentSets,
                current_states,
                peak_states,
            });
        };
        match solve_exact_paging_observed(demands, cap, &mut observe_resident_sets)? {
            PagerOutcome::Solved(plan) => {
                return Ok(ProductionPagingResult {
                    solver: ProductionPagingSolver::ResidentSets,
                    plan,
                });
            }
            PagerOutcome::SolverCapped { .. } => {}
        }
    }
    Err(BackwardSearchError::ProductionPagerResourceLimit {
        max_states: 4_000_000,
    })
}

pub fn solve_exact_paging(
    demands: &[BackwardDemand],
    state_cap: usize,
) -> Result<PagerOutcome, BackwardSearchError> {
    solve_exact_paging_observed(demands, state_cap, &mut |_, _| {})
}

fn solve_exact_paging_observed(
    demands: &[BackwardDemand],
    state_cap: usize,
    observe: &mut impl FnMut(usize, usize),
) -> Result<PagerOutcome, BackwardSearchError> {
    let (demand_leaves, leaf_widths) = dense_leaf_domain(demands)?;
    let miss_costs = demands
        .iter()
        .map(|demand| {
            Ok((
                demand.miss_cost.dram_bytes()?,
                demand.miss_cost.ops.primitive_equivalents()?,
            ))
        })
        .collect::<Result<Vec<_>, BackwardSearchError>>()?;
    let mut telemetry = PagingTelemetry::default();
    let mut arena = vec![ArenaEntry {
        predecessor: None,
        action: None,
        live_lanes_after: 0,
    }];
    let mut current = BTreeMap::from([(
        Vec::new(),
        Node {
            objective: PagingObjective::default(),
            predicted_misses: 0,
            refused_retains: 0,
            live_lanes: 0,
            parent_lex_rank: 0,
            action: PagingAction::Bypass,
            lex_rank: 0,
            predecessor: 0,
            arena_index: 0,
        },
    )]);
    observe(current.len(), current.len());

    for (position, demand) in demands.iter().enumerate() {
        let demanded_leaf = demand_leaves[position];
        let leaf_width = leaf_widths[usize::from(demanded_leaf)];
        let mut next = BTreeMap::<Vec<u16>, Node>::new();
        let mut processed_states = 0usize;

        for (residents, parent) in &current {
            processed_states += 1;
            let (base_residents, hit) = remove_demanded(residents, demanded_leaf);
            let live_without_demand = if hit {
                parent
                    .live_lanes
                    .checked_sub(leaf_width)
                    .ok_or(BackwardSearchError::CostOverflow)?
            } else {
                parent.live_lanes
            };
            let mut base = parent.clone();
            base.parent_lex_rank = parent.lex_rank;
            base.predecessor = parent.arena_index;
            base.live_lanes = live_without_demand;
            if hit {
                base.objective.evictions = checked_increment(base.objective.evictions)?;
            } else {
                base.objective.dram_bytes = base
                    .objective
                    .dram_bytes
                    .checked_add(miss_costs[position].0)
                    .ok_or(BackwardSearchError::CostOverflow)?;
                base.objective.primitive_source_ops = base
                    .objective
                    .primitive_source_ops
                    .checked_add(miss_costs[position].1)
                    .ok_or(BackwardSearchError::CostOverflow)?;
                base.predicted_misses = checked_increment(base.predicted_misses)?;
            }

            let retained_lanes = live_without_demand
                .checked_add(leaf_width)
                .ok_or(BackwardSearchError::CostOverflow)?;
            let retain_fits = demand.has_next && retained_lanes <= demand.gap_capacity_lanes;

            let mut bypass = base.clone();
            bypass.action = PagingAction::Bypass;
            if demand.has_next && !retain_fits {
                bypass.refused_retains = checked_increment(bypass.refused_retains)?;
            }
            if live_without_demand <= demand.gap_capacity_lanes {
                merge_candidate(&mut next, base_residents.clone(), bypass, &mut telemetry)?;
            }

            if retain_fits {
                let mut retained = base_residents;
                let insertion = retained
                    .binary_search(&demanded_leaf)
                    .expect_err("the demanded leaf was removed before reopening its interval");
                retained.insert(insertion, demanded_leaf);
                let mut retain = base;
                retain.action = PagingAction::Retain;
                retain.live_lanes = retained_lanes;
                retain.objective.admissions = checked_increment(retain.objective.admissions)?;
                telemetry.peak_live_lanes = telemetry.peak_live_lanes.max(retained_lanes);
                merge_candidate(&mut next, retained, retain, &mut telemetry)?;
            }
            if processed_states.is_multiple_of(4096) {
                telemetry.peak_live_states = telemetry.peak_live_states.max(next.len());
                observe(next.len(), telemetry.peak_live_states);
            }
        }

        telemetry.peak_live_states = telemetry.peak_live_states.max(next.len());
        observe(next.len(), telemetry.peak_live_states);
        if next.len() >= state_cap {
            return Ok(PagerOutcome::SolverCapped {
                cap: state_cap,
                demand_position: position,
                peak_states: telemetry.peak_live_states,
                generated_states: telemetry.generated_states,
                merged_states: telemetry.merged_states,
            });
        }

        let mut ranked = next.into_iter().collect::<Vec<_>>();
        ranked.sort_by(|(left_residents, left), (right_residents, right)| {
            (left.parent_lex_rank, left.action, left_residents).cmp(&(
                right.parent_lex_rank,
                right.action,
                right_residents,
            ))
        });
        current = BTreeMap::new();
        for (rank, (residents, mut node)) in ranked.into_iter().enumerate() {
            node.lex_rank = u64::try_from(rank).map_err(|_| BackwardSearchError::CostOverflow)?;
            node.arena_index = arena.len();
            arena.push(ArenaEntry {
                predecessor: Some(node.predecessor),
                action: Some(node.action),
                live_lanes_after: node.live_lanes,
            });
            current.insert(residents, node);
        }
    }

    let minimum_objective = current
        .values()
        .map(|node| node.objective)
        .min()
        .expect("the all-bypass state keeps every layer nonempty");
    let mut canonical_plan = None;
    for terminal in current
        .values()
        .filter(|node| node.objective == minimum_objective)
    {
        let (actions, _) = reconstruct(&arena, terminal.arena_index);
        let plan = reconstruct_paging_plan(demands, &actions)?;
        if canonical_plan
            .as_ref()
            .is_none_or(|incumbent| canonical_plan_key(&plan) < canonical_plan_key(incumbent))
        {
            canonical_plan = Some(plan);
        }
    }
    let mut plan = canonical_plan.expect("the all-bypass state keeps every layer nonempty");
    plan.telemetry = telemetry;
    Ok(PagerOutcome::Solved(plan))
}

fn dense_leaf_domain(
    demands: &[BackwardDemand],
) -> Result<(Vec<u16>, Vec<u8>), BackwardSearchError> {
    let mut domain = BTreeMap::<ExprId, u8>::new();
    for demand in demands {
        domain.entry(demand.expr).or_insert(demand.width_lanes);
    }
    u16::try_from(domain.len()).map_err(|_| BackwardSearchError::CostOverflow)?;
    let mut indices = BTreeMap::<ExprId, u16>::new();
    let mut widths = Vec::with_capacity(domain.len());
    for (index, (expr, width)) in domain.into_iter().enumerate() {
        indices.insert(
            expr,
            u16::try_from(index).map_err(|_| BackwardSearchError::CostOverflow)?,
        );
        widths.push(width);
    }
    let demand_leaves = demands.iter().map(|demand| indices[&demand.expr]).collect();
    Ok((demand_leaves, widths))
}

fn remove_demanded(residents: &[u16], demanded: u16) -> (Vec<u16>, bool) {
    let mut remaining = residents.to_vec();
    match remaining.binary_search(&demanded) {
        Ok(index) => {
            remaining.remove(index);
            (remaining, true)
        }
        Err(_) => (remaining, false),
    }
}

fn merge_candidate(
    states: &mut BTreeMap<Vec<u16>, Node>,
    residents: Vec<u16>,
    candidate: Node,
    telemetry: &mut PagingTelemetry,
) -> Result<(), BackwardSearchError> {
    telemetry.generated_states = telemetry
        .generated_states
        .checked_add(1)
        .ok_or(BackwardSearchError::CostOverflow)?;
    match states.entry(residents) {
        std::collections::btree_map::Entry::Vacant(entry) => {
            entry.insert(candidate);
        }
        std::collections::btree_map::Entry::Occupied(mut entry) => {
            telemetry.merged_states = telemetry
                .merged_states
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
            if node_key(&candidate) < node_key(entry.get()) {
                entry.insert(candidate);
            }
        }
    }
    Ok(())
}

fn checked_increment(value: u32) -> Result<u32, BackwardSearchError> {
    value
        .checked_add(1)
        .ok_or(BackwardSearchError::CostOverflow)
}

fn reconstruct(arena: &[ArenaEntry], terminal: usize) -> (Vec<PagingAction>, Vec<u8>) {
    let mut actions = Vec::new();
    let mut live_lanes_after = Vec::new();
    let mut cursor = terminal;
    while let Some(predecessor) = arena[cursor].predecessor {
        actions.push(
            arena[cursor]
                .action
                .expect("non-root arena entries carry actions"),
        );
        live_lanes_after.push(arena[cursor].live_lanes_after);
        cursor = predecessor;
    }
    actions.reverse();
    live_lanes_after.reverse();
    (actions, live_lanes_after)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use cs::gkr_compiler::dag_ir::ExprId;

    use crate::bwd::distill::{StableBwdConsumer, StableBwdExprKey, StableBwdSiteKey};
    use crate::bwd::trace::{BwdFingerprint, BwdServeKind};
    use crate::eval_plan::backward_search::problem::{
        BackwardDemand, StableFragmentKey, StableLeafDemandKey,
    };
    use crate::eval_plan::backward_search::{MAX_PAGER_STATES, SourceCost, SourceOpCost};

    use super::*;

    #[test]
    fn exact_dp_matches_exhaustive_bf_ext_and_mixed_streams() {
        for demands in [
            bf_stream(),
            ext_stream(),
            mixed_stream(),
            changing_capacity_stream(),
            shrinking_capacity_stream(),
        ] {
            let exact = solved(
                &demands,
                solve_exact_paging(&demands, MAX_PAGER_STATES).unwrap(),
            );
            let brute = exhaustive(&demands).expect("tiny stream has a solution");
            assert_eq!(exact.objective, brute.objective);
            assert_eq!(exact.actions, brute.actions);
        }
    }

    #[test]
    fn zero_cost_retain_that_fits_canonically_prefers_bypass() {
        let demands = equal_cost_stream();
        let exact = solved(
            &demands,
            solve_exact_paging(&demands, MAX_PAGER_STATES).unwrap(),
        );
        assert_eq!(
            exact.actions,
            vec![PagingAction::Bypass; exact.actions.len()]
        );
    }

    #[test]
    fn reconstructed_actions_match_exact_plan_observables() {
        let demands = mixed_stream();
        let exact = solved(
            &demands,
            solve_exact_paging(&demands, MAX_PAGER_STATES).unwrap(),
        );
        let rebuilt = reconstruct_paging_plan(&demands, &exact.actions).unwrap();
        assert_eq!(rebuilt.actions, exact.actions);
        assert_eq!(rebuilt.live_lanes_after, exact.live_lanes_after);
        assert_eq!(rebuilt.objective, exact.objective);
        assert_eq!(rebuilt.predicted_misses, exact.predicted_misses);
        assert_eq!(rebuilt.refused_retains, exact.refused_retains);
    }

    #[test]
    fn reconstructed_actions_reject_illegal_retain_and_bad_length() {
        let mut demands = mixed_stream();
        demands[0].has_next = false;
        assert!(matches!(
            reconstruct_paging_plan(
                &demands,
                &[
                    PagingAction::Retain,
                    PagingAction::Bypass,
                    PagingAction::Bypass,
                    PagingAction::Bypass,
                    PagingAction::Bypass,
                    PagingAction::Bypass,
                ],
            ),
            Err(BackwardSearchError::IllegalPagingRetain { demand_position: 0 })
        ));
        assert!(matches!(
            reconstruct_paging_plan(&demands, &[]),
            Err(BackwardSearchError::PagingActionCount { .. })
        ));
    }

    #[test]
    fn zero_demand_reconstruction_is_an_exact_empty_plan() {
        let plan = reconstruct_paging_plan(&[], &[]).unwrap();
        assert!(plan.actions.is_empty());
        assert!(plan.live_lanes_after.is_empty());
        assert_eq!(plan.objective, PagingObjective::default());
    }

    #[test]
    fn retain_all_fast_path_rejects_overlapping_intervals() {
        assert_eq!(
            solve_retain_all_if_exact(&overlapping_retain_stream()).unwrap(),
            None
        );
    }

    #[test]
    fn retain_all_fast_path_matches_exact_when_all_intervals_fit() {
        let demands = all_fitting_stream();
        let exact = solved(
            &demands,
            solve_exact_paging(&demands, MAX_PAGER_STATES).unwrap(),
        );
        let retained = solve_retain_all_if_exact(&demands).unwrap().unwrap();
        assert_eq!(retained.actions, exact.actions);
        assert_eq!(retained.objective, exact.objective);
    }

    #[test]
    fn production_pager_dispatches_by_exact_solver_domain() {
        assert_eq!(
            solve_production_paging(&all_fitting_stream())
                .unwrap()
                .solver,
            ProductionPagingSolver::RetainAll
        );
        assert_eq!(
            solve_production_paging(&overlapping_retain_stream())
                .unwrap()
                .solver,
            ProductionPagingSolver::UniformIntervals
        );
        assert_eq!(
            solve_production_paging(&shrinking_capacity_stream())
                .unwrap()
                .solver,
            ProductionPagingSolver::ResidentSets
        );
    }

    #[test]
    fn observed_resident_sets_reports_live_nonzero_states_before_return() {
        let returned = std::cell::Cell::new(false);
        let mut updates = Vec::new();
        let result = solve_production_paging_observed(&shrinking_capacity_stream(), |progress| {
            assert!(
                !returned.get(),
                "pager callback must run before solver return"
            );
            updates.push(progress);
        })
        .unwrap();
        returned.set(true);
        assert_eq!(result.solver, ProductionPagingSolver::ResidentSets);
        assert!(updates.iter().all(|update| {
            update.solver == ProductionPagingSolver::ResidentSets
                && update.current_states <= update.peak_states
        }));
        assert!(
            updates
                .iter()
                .any(|update| update.current_states > 0 && update.peak_states > 0)
        );
    }

    #[test]
    fn observed_uniform_solver_reports_live_nonzero_states_before_return() {
        let returned = std::cell::Cell::new(false);
        let mut updates = Vec::new();
        let result = solve_production_paging_observed(&overlapping_retain_stream(), |progress| {
            assert!(
                !returned.get(),
                "pager callback must run before solver return"
            );
            updates.push(progress);
        })
        .unwrap();
        returned.set(true);
        assert_eq!(result.solver, ProductionPagingSolver::UniformIntervals);
        assert!(updates.iter().all(|update| {
            update.solver == ProductionPagingSolver::UniformIntervals
                && update.current_states <= update.peak_states
        }));
        assert!(
            updates
                .iter()
                .any(|update| update.current_states > 0 && update.peak_states > 0)
        );
    }

    #[test]
    fn one_demand_can_close_and_reopen_while_other_residents_remain() {
        let demands = reopen_stream();
        let exact = solved(
            &demands,
            solve_exact_paging(&demands, MAX_PAGER_STATES).unwrap(),
        );
        assert_eq!(exact.telemetry.peak_live_lanes, 5);
        assert_eq!(exact.refused_retains, 0);
    }

    #[test]
    fn bypass_rejects_unrelated_resident_over_shrunk_gap_capacity() {
        let demands = shrinking_capacity_stream();
        let exact = solved(
            &demands,
            solve_exact_paging(&demands, MAX_PAGER_STATES).unwrap(),
        );
        assert_eq!(exact.actions, vec![PagingAction::Bypass; 3]);
        assert_eq!(
            exact.objective,
            PagingObjective {
                dram_bytes: 207,
                primitive_source_ops: 41,
                admissions: 0,
                evictions: 0,
            }
        );
    }

    #[test]
    fn tiny_live_state_cap_returns_uncomputed_solver_capped() {
        match solve_exact_paging(&mixed_stream(), 1).unwrap() {
            PagerOutcome::SolverCapped {
                cap,
                generated_states,
                merged_states,
                ..
            } => {
                assert_eq!(cap, 1);
                assert!(generated_states > 0);
                assert!(merged_states <= generated_states);
            }
            solved => panic!("expected capped pager, got {solved:?}"),
        }
    }

    fn solved(demands: &[BackwardDemand], outcome: PagerOutcome) -> ExactPagingPlan {
        let plan = match outcome {
            PagerOutcome::Solved(plan) => plan,
            capped => panic!("expected a solved paging plan, got {capped:?}"),
        };
        assert_eq!(plan.live_lanes_after.len(), demands.len());
        for (position, (&live_lanes, demand)) in
            plan.live_lanes_after.iter().zip(demands).enumerate()
        {
            assert!(
                live_lanes <= demand.gap_capacity_lanes,
                "position {position} leaves {live_lanes} lanes live against capacity {}",
                demand.gap_capacity_lanes,
            );
        }
        plan
    }

    fn exhaustive(demands: &[BackwardDemand]) -> Option<ExactPagingPlan> {
        assert!(demands.len() <= 8);
        let widths = demands
            .iter()
            .map(|demand| (demand.expr, demand.width_lanes))
            .collect::<BTreeMap<_, _>>();
        let mut best: Option<ExactPagingPlan> = None;

        for mask in 0..(1usize << demands.len()) {
            let mut residents = BTreeSet::new();
            let mut actions = Vec::with_capacity(demands.len());
            let mut live_lanes_after = Vec::with_capacity(demands.len());
            let mut objective = PagingObjective::default();
            let mut predicted_misses = 0u32;
            let mut refused_retains = 0u32;
            let mut legal = true;

            for (position, demand) in demands.iter().enumerate() {
                if residents.remove(&demand.expr) {
                    objective.evictions += 1;
                } else {
                    predicted_misses += 1;
                    objective.dram_bytes += demand.miss_cost.dram_bytes().unwrap();
                    objective.primitive_source_ops +=
                        demand.miss_cost.ops.primitive_equivalents().unwrap();
                }

                let action = if mask & (1 << position) == 0 {
                    PagingAction::Bypass
                } else {
                    PagingAction::Retain
                };
                let live_without_demand = resident_lanes(&residents, &widths);
                match action {
                    PagingAction::Bypass => {
                        if demand.has_next
                            && live_without_demand + demand.width_lanes > demand.gap_capacity_lanes
                        {
                            refused_retains += 1;
                        }
                    }
                    PagingAction::Retain => {
                        if !demand.has_next {
                            legal = false;
                            break;
                        }
                        residents.insert(demand.expr);
                        objective.admissions += 1;
                    }
                }
                actions.push(action);
                let live_lanes = resident_lanes(&residents, &widths);
                if live_lanes > demand.gap_capacity_lanes {
                    legal = false;
                    break;
                }
                live_lanes_after.push(live_lanes);
            }

            if !legal {
                continue;
            }
            let peak_live_lanes = live_lanes_after.iter().copied().max().unwrap_or(0);
            let candidate = ExactPagingPlan {
                actions,
                live_lanes_after,
                objective,
                predicted_misses,
                refused_retains,
                telemetry: PagingTelemetry {
                    peak_live_lanes,
                    ..PagingTelemetry::default()
                },
            };
            if best.as_ref().is_none_or(|incumbent| {
                (candidate.objective, &candidate.actions)
                    < (incumbent.objective, &incumbent.actions)
            }) {
                best = Some(candidate);
            }
        }

        best
    }

    fn resident_lanes(residents: &BTreeSet<ExprId>, widths: &BTreeMap<ExprId, u8>) -> u8 {
        residents.iter().map(|resident| widths[resident]).sum()
    }

    fn bf_stream() -> Vec<BackwardDemand> {
        stream(&[
            (0, 1, 1, 20, 3),
            (1, 1, 1, 11, 2),
            (0, 1, 1, 20, 3),
            (1, 1, 0, 11, 2),
        ])
    }

    fn ext_stream() -> Vec<BackwardDemand> {
        stream(&[
            (0, 4, 4, 80, 12),
            (1, 4, 4, 44, 8),
            (0, 4, 4, 80, 12),
            (1, 4, 0, 44, 8),
        ])
    }

    fn mixed_stream() -> Vec<BackwardDemand> {
        stream(&[
            (0, 4, 5, 80, 12),
            (1, 1, 5, 9, 1),
            (2, 4, 5, 64, 9),
            (0, 4, 5, 80, 12),
            (1, 1, 5, 9, 1),
            (2, 4, 0, 64, 9),
        ])
    }

    fn changing_capacity_stream() -> Vec<BackwardDemand> {
        stream(&[
            (0, 4, 5, 90, 13),
            (1, 1, 1, 8, 1),
            (2, 1, 5, 7, 1),
            (0, 4, 4, 90, 13),
            (1, 1, 1, 8, 1),
            (2, 1, 0, 7, 1),
        ])
    }

    fn shrinking_capacity_stream() -> Vec<BackwardDemand> {
        stream(&[(0, 4, 4, 100, 20), (1, 1, 1, 7, 1), (0, 4, 0, 100, 20)])
    }

    fn equal_cost_stream() -> Vec<BackwardDemand> {
        stream(&[(0, 1, 1, 0, 0), (0, 1, 1, 0, 0), (0, 1, 0, 0, 0)])
    }

    fn reopen_stream() -> Vec<BackwardDemand> {
        stream(&[
            (0, 4, 5, 100, 20),
            (1, 1, 5, 30, 5),
            (0, 4, 5, 100, 20),
            (1, 1, 5, 30, 5),
            (0, 4, 0, 100, 20),
        ])
    }

    fn overlapping_retain_stream() -> Vec<BackwardDemand> {
        stream(&[
            (0, 1, 1, 10, 1),
            (1, 1, 1, 10, 1),
            (0, 1, 1, 10, 1),
            (1, 1, 0, 10, 1),
        ])
    }

    fn all_fitting_stream() -> Vec<BackwardDemand> {
        stream(&[
            (0, 1, 2, 10, 1),
            (1, 1, 2, 10, 1),
            (0, 1, 2, 10, 1),
            (1, 1, 0, 10, 1),
        ])
    }

    fn stream(spec: &[(u32, u8, u8, u128, u128)]) -> Vec<BackwardDemand> {
        let mut later = BTreeSet::new();
        let mut has_next = vec![false; spec.len()];
        for (position, &(expr, _, _, _, _)) in spec.iter().enumerate().rev() {
            has_next[position] = later.contains(&expr);
            later.insert(expr);
        }
        spec.iter()
            .enumerate()
            .map(
                |(position, &(expr, width_lanes, gap_capacity_lanes, dram, ops))| {
                    demand(
                        position,
                        expr,
                        width_lanes,
                        gap_capacity_lanes,
                        dram,
                        ops,
                        has_next[position],
                    )
                },
            )
            .collect()
    }

    fn demand(
        position: usize,
        expr: u32,
        width_lanes: u8,
        gap_capacity_lanes: u8,
        dram: u128,
        ops: u128,
        has_next: bool,
    ) -> BackwardDemand {
        let expr = ExprId(expr);
        let stable_expr = StableBwdExprKey::Canonical(expr);
        BackwardDemand {
            key: StableLeafDemandKey {
                fragment: StableFragmentKey {
                    atoms: vec![stable_expr],
                    recipe: Vec::new(),
                },
                site: StableBwdSiteKey {
                    consumer: StableBwdConsumer::RootOutput,
                    value: stable_expr,
                },
                occurrence_in_fragment: position as u32,
            },
            fp: BwdFingerprint {
                term: position as u32,
                kind: BwdServeKind::Operand,
                value: expr,
                consumer: None,
            },
            expr,
            source_desc: Some(expr.0 as u16),
            instruction: position,
            physical_ordinal: position,
            width_lanes,
            gap_capacity_lanes,
            miss_cost: SourceCost {
                plain_read_bytes: dram,
                ops: SourceOpCost {
                    bf_add: ops,
                    ..SourceOpCost::default()
                },
                ..SourceCost::default()
            },
            has_next,
        }
    }
}
