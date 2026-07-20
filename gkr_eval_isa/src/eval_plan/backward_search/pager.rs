use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::ExprId;

use super::BackwardSearchError;
use super::problem::BackwardDemand;

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

pub fn solve_exact_paging(
    demands: &[BackwardDemand],
    state_cap: usize,
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

    for (position, demand) in demands.iter().enumerate() {
        let demanded_leaf = demand_leaves[position];
        let leaf_width = leaf_widths[usize::from(demanded_leaf)];
        let mut next = BTreeMap::<Vec<u16>, Node>::new();

        for (residents, parent) in &current {
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
        }

        telemetry.peak_live_states = telemetry.peak_live_states.max(next.len());
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

    let (_, terminal) = current
        .iter()
        .min_by_key(|(residents, node)| (node.objective, node.lex_rank, *residents))
        .expect("the all-bypass state keeps every layer nonempty");
    let (actions, live_lanes_after) = reconstruct(&arena, terminal.arena_index);
    Ok(PagerOutcome::Solved(ExactPagingPlan {
        actions,
        live_lanes_after,
        objective: terminal.objective,
        predicted_misses: terminal.predicted_misses,
        refused_retains: terminal.refused_retains,
        telemetry,
    }))
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
    fn bypass_wins_equal_cost_and_no_retention_optimum() {
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
