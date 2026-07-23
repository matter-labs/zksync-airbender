use std::cmp::Ordering;
use std::collections::{BTreeMap, BinaryHeap};

use cs::gkr_compiler::dag_ir::ExprId;

use super::BackwardSearchError;
use super::pager::{ExactPagingPlan, PagingAction, reconstruct_paging_plan};
use super::problem::BackwardDemand;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct SignedU128 {
    negative: bool,
    magnitude: u128,
}

impl SignedU128 {
    fn negative(value: u128) -> Self {
        Self {
            negative: value != 0,
            magnitude: value,
        }
    }

    fn positive(value: u128) -> Self {
        Self {
            negative: false,
            magnitude: value,
        }
    }

    fn checked_neg(&self) -> Self {
        Self {
            negative: self.magnitude != 0 && !self.negative,
            magnitude: self.magnitude,
        }
    }

    fn checked_add(&self, other: &Self) -> Result<Self, BackwardSearchError> {
        if self.negative == other.negative {
            let magnitude = self
                .magnitude
                .checked_add(other.magnitude)
                .ok_or(BackwardSearchError::CostOverflow)?;
            Ok(Self {
                negative: self.negative && magnitude != 0,
                magnitude,
            })
        } else {
            Ok(match self.magnitude.cmp(&other.magnitude) {
                Ordering::Greater => Self {
                    negative: self.negative,
                    magnitude: self.magnitude - other.magnitude,
                },
                Ordering::Less => Self {
                    negative: other.negative,
                    magnitude: other.magnitude - self.magnitude,
                },
                Ordering::Equal => Self::default(),
            })
        }
    }
}

impl Ord for SignedU128 {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.negative, other.negative) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => self.magnitude.cmp(&other.magnitude),
            (true, true) => other.magnitude.cmp(&self.magnitude),
        }
    }
}

impl PartialOrd for SignedU128 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct SignedBig {
    negative: bool,
    words: Vec<u64>,
}

impl SignedBig {
    fn bit(bit: usize) -> Self {
        let mut words = vec![0; bit / 64 + 1];
        words[bit / 64] = 1u64 << (bit % 64);
        Self {
            negative: false,
            words,
        }
    }

    fn checked_neg(&self) -> Self {
        Self {
            negative: !self.words.is_empty() && !self.negative,
            words: self.words.clone(),
        }
    }

    fn checked_add(&self, other: &Self) -> Result<Self, BackwardSearchError> {
        if self.negative == other.negative {
            let mut words = Vec::with_capacity(self.words.len().max(other.words.len()) + 1);
            let mut carry = 0u128;
            for index in 0..self.words.len().max(other.words.len()) {
                let sum = u128::from(self.words.get(index).copied().unwrap_or(0))
                    + u128::from(other.words.get(index).copied().unwrap_or(0))
                    + carry;
                words.push(sum as u64);
                carry = sum >> 64;
            }
            if carry != 0 {
                words.push(carry as u64);
            }
            let mut result = Self {
                negative: self.negative,
                words,
            };
            result.normalize();
            Ok(result)
        } else {
            match magnitude_cmp(&self.words, &other.words) {
                Ordering::Equal => Ok(Self::default()),
                Ordering::Greater => Ok(Self::from_difference(
                    self.negative,
                    &self.words,
                    &other.words,
                )),
                Ordering::Less => Ok(Self::from_difference(
                    other.negative,
                    &other.words,
                    &self.words,
                )),
            }
        }
    }

    fn from_difference(negative: bool, larger: &[u64], smaller: &[u64]) -> Self {
        let mut words = Vec::with_capacity(larger.len());
        let mut borrow = 0u128;
        for (index, &left) in larger.iter().enumerate() {
            let right = u128::from(smaller.get(index).copied().unwrap_or(0)) + borrow;
            let left = u128::from(left);
            if left >= right {
                words.push((left - right) as u64);
                borrow = 0;
            } else {
                words.push(((1u128 << 64) + left - right) as u64);
                borrow = 1;
            }
        }
        debug_assert_eq!(borrow, 0);
        let mut result = Self { negative, words };
        result.normalize();
        result
    }

    fn normalize(&mut self) {
        while self.words.last() == Some(&0) {
            self.words.pop();
        }
        if self.words.is_empty() {
            self.negative = false;
        }
    }
}

fn magnitude_cmp(left: &[u64], right: &[u64]) -> Ordering {
    match left.len().cmp(&right.len()) {
        Ordering::Equal => left.iter().rev().cmp(right.iter().rev()),
        ordering => ordering,
    }
}

impl Ord for SignedBig {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.negative, other.negative) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => magnitude_cmp(&self.words, &other.words),
            (true, true) => magnitude_cmp(&other.words, &self.words),
        }
    }
}

impl PartialOrd for SignedBig {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
struct Cost {
    // After the mandatory-blocker field, tuple order is the canonical pager
    // order. Earlier actions receive higher binary place values, so minimizing
    // `action_bits` is exactly the lexicographically smallest Bypass/Retain
    // stream after the numeric ties.
    negative_blockers: SignedU128,
    negative_saved_dram: SignedU128,
    negative_saved_ops: SignedU128,
    selected_intervals: SignedU128,
    action_bits: SignedBig,
}

impl Cost {
    fn real_interval(dram: u128, ops: u128, action_bit: usize) -> Self {
        Self {
            negative_saved_dram: SignedU128::negative(dram),
            negative_saved_ops: SignedU128::negative(ops),
            selected_intervals: SignedU128::positive(1),
            action_bits: SignedBig::bit(action_bit),
            ..Self::default()
        }
    }

    fn blocker() -> Self {
        Self {
            negative_blockers: SignedU128::negative(1),
            ..Self::default()
        }
    }

    fn checked_neg(&self) -> Self {
        Self {
            negative_blockers: self.negative_blockers.checked_neg(),
            negative_saved_dram: self.negative_saved_dram.checked_neg(),
            negative_saved_ops: self.negative_saved_ops.checked_neg(),
            selected_intervals: self.selected_intervals.checked_neg(),
            action_bits: self.action_bits.checked_neg(),
        }
    }

    fn checked_add(&self, other: &Self) -> Result<Self, BackwardSearchError> {
        Ok(Self {
            negative_blockers: self
                .negative_blockers
                .checked_add(&other.negative_blockers)?,
            negative_saved_dram: self
                .negative_saved_dram
                .checked_add(&other.negative_saved_dram)?,
            negative_saved_ops: self
                .negative_saved_ops
                .checked_add(&other.negative_saved_ops)?,
            selected_intervals: self
                .selected_intervals
                .checked_add(&other.selected_intervals)?,
            action_bits: self.action_bits.checked_add(&other.action_bits)?,
        })
    }

    fn checked_sub(&self, other: &Self) -> Result<Self, BackwardSearchError> {
        self.checked_add(&other.checked_neg())
    }
}

#[derive(Clone, Debug)]
struct Edge {
    to: usize,
    reverse: usize,
    residual_capacity: u16,
    cost: Cost,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct QueueEntry {
    cost: Cost,
    node: usize,
}

impl Ord for QueueEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .cost
            .cmp(&self.cost)
            .then_with(|| other.node.cmp(&self.node))
    }
}

impl PartialOrd for QueueEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub fn solve_uniform_exact_paging(
    demands: &[BackwardDemand],
) -> Result<ExactPagingPlan, BackwardSearchError> {
    solve_uniform_exact_paging_observed(demands, &mut |_, _| {})
}

pub(crate) fn solve_uniform_exact_paging_observed(
    demands: &[BackwardDemand],
    observe: &mut impl FnMut(usize, usize),
) -> Result<ExactPagingPlan, BackwardSearchError> {
    for (demand_position, demand) in demands.iter().enumerate() {
        if demand.width_lanes != 1 {
            return Err(BackwardSearchError::UniformPagerMixedWidth {
                demand_position,
                width_lanes: demand.width_lanes,
            });
        }
    }

    let mut actions = vec![PagingAction::Bypass; demands.len()];
    let Some(max_capacity) = demands.iter().map(|demand| demand.gap_capacity_lanes).max() else {
        return reconstruct_paging_plan(demands, &actions);
    };
    if max_capacity == 0 {
        return reconstruct_paging_plan(demands, &actions);
    }

    // A fixed `max_capacity` flow crosses every gap. A selected interval edge
    // skips the corresponding adjacent edges and therefore occupies one lane
    // on every crossed gap.
    let mut graph = vec![Vec::<Edge>::new(); demands.len() + 1];
    for position in 0..demands.len() {
        add_edge(
            &mut graph,
            position,
            position + 1,
            u16::from(max_capacity),
            Cost::default(),
        );
    }

    let mut next_positions = BTreeMap::<ExprId, usize>::new();
    let mut real_edges = Vec::new();
    for start in (0..demands.len()).rev() {
        let demand = &demands[start];
        let next = next_positions.insert(demand.expr, start);
        if !demand.has_next {
            continue;
        }
        let end = next.expect("has_next demands have a later demand of the same expression");
        let dram = demands[end].miss_cost.dram_bytes()?;
        let ops = demands[end].miss_cost.ops.primitive_equivalents()?;
        let edge_index = graph[start].len();
        add_edge(
            &mut graph,
            start,
            end,
            1,
            Cost::real_interval(dram, ops, demands.len() - 1 - start),
        );
        real_edges.push((start, edge_index));
    }

    // Mandatory blocker intervals occupy `max_capacity - gap_capacity` lanes.
    // Their leading objective component makes every blocker win before any
    // real interval tradeoff, reducing variable capacities to a constant-flow
    // min-cost formulation without scalarizing the checked source costs.
    let blockers = decompose_blockers(demands, max_capacity)?;
    for (start, end) in blockers {
        add_edge(&mut graph, start, end, 1, Cost::blocker());
    }

    min_cost_flow(&mut graph, usize::from(max_capacity), observe)?;
    for (start, edge_index) in real_edges {
        if graph[start][edge_index].residual_capacity == 0 {
            actions[start] = PagingAction::Retain;
        }
    }
    reconstruct_paging_plan(demands, &actions)
}

fn decompose_blockers(
    demands: &[BackwardDemand],
    max_capacity: u8,
) -> Result<Vec<(usize, usize)>, BackwardSearchError> {
    let mut starts = Vec::new();
    let mut blockers = Vec::new();
    let mut previous = 0u8;
    for (position, demand) in demands.iter().enumerate() {
        let blocked = max_capacity
            .checked_sub(demand.gap_capacity_lanes)
            .ok_or(BackwardSearchError::CostOverflow)?;
        while previous < blocked {
            starts.push(position);
            previous = previous
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
        }
        while previous > blocked {
            let start = starts
                .pop()
                .expect("positive blocker depth has an open blocker interval");
            blockers.push((start, position));
            previous -= 1;
        }
    }
    while let Some(start) = starts.pop() {
        blockers.push((start, demands.len()));
    }
    Ok(blockers)
}

fn add_edge(graph: &mut [Vec<Edge>], from: usize, to: usize, capacity: u16, cost: Cost) {
    let forward = graph[from].len();
    let reverse = graph[to].len();
    graph[from].push(Edge {
        to,
        reverse,
        residual_capacity: capacity,
        cost: cost.clone(),
    });
    graph[to].push(Edge {
        to: from,
        reverse: forward,
        residual_capacity: 0,
        cost: cost.checked_neg(),
    });
}

fn min_cost_flow(
    graph: &mut [Vec<Edge>],
    units: usize,
    observe: &mut impl FnMut(usize, usize),
) -> Result<(), BackwardSearchError> {
    let terminal = graph.len() - 1;
    let mut potential = dag_initial_potentials(graph)?;
    let mut peak_states = 0usize;
    for _ in 0..units {
        let mut distance = vec![None::<Cost>; graph.len()];
        let mut predecessor = vec![None::<(usize, usize)>; graph.len()];
        let mut queue = BinaryHeap::new();
        distance[0] = Some(Cost::default());
        queue.push(QueueEntry {
            cost: Cost::default(),
            node: 0,
        });
        peak_states = peak_states.max(queue.len());
        observe(queue.len(), peak_states);
        let mut processed = 0usize;

        while let Some(QueueEntry { cost, node }) = queue.pop() {
            processed += 1;
            if distance[node].as_ref() != Some(&cost) {
                continue;
            }
            for (edge_index, edge) in graph[node].iter().enumerate() {
                if edge.residual_capacity == 0 {
                    continue;
                }
                let reduced = edge
                    .cost
                    .checked_add(&potential[node])?
                    .checked_sub(&potential[edge.to])?;
                debug_assert!(reduced >= Cost::default());
                let candidate = cost.checked_add(&reduced)?;
                if distance[edge.to]
                    .as_ref()
                    .is_none_or(|incumbent| candidate < *incumbent)
                {
                    distance[edge.to] = Some(candidate.clone());
                    predecessor[edge.to] = Some((node, edge_index));
                    queue.push(QueueEntry {
                        cost: candidate,
                        node: edge.to,
                    });
                    peak_states = peak_states.max(queue.len());
                }
            }
            if processed.is_multiple_of(4096) {
                observe(queue.len(), peak_states);
            }
        }
        observe(queue.len(), peak_states);

        for (node, reached) in distance.iter().enumerate() {
            if let Some(reached) = reached {
                potential[node] = potential[node].checked_add(reached)?;
            }
        }
        let mut cursor = terminal;
        while cursor != 0 {
            let (from, edge_index) = predecessor[cursor]
                .expect("adjacent edges leave every required flow path reachable");
            let reverse = graph[from][edge_index].reverse;
            graph[from][edge_index].residual_capacity -= 1;
            graph[cursor][reverse].residual_capacity = graph[cursor][reverse]
                .residual_capacity
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
            cursor = from;
        }
    }
    Ok(())
}

fn dag_initial_potentials(graph: &[Vec<Edge>]) -> Result<Vec<Cost>, BackwardSearchError> {
    let mut distance = vec![None::<Cost>; graph.len()];
    distance[0] = Some(Cost::default());
    for node in 0..graph.len() {
        let Some(base) = distance[node].clone() else {
            continue;
        };
        for edge in &graph[node] {
            if edge.residual_capacity == 0 || edge.to <= node {
                continue;
            }
            let candidate = base.checked_add(&edge.cost)?;
            if distance[edge.to]
                .as_ref()
                .is_none_or(|incumbent| candidate < *incumbent)
            {
                distance[edge.to] = Some(candidate);
            }
        }
    }
    Ok(distance
        .into_iter()
        .map(|cost| cost.expect("adjacent edges reach every position"))
        .collect())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use cs::gkr_compiler::dag_ir::ExprId;

    use crate::bwd::distill::{StableBwdConsumer, StableBwdExprKey, StableBwdSiteKey};
    use crate::bwd::trace::{BwdFingerprint, BwdServeKind};
    use crate::eval_plan::ValueFingerprint;
    use crate::eval_plan::backward_search::problem::{
        BackwardDemand, StableFragmentKey, StableLeafDemandKey,
    };
    use crate::eval_plan::backward_search::{
        BackwardSearchError, ExactPagingPlan, MAX_PAGER_STATES, PagerOutcome, PagingAction,
        SourceCost, SourceOpCost, reconstruct_paging_plan, solve_exact_paging,
    };

    use super::solve_uniform_exact_paging;

    #[test]
    fn uniform_solver_matches_exhaustive_variable_capacity_cases() {
        for demands in exhaustive_uniform_fixtures() {
            let expected = exhaustive_best(&demands).expect("all-bypass is legal");
            let actual = solve_uniform_exact_paging(&demands).unwrap();
            assert_eq!(actual.actions, expected.actions, "demands: {demands:?}");
            assert_eq!(actual.objective, expected.objective, "demands: {demands:?}");
        }
    }

    #[test]
    fn uniform_solver_rejects_mixed_width_input() {
        let mut demands = uniform_fixture();
        demands[1].width_lanes = 4;
        assert!(matches!(
            solve_uniform_exact_paging(&demands),
            Err(BackwardSearchError::UniformPagerMixedWidth {
                demand_position: 1,
                width_lanes: 4,
            })
        ));
    }

    #[test]
    fn uniform_solver_matches_resident_sets_on_traversable_unit_fixtures() {
        for demands in [
            costed_stream(&[(0, 1, 20, 3), (1, 1, 11, 2), (0, 1, 20, 3), (1, 0, 11, 2)]),
            costed_stream(&[(0, 1, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0)]),
            costed_stream(&[(0, 1, 10, 1), (1, 1, 10, 1), (0, 1, 10, 1), (1, 0, 10, 1)]),
            costed_stream(&[(0, 2, 10, 1), (1, 2, 10, 1), (0, 2, 10, 1), (1, 0, 10, 1)]),
        ] {
            let uniform = solve_uniform_exact_paging(&demands).unwrap();
            let PagerOutcome::Solved(resident_sets) =
                solve_exact_paging(&demands, MAX_PAGER_STATES).unwrap()
            else {
                panic!("tiny fixture must not cap");
            };
            assert_eq!(uniform.actions, resident_sets.actions);
            assert_eq!(uniform.objective, resident_sets.objective);
        }
    }

    #[test]
    fn uniform_solver_uses_canonical_action_order_for_exact_ties() {
        let mut demands = stream(&[0, 1, 0, 1], &[1, 1, 1, 0]);
        for demand in &mut demands {
            demand.miss_cost = SourceCost {
                plain_read_bytes: 10,
                ops: SourceOpCost {
                    bf_add: 2,
                    ..SourceOpCost::default()
                },
                ..SourceCost::default()
            };
        }
        let plan = solve_uniform_exact_paging(&demands).unwrap();
        assert_eq!(
            plan.actions,
            vec![
                PagingAction::Bypass,
                PagingAction::Retain,
                PagingAction::Bypass,
                PagingAction::Bypass,
            ]
        );

        for demand in &mut demands {
            demand.miss_cost = SourceCost::default();
        }
        assert_eq!(
            solve_uniform_exact_paging(&demands).unwrap().actions,
            vec![PagingAction::Bypass; demands.len()]
        );
    }

    fn exhaustive_best(demands: &[BackwardDemand]) -> Option<ExactPagingPlan> {
        assert!(demands.len() <= 8);
        let mut best: Option<ExactPagingPlan> = None;
        for mask in 0..(1usize << demands.len()) {
            let actions = (0..demands.len())
                .map(|position| {
                    if mask & (1 << position) == 0 {
                        PagingAction::Bypass
                    } else {
                        PagingAction::Retain
                    }
                })
                .collect::<Vec<_>>();
            let Ok(candidate) = reconstruct_paging_plan(demands, &actions) else {
                continue;
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

    fn exhaustive_uniform_fixtures() -> Vec<Vec<BackwardDemand>> {
        let mut fixtures = vec![Vec::new(), uniform_fixture()];
        for len in 1..=6 {
            for leaf_bits in 0..(1usize << len) {
                let exprs = (0..len)
                    .map(|position| ((leaf_bits >> position) & 1) as u32)
                    .collect::<Vec<_>>();
                for capacity_bits in 0..(1usize << len) {
                    let capacities = (0..len)
                        .map(|position| ((capacity_bits >> position) & 1) as u8)
                        .collect::<Vec<_>>();
                    fixtures.push(stream(&exprs, &capacities));
                }
            }
        }
        fixtures
    }

    fn uniform_fixture() -> Vec<BackwardDemand> {
        stream(&[0, 1, 0, 1, 0], &[2, 1, 1, 2, 0])
    }

    fn stream(exprs: &[u32], capacities: &[u8]) -> Vec<BackwardDemand> {
        assert_eq!(exprs.len(), capacities.len());
        let mut later = BTreeSet::new();
        let mut has_next = vec![false; exprs.len()];
        for (position, &expr) in exprs.iter().enumerate().rev() {
            has_next[position] = later.contains(&expr);
            later.insert(expr);
        }
        exprs
            .iter()
            .zip(capacities)
            .enumerate()
            .map(|(position, (&expr, &gap_capacity_lanes))| {
                demand(position, expr, gap_capacity_lanes, has_next[position])
            })
            .collect()
    }

    fn costed_stream(spec: &[(u32, u8, u128, u128)]) -> Vec<BackwardDemand> {
        let exprs = spec.iter().map(|entry| entry.0).collect::<Vec<_>>();
        let capacities = spec.iter().map(|entry| entry.1).collect::<Vec<_>>();
        let mut demands = stream(&exprs, &capacities);
        for (demand, &(_, _, dram, ops)) in demands.iter_mut().zip(spec) {
            demand.miss_cost = SourceCost {
                plain_read_bytes: dram,
                ops: SourceOpCost {
                    bf_add: ops,
                    ..SourceOpCost::default()
                },
                ..SourceCost::default()
            };
        }
        demands
    }

    fn demand(
        position: usize,
        expr: u32,
        gap_capacity_lanes: u8,
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
            physical: ValueFingerprint([u64::from(expr.0), 0]),
            source_desc: Some(expr.0 as u16),
            instruction: position,
            physical_ordinal: position,
            width_lanes: 1,
            gap_capacity_lanes,
            miss_cost: SourceCost {
                plain_read_bytes: u128::from(expr.0 + 1) * 11 + position as u128,
                ops: SourceOpCost {
                    bf_add: u128::from(expr.0 + 1) * 3 + (position % 2) as u128,
                    ..SourceOpCost::default()
                },
                ..SourceCost::default()
            },
            has_next,
        }
    }
}
