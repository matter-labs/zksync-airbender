use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::{DagLayer, ExprId};
use rayon::prelude::*;

use crate::bwd::distill::DistilledLayer;
use crate::eval_plan::search_driver::{SearchAdapter, StableRng};

use super::pager::{
    ExactPagingPlan, PagerOutcome, PagingAction, PagingObjective, PagingTelemetry,
    solve_exact_paging,
};
use super::problem::{
    BackwardSearchProblem, StableFragmentKey, StableLeafDemandKey, build_problem_for_order,
};
use super::{
    BackwardScore, BackwardSearchError, CertifiedBackwardCandidate, MAX_PAGER_STATES,
    compile_and_certify_paging,
};

#[derive(Clone, Debug, PartialEq)]
pub struct BackwardGenome {
    pub fragment_order_key: BTreeMap<StableFragmentKey, f64>,
    pub leaf_cache_priority: BTreeMap<StableLeafDemandKey, f64>,
}

impl BackwardGenome {
    pub fn constructive(problem: &BackwardSearchProblem) -> Self {
        let fragment_order_key = problem
            .constructive_order
            .iter()
            .enumerate()
            .map(|(position, key)| (key.clone(), position as f64))
            .collect();
        let leaf_cache_priority = problem
            .leaf_domain
            .iter()
            .cloned()
            .map(|key| (key, -1.0))
            .collect();
        Self {
            fragment_order_key,
            leaf_cache_priority,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BackwardSearchArm {
    OrderOnly,
    CacheOnly,
    Joint,
}

pub fn paging_seed(
    problem: &BackwardSearchProblem,
    paging: &ExactPagingPlan,
) -> Result<BackwardGenome, BackwardSearchError> {
    if paging.actions.len() != problem.demands.len() {
        return Err(BackwardSearchError::PagingSeedMismatch);
    }
    let mut genome = BackwardGenome::constructive(problem);
    for (demand, action) in problem.demands.iter().zip(&paging.actions) {
        let priority = match action {
            PagingAction::Bypass => -1.0,
            PagingAction::Retain => 1.0,
        };
        let Some(slot) = genome.leaf_cache_priority.get_mut(&demand.key) else {
            return Err(BackwardSearchError::InvalidGenomeDomain {
                gene: "leaf cache priority",
            });
        };
        *slot = priority;
    }
    match decode_cache_actions(problem, &genome) {
        Ok(actions) if actions == paging.actions => Ok(genome),
        Ok(_) | Err(_) => Err(BackwardSearchError::PagingSeedMismatch),
    }
}

pub fn decode_fragment_order(
    problem: &BackwardSearchProblem,
    genome: &BackwardGenome,
) -> Result<Vec<StableFragmentKey>, BackwardSearchError> {
    validate_domain(
        &problem.fragment_domain,
        &genome.fragment_order_key,
        "fragment order key",
    )?;
    let mut keyed = problem
        .fragment_domain
        .iter()
        .map(|fragment| {
            let value = genome.fragment_order_key[fragment];
            if !value.is_finite() {
                return Err(BackwardSearchError::NonFiniteGenomeValue {
                    gene: "fragment order key",
                });
            }
            Ok((ordered_f64_bits(value), fragment.clone()))
        })
        .collect::<Result<Vec<_>, BackwardSearchError>>()?;
    keyed.sort();
    Ok(keyed.into_iter().map(|(_, fragment)| fragment).collect())
}

pub fn decode_cache_actions(
    problem: &BackwardSearchProblem,
    genome: &BackwardGenome,
) -> Result<Vec<PagingAction>, BackwardSearchError> {
    Ok(decode_cache_plan(problem, genome)?.actions)
}

pub(crate) fn mutate_genome(
    problem: &BackwardSearchProblem,
    arm: BackwardSearchArm,
    genome: &mut BackwardGenome,
    rng: &mut StableRng,
) {
    match arm {
        BackwardSearchArm::OrderOnly => mutate_order(problem, genome, rng),
        BackwardSearchArm::CacheOnly => mutate_cache(problem, genome, rng),
        BackwardSearchArm::Joint => {
            if rng.next_u64() & 1 == 0 {
                mutate_order(problem, genome, rng);
            } else {
                mutate_cache(problem, genome, rng);
            }
        }
    }
}

pub struct BackwardAdapter<'a> {
    canonical: &'a DagLayer,
    distilled: &'a DistilledLayer,
    problem: &'a BackwardSearchProblem,
    exact_seed: &'a ExactPagingPlan,
    trace_len: usize,
    arm: BackwardSearchArm,
}

impl<'a> BackwardAdapter<'a> {
    pub fn new(
        canonical: &'a DagLayer,
        distilled: &'a DistilledLayer,
        problem: &'a BackwardSearchProblem,
        exact_seed: &'a ExactPagingPlan,
        trace_len: usize,
        arm: BackwardSearchArm,
    ) -> Self {
        Self {
            canonical,
            distilled,
            problem,
            exact_seed,
            trace_len,
            arm,
        }
    }

    fn evaluate(
        &self,
        ordinal: usize,
        genome: &BackwardGenome,
    ) -> Result<(BackwardScore, Option<CertifiedBackwardCandidate>), BackwardSearchError> {
        match self.evaluate_candidate(ordinal, genome) {
            Ok(Some(candidate)) => Ok((candidate.score, Some(candidate))),
            Ok(None) => Ok((infeasible_score(ordinal), None)),
            Err(error) if candidate_infeasible(&error) => Ok((infeasible_score(ordinal), None)),
            Err(error) => Err(error),
        }
    }

    fn evaluate_candidate(
        &self,
        ordinal: usize,
        genome: &BackwardGenome,
    ) -> Result<Option<CertifiedBackwardCandidate>, BackwardSearchError> {
        let stable_order = decode_fragment_order(self.problem, genome)?;
        let original_indices = self
            .problem
            .selected_order
            .iter()
            .cloned()
            .zip(self.problem.selected_order_indices.iter().copied())
            .collect::<BTreeMap<_, _>>();
        let order = stable_order
            .iter()
            .map(|fragment| {
                original_indices.get(fragment).copied().ok_or(
                    BackwardSearchError::InvalidGenomeDomain {
                        gene: "fragment order key",
                    },
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let candidate_problem = build_problem_for_order(
            self.canonical,
            self.distilled,
            &order,
            self.trace_len,
            self.problem.budget_cells,
            self.problem.stream_reductions,
        )?;
        let paging = match self.arm {
            BackwardSearchArm::OrderOnly => {
                match solve_exact_paging(&candidate_problem.demands, MAX_PAGER_STATES)? {
                    PagerOutcome::Solved(paging) => paging,
                    PagerOutcome::SolverCapped { .. } => return Ok(None),
                }
            }
            BackwardSearchArm::CacheOnly | BackwardSearchArm::Joint => {
                decode_cache_plan(&candidate_problem, genome)?
            }
        };
        compile_and_certify_paging(self.distilled, &candidate_problem, &paging, ordinal).map(Some)
    }
}

#[derive(Clone, Copy)]
pub struct BackwardGuidedTrial;

impl SearchAdapter for BackwardAdapter<'_> {
    type Genome = BackwardGenome;
    type Score = BackwardScore;
    type Evaluation = Option<CertifiedBackwardCandidate>;
    type Error = BackwardSearchError;
    type GuidedTrial = BackwardGuidedTrial;

    fn seeds(&self) -> Result<Vec<Self::Genome>, Self::Error> {
        match self.arm {
            BackwardSearchArm::OrderOnly => Ok(vec![BackwardGenome::constructive(self.problem)]),
            BackwardSearchArm::CacheOnly | BackwardSearchArm::Joint => {
                Ok(vec![paging_seed(self.problem, self.exact_seed)?])
            }
        }
    }

    fn parent_eligible(&self, score: &Self::Score) -> bool {
        !score.infeasible
    }

    fn population_fill_seed(
        &self,
        seeds: &[Self::Genome],
        seed_scores: &[Self::Score],
        _population_len: usize,
    ) -> Self::Genome {
        seed_scores
            .iter()
            .position(|score| !score.infeasible)
            .and_then(|index| seeds.get(index))
            .unwrap_or(&seeds[0])
            .clone()
    }

    fn mutate(&self, genome: &mut Self::Genome, rng: &mut StableRng) {
        mutate_genome(self.problem, self.arm, genome, rng);
    }

    fn score_batch(
        &self,
        candidates: &[(usize, Self::Genome)],
    ) -> Vec<Result<(Self::Score, Self::Evaluation), Self::Error>> {
        candidates
            .par_iter()
            .map(|(ordinal, genome)| self.evaluate(*ordinal, genome))
            .collect()
    }

    fn guided_trials(
        &self,
        _pre_guided_best: &Self::Genome,
        pre_guided_evaluation: &Self::Evaluation,
    ) -> Vec<Self::GuidedTrial> {
        pre_guided_evaluation
            .as_ref()
            .map(|_| vec![BackwardGuidedTrial])
            .unwrap_or_default()
    }

    fn apply_guided_trial(
        &self,
        _trial: &Self::GuidedTrial,
        live_best: &Self::Genome,
        _live_evaluation: &Self::Evaluation,
    ) -> Self::Genome {
        let mut guided = live_best.clone();
        guided.fragment_order_key = BackwardGenome::constructive(self.problem).fragment_order_key;
        guided
    }
}

fn decode_cache_plan(
    problem: &BackwardSearchProblem,
    genome: &BackwardGenome,
) -> Result<ExactPagingPlan, BackwardSearchError> {
    validate_domain(
        &problem.leaf_domain,
        &genome.leaf_cache_priority,
        "leaf cache priority",
    )?;
    let mut residents = BTreeMap::<ExprId, u8>::new();
    let mut live_lanes = 0u8;
    let mut actions = Vec::with_capacity(problem.demands.len());
    let mut live_lanes_after = Vec::with_capacity(problem.demands.len());
    let mut objective = PagingObjective::default();
    let mut predicted_misses = 0u32;
    let mut refused_retains = 0u32;
    let mut peak_live_lanes = 0u8;

    for (position, demand) in problem.demands.iter().enumerate() {
        let hit = residents.remove(&demand.expr).is_some();
        if hit {
            live_lanes = live_lanes
                .checked_sub(demand.width_lanes)
                .ok_or(BackwardSearchError::CostOverflow)?;
            objective.evictions = increment(objective.evictions)?;
        } else {
            objective.dram_bytes = objective
                .dram_bytes
                .checked_add(demand.miss_cost.dram_bytes()?)
                .ok_or(BackwardSearchError::CostOverflow)?;
            objective.primitive_source_ops = objective
                .primitive_source_ops
                .checked_add(demand.miss_cost.ops.primitive_equivalents()?)
                .ok_or(BackwardSearchError::CostOverflow)?;
            predicted_misses = increment(predicted_misses)?;
        }

        let priority = genome.leaf_cache_priority[&demand.key];
        if !priority.is_finite() {
            return Err(BackwardSearchError::NonFiniteGenomeValue {
                gene: "leaf cache priority",
            });
        }
        let action = if priority > 0.0 {
            let retained_lanes = live_lanes
                .checked_add(demand.width_lanes)
                .ok_or(BackwardSearchError::CostOverflow)?;
            if !demand.has_next || retained_lanes > demand.gap_capacity_lanes {
                return Err(BackwardSearchError::CacheGenomeInfeasible {
                    demand_position: position,
                });
            }
            residents.insert(demand.expr, demand.width_lanes);
            live_lanes = retained_lanes;
            objective.admissions = increment(objective.admissions)?;
            peak_live_lanes = peak_live_lanes.max(live_lanes);
            PagingAction::Retain
        } else {
            let retain_fits = demand.has_next
                && live_lanes
                    .checked_add(demand.width_lanes)
                    .ok_or(BackwardSearchError::CostOverflow)?
                    <= demand.gap_capacity_lanes;
            if demand.has_next && !retain_fits {
                refused_retains = increment(refused_retains)?;
            }
            if live_lanes > demand.gap_capacity_lanes {
                return Err(BackwardSearchError::CacheGenomeInfeasible {
                    demand_position: position,
                });
            }
            PagingAction::Bypass
        };
        actions.push(action);
        live_lanes_after.push(live_lanes);
    }

    Ok(ExactPagingPlan {
        actions,
        live_lanes_after,
        objective,
        predicted_misses,
        refused_retains,
        telemetry: PagingTelemetry {
            peak_live_states: usize::from(!problem.demands.is_empty()),
            generated_states: problem
                .demands
                .len()
                .try_into()
                .map_err(|_| BackwardSearchError::CostOverflow)?,
            merged_states: 0,
            peak_live_lanes,
        },
    })
}

fn validate_domain<K: Ord>(
    expected: &[K],
    actual: &BTreeMap<K, f64>,
    gene: &'static str,
) -> Result<(), BackwardSearchError> {
    if expected.len() != actual.len() || expected.iter().any(|key| !actual.contains_key(key)) {
        return Err(BackwardSearchError::InvalidGenomeDomain { gene });
    }
    Ok(())
}

fn ordered_f64_bits(value: f64) -> u64 {
    let bits = value.to_bits();
    if bits >> 63 == 0 {
        bits ^ (1 << 63)
    } else {
        !bits
    }
}

fn mutate_order(problem: &BackwardSearchProblem, genome: &mut BackwardGenome, rng: &mut StableRng) {
    if problem.fragment_domain.len() < 2 {
        return;
    }
    let first = rng.index(problem.fragment_domain.len());
    let mut second = rng.index(problem.fragment_domain.len() - 1);
    if second >= first {
        second += 1;
    }
    let first_key = &problem.fragment_domain[first];
    let second_key = &problem.fragment_domain[second];
    let Some(first_value) = genome.fragment_order_key.get(first_key).copied() else {
        return;
    };
    let Some(second_value) = genome.fragment_order_key.get(second_key).copied() else {
        return;
    };
    genome
        .fragment_order_key
        .insert(first_key.clone(), second_value);
    genome
        .fragment_order_key
        .insert(second_key.clone(), first_value);
}

fn mutate_cache(problem: &BackwardSearchProblem, genome: &mut BackwardGenome, rng: &mut StableRng) {
    if problem.leaf_domain.is_empty() {
        return;
    }
    let key = &problem.leaf_domain[rng.index(problem.leaf_domain.len())];
    if let Some(priority) = genome.leaf_cache_priority.get_mut(key) {
        *priority = -*priority;
    }
}

fn increment(value: u32) -> Result<u32, BackwardSearchError> {
    value
        .checked_add(1)
        .ok_or(BackwardSearchError::CostOverflow)
}

fn candidate_infeasible(error: &BackwardSearchError) -> bool {
    matches!(
        error,
        BackwardSearchError::CacheGenomeInfeasible { .. }
            | BackwardSearchError::PlacementIntegrationFailure
            | BackwardSearchError::BackwardEvaluation(
                crate::eval_plan::backward::BackwardEvaluationError::Concrete(
                    crate::eval_plan::ConcreteBindError::PlacementFailed { .. }
                )
            )
    )
}

fn infeasible_score(ordinal: usize) -> BackwardScore {
    BackwardScore {
        infeasible: true,
        whole_pass_dram_bytes: u128::MAX,
        primitive_source_ops: u128::MAX,
        instructions: usize::MAX,
        encoded_lanes: usize::MAX,
        arithmetic_ops: usize::MAX,
        ordinal,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup,
        RootId, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
    };
    use rayon::ThreadPoolBuilder;

    use crate::bwd::distill::{DistilledLayer, distill};
    use crate::eval_plan::backward_search::pager::{
        ExactPagingPlan, PagerOutcome, PagingAction, solve_exact_paging,
    };
    use crate::eval_plan::backward_search::problem::{
        BackwardSearchProblem, build_backward_search_problem,
    };
    use crate::eval_plan::backward_search::{BackwardSearchError, MAX_PAGER_STATES};
    use crate::eval_plan::search_driver::{SearchAdapter, StableRng};

    use super::{
        BackwardAdapter, BackwardGenome, BackwardSearchArm, decode_cache_actions,
        decode_fragment_order, mutate_genome, paging_seed,
    };

    #[test]
    fn fragment_keys_decode_to_a_total_deterministic_order() {
        let fixture = synthetic_solved_problem();
        let genome = BackwardGenome::constructive(&fixture.problem);
        assert_eq!(
            decode_fragment_order(&fixture.problem, &genome).unwrap(),
            fixture.problem.constructive_order
        );
    }

    #[test]
    fn exact_paging_seed_round_trips_action_stream_byte_for_byte() {
        let fixture = synthetic_solved_problem();
        let genome = paging_seed(&fixture.problem, &fixture.exact).unwrap();
        assert_eq!(
            decode_cache_actions(&fixture.problem, &genome).unwrap(),
            fixture.exact.actions
        );
    }

    #[test]
    fn malformed_paging_seed_reports_seed_mismatch() {
        let fixture = synthetic_solved_problem();
        let mut malformed = fixture.exact.clone();
        let terminal = fixture
            .problem
            .demands
            .iter()
            .position(|demand| !demand.has_next)
            .expect("synthetic problem has a terminal leaf demand");
        malformed.actions[terminal] = PagingAction::Retain;
        assert_eq!(
            paging_seed(&fixture.problem, &malformed),
            Err(BackwardSearchError::PagingSeedMismatch)
        );
    }

    #[test]
    fn order_only_mutation_never_changes_cache_priorities() {
        let fixture = synthetic_solved_problem();
        let mut genome = BackwardGenome::constructive(&fixture.problem);
        let before = genome.leaf_cache_priority.clone();
        mutate_genome(
            &fixture.problem,
            BackwardSearchArm::OrderOnly,
            &mut genome,
            &mut StableRng::new(7),
        );
        assert_eq!(genome.leaf_cache_priority, before);
    }

    #[test]
    fn genomes_have_no_nonleaf_staging_or_materialization_domain() {
        let fixture = synthetic_solved_problem();
        let genome = BackwardGenome::constructive(&fixture.problem);
        assert_eq!(
            genome.fragment_order_key.len(),
            fixture.problem.fragment_domain.len()
        );
        assert_eq!(
            genome.leaf_cache_priority.len(),
            fixture.problem.leaf_domain.len()
        );
    }

    #[test]
    fn requested_retain_that_does_not_fit_is_candidate_infeasible() {
        let fixture = synthetic_solved_problem();
        let mut genome = BackwardGenome::constructive(&fixture.problem);
        let terminal = fixture
            .problem
            .demands
            .iter()
            .find(|demand| !demand.has_next)
            .expect("synthetic problem has a terminal leaf demand");
        genome.leaf_cache_priority.insert(terminal.key.clone(), 1.0);
        assert!(matches!(
            decode_cache_actions(&fixture.problem, &genome),
            Err(BackwardSearchError::CacheGenomeInfeasible { .. })
        ));
    }

    #[test]
    fn adapter_scores_capacity_failure_as_candidate_infeasibility() {
        let fixture = synthetic_solved_problem();
        let mut genome = BackwardGenome::constructive(&fixture.problem);
        let terminal = fixture
            .problem
            .demands
            .iter()
            .find(|demand| !demand.has_next)
            .expect("synthetic problem has a terminal leaf demand");
        genome.leaf_cache_priority.insert(terminal.key.clone(), 1.0);
        let adapter = BackwardAdapter::new(
            &fixture.layer,
            &fixture.distilled,
            &fixture.problem,
            &fixture.exact,
            8,
            BackwardSearchArm::CacheOnly,
        );
        let (score, evaluation) = adapter.score_batch(&[(5, genome)]).pop().unwrap().unwrap();
        assert!(score.infeasible);
        assert_eq!(score.ordinal, 5);
        assert!(evaluation.is_none());
    }

    #[test]
    fn adapter_rebuilds_the_real_trace_for_the_decoded_order() {
        let fixture = synthetic_solved_problem();
        let constructive = BackwardGenome::constructive(&fixture.problem);
        let mut reversed = constructive.clone();
        let order = &fixture.problem.constructive_order;
        let first = order.first().unwrap();
        let last = order.last().unwrap();
        let first_value = reversed.fragment_order_key[first];
        let last_value = reversed.fragment_order_key[last];
        reversed
            .fragment_order_key
            .insert(first.clone(), last_value);
        reversed
            .fragment_order_key
            .insert(last.clone(), first_value);
        let adapter = BackwardAdapter::new(
            &fixture.layer,
            &fixture.distilled,
            &fixture.problem,
            &fixture.exact,
            8,
            BackwardSearchArm::OrderOnly,
        );

        let mut evaluations = adapter.score_batch(&[(0, constructive), (1, reversed)]);
        let (_, reversed) = evaluations.pop().unwrap().unwrap();
        let (_, constructive) = evaluations.pop().unwrap().unwrap();
        let reversed = reversed.expect("reversed order is feasible");
        let constructive = constructive.expect("constructive order is feasible");
        assert_ne!(
            constructive.occurrence_plan.entries,
            reversed.occurrence_plan.entries
        );
    }

    #[test]
    fn rayon_batch_evaluation_is_exact_across_one_and_four_threads() {
        let fixture = synthetic_solved_problem();
        let genome = paging_seed(&fixture.problem, &fixture.exact).unwrap();
        let adapter = BackwardAdapter::new(
            &fixture.layer,
            &fixture.distilled,
            &fixture.problem,
            &fixture.exact,
            8,
            BackwardSearchArm::Joint,
        );

        let evaluate = |threads| {
            ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap()
                .install(|| {
                    adapter
                        .score_batch(&[(17, genome.clone())])
                        .pop()
                        .unwrap()
                        .unwrap()
                })
        };
        let (one_score, one) = evaluate(1);
        let (four_score, four) = evaluate(4);
        let one = one.expect("exact seed is feasible");
        let four = four.expect("exact seed is feasible");

        assert_eq!(one.paging.actions, four.paging.actions);
        assert_eq!(one.occurrence_plan.entries, four.occurrence_plan.entries);
        assert_eq!(one.compiled.encoded, four.compiled.encoded);
        assert_eq!(one.certificate, four.certificate);
        assert_eq!(one_score, four_score);
        assert_eq!(one.paging.telemetry, four.paging.telemetry);
    }

    struct SyntheticFixture {
        layer: DagLayer,
        distilled: DistilledLayer,
        problem: BackwardSearchProblem,
        exact: ExactPagingPlan,
    }

    fn synthetic_solved_problem() -> SyntheticFixture {
        let layer = synthetic_two_shared_sources_layer();
        let distilled = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
        let (_, problem) = build_backward_search_problem(&layer, &distilled, 8, 4).unwrap();
        let problem = problem.expect("synthetic two-shared-source problem");
        let exact = match solve_exact_paging(&problem.demands, MAX_PAGER_STATES).unwrap() {
            PagerOutcome::Solved(exact) => exact,
            outcome => panic!("expected solved paging problem, got {outcome:?}"),
        };
        SyntheticFixture {
            layer,
            distilled,
            problem,
            exact,
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
