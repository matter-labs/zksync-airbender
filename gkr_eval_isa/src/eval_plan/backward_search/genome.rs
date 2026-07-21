use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use cs::gkr_compiler::dag_ir::DagLayer;
use rayon::prelude::*;

use crate::bwd::distill::DistilledLayer;
use crate::eval_plan::search_driver::{SearchAdapter, StableRng};

use super::pager::{
    ExactPagingPlan, PagerOutcome, PagingAction, reconstruct_paging_plan, solve_exact_paging,
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

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct BackwardAdapterTelemetrySnapshot {
    pub evaluation_attempts: usize,
    pub pager_calls: usize,
    pub pager_generated_states: u64,
    pub pager_merged_states: u64,
    pub pager_peak_states: usize,
    pub compile_time: Duration,
}

#[derive(Debug, Default)]
pub(crate) struct BackwardAdapterTelemetry {
    evaluation_attempts: AtomicUsize,
    pager_calls: AtomicUsize,
    pager_generated_states: AtomicU64,
    pager_merged_states: AtomicU64,
    pager_peak_states: AtomicUsize,
    compile_nanos: AtomicU64,
}

impl BackwardAdapterTelemetry {
    pub(crate) fn record_evaluation_attempts(&self, count: usize) {
        self.evaluation_attempts.fetch_add(count, Ordering::Relaxed);
    }

    pub(crate) fn record_pager_call(&self) {
        self.pager_calls.fetch_add(1, Ordering::Relaxed);
    }

    pub(crate) fn record_pager_outcome(&self, outcome: &PagerOutcome) {
        match outcome {
            PagerOutcome::Solved(plan) => {
                self.pager_generated_states
                    .fetch_add(plan.telemetry.generated_states, Ordering::Relaxed);
                self.pager_merged_states
                    .fetch_add(plan.telemetry.merged_states, Ordering::Relaxed);
                self.pager_peak_states
                    .fetch_max(plan.telemetry.peak_live_states, Ordering::Relaxed);
            }
            PagerOutcome::SolverCapped {
                peak_states,
                generated_states,
                merged_states,
                ..
            } => {
                self.pager_generated_states
                    .fetch_add(*generated_states, Ordering::Relaxed);
                self.pager_merged_states
                    .fetch_add(*merged_states, Ordering::Relaxed);
                self.pager_peak_states
                    .fetch_max(*peak_states, Ordering::Relaxed);
            }
        }
    }

    pub(crate) fn record_compile_time(&self, elapsed: Duration) {
        let nanos = u64::try_from(elapsed.as_nanos()).unwrap_or(u64::MAX);
        self.compile_nanos.fetch_add(nanos, Ordering::Relaxed);
    }

    pub(crate) fn snapshot(&self) -> BackwardAdapterTelemetrySnapshot {
        BackwardAdapterTelemetrySnapshot {
            evaluation_attempts: self.evaluation_attempts.load(Ordering::Relaxed),
            pager_calls: self.pager_calls.load(Ordering::Relaxed),
            pager_generated_states: self.pager_generated_states.load(Ordering::Relaxed),
            pager_merged_states: self.pager_merged_states.load(Ordering::Relaxed),
            pager_peak_states: self.pager_peak_states.load(Ordering::Relaxed),
            compile_time: Duration::from_nanos(self.compile_nanos.load(Ordering::Relaxed)),
        }
    }
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

fn decode_cache_action_vector(
    problem: &BackwardSearchProblem,
    genome: &BackwardGenome,
) -> Result<Vec<PagingAction>, BackwardSearchError> {
    validate_domain(
        &problem.leaf_domain,
        &genome.leaf_cache_priority,
        "leaf cache priority",
    )?;
    problem
        .demands
        .iter()
        .map(|demand| {
            let priority = genome.leaf_cache_priority[&demand.key];
            if !priority.is_finite() {
                return Err(BackwardSearchError::NonFiniteGenomeValue {
                    gene: "leaf cache priority",
                });
            }
            Ok(if priority > 0.0 {
                PagingAction::Retain
            } else {
                PagingAction::Bypass
            })
        })
        .collect()
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

enum CandidateProblem<'a> {
    Reused(&'a BackwardSearchProblem),
    Rebuilt(BackwardSearchProblem),
}

impl AsRef<BackwardSearchProblem> for CandidateProblem<'_> {
    fn as_ref(&self) -> &BackwardSearchProblem {
        match self {
            Self::Reused(problem) => problem,
            Self::Rebuilt(problem) => problem,
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
    pager_cap: usize,
    telemetry: Option<&'a BackwardAdapterTelemetry>,
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
            pager_cap: MAX_PAGER_STATES,
            telemetry: None,
        }
    }

    pub(crate) fn with_pager_cap(mut self, pager_cap: usize) -> Self {
        self.pager_cap = pager_cap;
        self
    }

    pub(crate) fn with_telemetry(mut self, telemetry: &'a BackwardAdapterTelemetry) -> Self {
        self.telemetry = Some(telemetry);
        self
    }

    fn evaluate(
        &self,
        ordinal: usize,
        genome: &BackwardGenome,
    ) -> Result<(BackwardScore, Option<CertifiedBackwardCandidate>), BackwardSearchError> {
        match self.evaluate_candidate(ordinal, genome) {
            Ok(Some(candidate)) => Ok((candidate.score, Some(candidate))),
            Ok(None) => Ok((infeasible_score(ordinal), None)),
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
        let candidate_problem = match self.candidate_problem_for_order(&order) {
            Ok(problem) => problem,
            Err(error) if pre_paging_candidate_infeasible(&error) => return Ok(None),
            Err(error) => return Err(error),
        };
        self.evaluate_candidate_against(ordinal, genome, candidate_problem.as_ref())
    }

    fn candidate_problem_for_order(
        &self,
        order: &[usize],
    ) -> Result<CandidateProblem<'_>, BackwardSearchError> {
        if order == self.problem.selected_order_indices {
            Ok(CandidateProblem::Reused(self.problem))
        } else {
            build_problem_for_order(
                self.canonical,
                self.distilled,
                order,
                self.trace_len,
                self.problem.budget_cells,
                self.problem.stream_reductions,
            )
            .map(CandidateProblem::Rebuilt)
        }
    }

    fn evaluate_candidate_against(
        &self,
        ordinal: usize,
        genome: &BackwardGenome,
        candidate_problem: &BackwardSearchProblem,
    ) -> Result<Option<CertifiedBackwardCandidate>, BackwardSearchError> {
        let paging = match self.arm {
            BackwardSearchArm::OrderOnly => {
                if let Some(telemetry) = self.telemetry {
                    telemetry.record_pager_call();
                }
                let outcome = solve_exact_paging(&candidate_problem.demands, self.pager_cap)?;
                if let Some(telemetry) = self.telemetry {
                    telemetry.record_pager_outcome(&outcome);
                }
                exact_paging_plan(outcome)?
            }
            BackwardSearchArm::CacheOnly | BackwardSearchArm::Joint => {
                match decode_cache_plan(candidate_problem, genome) {
                    Ok(paging) => paging,
                    Err(BackwardSearchError::CacheGenomeInfeasible { .. }) => return Ok(None),
                    Err(error) => return Err(error),
                }
            }
        };
        let started = Instant::now();
        let result = preserve_certification_result(compile_and_certify_paging(
            self.distilled,
            candidate_problem,
            &paging,
            ordinal,
        ));
        if let Some(telemetry) = self.telemetry {
            telemetry.record_compile_time(started.elapsed());
        }
        result
    }
}

impl SearchAdapter for BackwardAdapter<'_> {
    type Genome = BackwardGenome;
    type Score = BackwardScore;
    type Evaluation = Option<CertifiedBackwardCandidate>;
    type Error = BackwardSearchError;
    type GuidedTrial = ();

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
        if let Some(telemetry) = self.telemetry {
            telemetry.record_evaluation_attempts(candidates.len());
        }
        candidates
            .par_iter()
            .map(|(ordinal, genome)| self.evaluate(*ordinal, genome))
            .collect()
    }

    fn guided_trials(
        &self,
        _pre_guided_best: &Self::Genome,
        _pre_guided_evaluation: &Self::Evaluation,
    ) -> Vec<Self::GuidedTrial> {
        Vec::new()
    }

    fn apply_guided_trial(
        &self,
        _trial: &Self::GuidedTrial,
        live_best: &Self::Genome,
        _live_evaluation: &Self::Evaluation,
    ) -> Self::Genome {
        live_best.clone()
    }
}

fn exact_paging_plan(outcome: PagerOutcome) -> Result<ExactPagingPlan, BackwardSearchError> {
    match outcome {
        PagerOutcome::Solved(paging) => Ok(paging),
        PagerOutcome::SolverCapped {
            cap,
            demand_position,
            peak_states,
            generated_states,
            merged_states,
        } => Err(BackwardSearchError::ExactPagerSolverCapped {
            cap,
            demand_position,
            peak_states,
            generated_states,
            merged_states,
        }),
    }
}

fn preserve_certification_result(
    result: Result<CertifiedBackwardCandidate, BackwardSearchError>,
) -> Result<Option<CertifiedBackwardCandidate>, BackwardSearchError> {
    result.map(Some)
}

fn decode_cache_plan(
    problem: &BackwardSearchProblem,
    genome: &BackwardGenome,
) -> Result<ExactPagingPlan, BackwardSearchError> {
    let actions = decode_cache_action_vector(problem, genome)?;
    match reconstruct_paging_plan(&problem.demands, &actions) {
        Ok(plan) => Ok(plan),
        Err(
            BackwardSearchError::IllegalPagingRetain { demand_position }
            | BackwardSearchError::PagingLiveSetOverCapacity { demand_position },
        ) => Err(BackwardSearchError::CacheGenomeInfeasible { demand_position }),
        Err(error) => Err(error),
    }
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

fn pre_paging_candidate_infeasible(error: &BackwardSearchError) -> bool {
    matches!(
        error,
        BackwardSearchError::BackwardEvaluation(
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
        ExactPagingPlan, PagerOutcome, PagingAction, reconstruct_paging_plan, solve_exact_paging,
    };
    use crate::eval_plan::backward_search::problem::{
        BackwardSearchProblem, build_backward_search_problem, build_problem_for_order,
    };
    use crate::eval_plan::backward_search::{BackwardSearchError, MAX_PAGER_STATES, SourceCost};
    use crate::eval_plan::search_driver::{SearchAdapter, StableRng};

    use super::{
        BackwardAdapter, BackwardGenome, BackwardSearchArm, CandidateProblem,
        decode_cache_action_vector, decode_cache_actions, decode_cache_plan, decode_fragment_order,
        exact_paging_plan, mutate_genome, paging_seed, preserve_certification_result,
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
    fn decoded_genome_actions_match_reconstructed_paging_observables() {
        let fixture = synthetic_solved_problem();
        let genome = paging_seed(&fixture.problem, &fixture.exact).unwrap();
        let actions = decode_cache_actions(&fixture.problem, &genome).unwrap();
        let decoded = decode_cache_plan(&fixture.problem, &genome).unwrap();
        let rebuilt = reconstruct_paging_plan(&fixture.problem.demands, &actions).unwrap();
        assert_eq!(decoded.actions, rebuilt.actions);
        assert_eq!(decoded.live_lanes_after, rebuilt.live_lanes_after);
        assert_eq!(decoded.objective, rebuilt.objective);
        assert_eq!(decoded.predicted_misses, rebuilt.predicted_misses);
        assert_eq!(decoded.refused_retains, rebuilt.refused_retains);
    }

    #[test]
    fn cache_genome_maps_reconstructed_live_set_over_capacity() {
        let fixture = synthetic_solved_problem();
        let mut problem = fixture.problem.clone();
        let mut retained = problem.demands[0].clone();
        retained.expr = ExprId(0);
        retained.width_lanes = 1;
        retained.gap_capacity_lanes = 1;
        retained.has_next = true;
        let mut bypass = retained.clone();
        bypass.key.occurrence_in_fragment = retained.key.occurrence_in_fragment + 1;
        bypass.expr = ExprId(1);
        bypass.gap_capacity_lanes = 0;
        bypass.has_next = false;
        problem.demands = vec![retained.clone(), bypass];
        problem.leaf_domain = vec![retained.key.clone(), problem.demands[1].key.clone()];
        let mut genome = BackwardGenome::constructive(&problem);
        genome.leaf_cache_priority.insert(retained.key.clone(), 1.0);

        let actions = decode_cache_action_vector(&problem, &genome).unwrap();
        assert_eq!(
            reconstruct_paging_plan(&problem.demands, &actions),
            Err(BackwardSearchError::PagingLiveSetOverCapacity { demand_position: 1 })
        );
        assert_eq!(
            decode_cache_actions(&problem, &genome),
            Err(BackwardSearchError::CacheGenomeInfeasible { demand_position: 1 })
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
    fn missing_and_extra_gene_keys_are_rejected() {
        let fixture = synthetic_solved_problem();
        let genome = BackwardGenome::constructive(&fixture.problem);

        let mut missing_fragment = genome.clone();
        missing_fragment
            .fragment_order_key
            .remove(&fixture.problem.fragment_domain[0]);
        assert!(matches!(
            decode_fragment_order(&fixture.problem, &missing_fragment),
            Err(BackwardSearchError::InvalidGenomeDomain {
                gene: "fragment order key"
            })
        ));

        let mut extra_fragment = genome.clone();
        let mut extra_fragment_key = fixture.problem.fragment_domain[0].clone();
        extra_fragment_key.recipe.push(Vec::new());
        extra_fragment
            .fragment_order_key
            .insert(extra_fragment_key, 99.0);
        assert!(matches!(
            decode_fragment_order(&fixture.problem, &extra_fragment),
            Err(BackwardSearchError::InvalidGenomeDomain {
                gene: "fragment order key"
            })
        ));

        let mut missing_leaf = genome.clone();
        missing_leaf
            .leaf_cache_priority
            .remove(&fixture.problem.leaf_domain[0]);
        assert!(matches!(
            decode_cache_actions(&fixture.problem, &missing_leaf),
            Err(BackwardSearchError::InvalidGenomeDomain {
                gene: "leaf cache priority"
            })
        ));

        let mut extra_leaf = genome;
        let mut extra_leaf_key = fixture.problem.leaf_domain[0].clone();
        extra_leaf_key.occurrence_in_fragment = u32::MAX;
        extra_leaf.leaf_cache_priority.insert(extra_leaf_key, -1.0);
        assert!(matches!(
            decode_cache_actions(&fixture.problem, &extra_leaf),
            Err(BackwardSearchError::InvalidGenomeDomain {
                gene: "leaf cache priority"
            })
        ));
    }

    #[test]
    fn non_finite_gene_values_are_rejected() {
        let fixture = synthetic_solved_problem();
        for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            let mut genome = BackwardGenome::constructive(&fixture.problem);
            genome
                .fragment_order_key
                .insert(fixture.problem.fragment_domain[0].clone(), value);
            assert!(matches!(
                decode_fragment_order(&fixture.problem, &genome),
                Err(BackwardSearchError::NonFiniteGenomeValue {
                    gene: "fragment order key"
                })
            ));

            let mut genome = BackwardGenome::constructive(&fixture.problem);
            genome
                .leaf_cache_priority
                .insert(fixture.problem.leaf_domain[0].clone(), value);
            assert!(matches!(
                decode_cache_actions(&fixture.problem, &genome),
                Err(BackwardSearchError::NonFiniteGenomeValue {
                    gene: "leaf cache priority"
                })
            ));
        }
    }

    #[test]
    fn zero_and_one_element_mutations_are_safe_and_consume_stable_rng() {
        let fixture = synthetic_solved_problem();
        let mut empty = fixture.problem.clone();
        empty.fragment_domain.clear();
        empty.constructive_order.clear();
        empty.leaf_domain.clear();
        for arm in [BackwardSearchArm::OrderOnly, BackwardSearchArm::CacheOnly] {
            let mut genome = BackwardGenome::constructive(&empty);
            let mut actual = StableRng::new(23);
            mutate_genome(&empty, arm, &mut genome, &mut actual);
            let mut expected = StableRng::new(23);
            assert_eq!(actual.next_u64(), expected.next_u64());
        }
        let mut joint_genome = BackwardGenome::constructive(&empty);
        let mut actual = StableRng::new(23);
        mutate_genome(
            &empty,
            BackwardSearchArm::Joint,
            &mut joint_genome,
            &mut actual,
        );
        let mut expected = StableRng::new(23);
        expected.next_u64();
        assert_eq!(actual.next_u64(), expected.next_u64());

        let mut singleton_order = fixture.problem.clone();
        singleton_order.fragment_domain.truncate(1);
        singleton_order.constructive_order.truncate(1);
        let mut genome = BackwardGenome::constructive(&singleton_order);
        let mut actual = StableRng::new(41);
        mutate_genome(
            &singleton_order,
            BackwardSearchArm::OrderOnly,
            &mut genome,
            &mut actual,
        );
        let mut expected = StableRng::new(41);
        assert_eq!(actual.next_u64(), expected.next_u64());

        let mut singleton_cache = fixture.problem.clone();
        singleton_cache.leaf_domain.truncate(1);
        let mut genome = BackwardGenome::constructive(&singleton_cache);
        let key = singleton_cache.leaf_domain[0].clone();
        let mut actual = StableRng::new(41);
        mutate_genome(
            &singleton_cache,
            BackwardSearchArm::CacheOnly,
            &mut genome,
            &mut actual,
        );
        let mut expected = StableRng::new(41);
        expected.next_u64();
        assert_eq!(actual.next_u64(), expected.next_u64());
        assert_eq!(genome.leaf_cache_priority[&key], 1.0);
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
    fn exact_pager_cap_is_a_typed_adapter_error() {
        assert_eq!(
            exact_paging_plan(PagerOutcome::SolverCapped {
                cap: 12,
                demand_position: 7,
                peak_states: 13,
                generated_states: 21,
                merged_states: 3,
            }),
            Err(BackwardSearchError::ExactPagerSolverCapped {
                cap: 12,
                demand_position: 7,
                peak_states: 13,
                generated_states: 21,
                merged_states: 3,
            })
        );
    }

    #[test]
    fn task4_placement_and_certificate_errors_propagate_unchanged() {
        let errors = [
            BackwardSearchError::PlacementIntegrationFailure,
            BackwardSearchError::PagingReplayDiverged { at_entry: 1 },
            BackwardSearchError::PagingReplayIncomplete { at_entry: 2 },
            BackwardSearchError::PagingReplayRefused { count: 3 },
            BackwardSearchError::PagingSourceAccessMismatch {
                predicted_reads: 4,
                realized_reads: 5,
                predicted_width_lanes: 6,
                realized_width_lanes: 7,
            },
            BackwardSearchError::PagingReadCostMismatch {
                predicted: SourceCost::default(),
                realized: SourceCost {
                    plain_read_bytes: 1,
                    ..SourceCost::default()
                },
            },
            BackwardSearchError::PagingWriteCostMismatch {
                predicted: SourceCost::default(),
                realized: SourceCost {
                    materialization_write_bytes: 1,
                    ..SourceCost::default()
                },
            },
            BackwardSearchError::PagingOccupancyMismatch {
                position: 8,
                predicted: 9,
                realized: 10,
            },
            BackwardSearchError::PagingCertificateMismatch {
                observable: "test certificate",
            },
        ];
        for error in errors {
            let expected = format!("{error:?}");
            match preserve_certification_result(Err(error)) {
                Err(actual) => assert_eq!(format!("{actual:?}"), expected),
                Ok(_) => panic!("Task 4 error became a scored evaluation"),
            }
        }
    }

    #[test]
    fn backward_adapter_has_no_guided_trials_for_any_arm() {
        let fixture = synthetic_solved_problem();
        for arm in [
            BackwardSearchArm::OrderOnly,
            BackwardSearchArm::CacheOnly,
            BackwardSearchArm::Joint,
        ] {
            let adapter = BackwardAdapter::new(
                &fixture.layer,
                &fixture.distilled,
                &fixture.problem,
                &fixture.exact,
                8,
                arm,
            );
            let genome = BackwardGenome::constructive(&fixture.problem);
            assert!(adapter.guided_trials(&genome, &None).is_empty());
        }
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
    fn unchanged_order_reuse_is_exactly_equivalent_to_rebuild() {
        let fixture = synthetic_solved_problem();
        let genome = paging_seed(&fixture.problem, &fixture.exact).unwrap();
        let adapter = BackwardAdapter::new(
            &fixture.layer,
            &fixture.distilled,
            &fixture.problem,
            &fixture.exact,
            8,
            BackwardSearchArm::CacheOnly,
        );
        let stable = decode_fragment_order(&fixture.problem, &genome).unwrap();
        let originals = fixture
            .problem
            .selected_order
            .iter()
            .cloned()
            .zip(fixture.problem.selected_order_indices.iter().copied())
            .collect::<BTreeMap<_, _>>();
        let order = stable
            .iter()
            .map(|fragment| originals[fragment])
            .collect::<Vec<_>>();
        let selected = adapter.candidate_problem_for_order(&order).unwrap();
        assert!(matches!(&selected, CandidateProblem::Reused(_)));
        let reused = adapter
            .evaluate_candidate_against(7, &genome, selected.as_ref())
            .unwrap()
            .expect("constructive reused candidate is feasible");

        let rebuilt = build_problem_for_order(
            &fixture.layer,
            &fixture.distilled,
            &order,
            8,
            fixture.problem.budget_cells,
            fixture.problem.stream_reductions,
        )
        .unwrap();
        let forced = adapter
            .evaluate_candidate_against(7, &genome, &rebuilt)
            .unwrap()
            .expect("constructive rebuilt candidate is feasible");

        assert_eq!(reused.score, forced.score);
        assert_eq!(reused.paging.actions, forced.paging.actions);
        assert_eq!(
            reused.occurrence_plan.entries,
            forced.occurrence_plan.entries
        );
        assert_eq!(reused.certificate, forced.certificate);
        assert_eq!(reused.compiled.encoded, forced.compiled.encoded);
    }

    #[test]
    fn changed_order_uses_the_existing_rebuild_path() {
        let fixture = synthetic_solved_problem();
        let constructive = BackwardGenome::constructive(&fixture.problem);
        let mut reversed = constructive.clone();
        let stable_order = &fixture.problem.constructive_order;
        let first = stable_order.first().unwrap();
        let last = stable_order.last().unwrap();
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
        let stable = decode_fragment_order(&fixture.problem, &reversed).unwrap();
        let originals = fixture
            .problem
            .selected_order
            .iter()
            .cloned()
            .zip(fixture.problem.selected_order_indices.iter().copied())
            .collect::<BTreeMap<_, _>>();
        let order = stable
            .iter()
            .map(|fragment| originals[fragment])
            .collect::<Vec<_>>();

        assert!(matches!(
            adapter.candidate_problem_for_order(&order).unwrap(),
            CandidateProblem::Rebuilt(_)
        ));
        let (_, candidate) = adapter
            .score_batch(&[(11, reversed)])
            .pop()
            .unwrap()
            .unwrap();
        assert!(candidate.is_some());
    }

    #[test]
    fn rayon_batch_slots_are_exact_across_one_and_four_threads() {
        let fixture = synthetic_solved_problem();
        let constructive = paging_seed(&fixture.problem, &fixture.exact).unwrap();
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
        let candidates = vec![(17, constructive), (3, reversed)];

        let evaluate = |threads| {
            ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap()
                .install(|| {
                    adapter
                        .score_batch(&candidates)
                        .into_iter()
                        .map(|result| {
                            let (score, candidate) = result.unwrap();
                            let candidate = candidate.expect("assigned candidate is feasible");
                            (
                                score,
                                candidate.paging.actions,
                                candidate.occurrence_plan.entries,
                                candidate.compiled.encoded,
                                candidate.certificate,
                                candidate.paging.telemetry,
                            )
                        })
                        .collect::<Vec<_>>()
                })
        };
        let one = evaluate(1);
        let four = evaluate(4);
        assert_eq!(
            one.iter().map(|entry| entry.0.ordinal).collect::<Vec<_>>(),
            vec![17, 3]
        );
        assert_eq!(one, four);
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
