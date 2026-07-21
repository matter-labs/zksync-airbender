use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};

use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer};
use rayon::prelude::*;

use crate::bwd::distill::DistilledLayer;
use crate::eval_plan::search_driver::{
    SearchAdapter, SearchDriverConfig, SearchDriverError, SearchDriverOutcome, StableRng,
    run_search_driver,
};

use super::problem::{
    BackwardSearchProblem, StableFragmentKey, build_backward_search_problem,
    build_problem_for_order, decode_order_indices,
};
use super::{
    BackwardScore, BackwardSearchError, CertifiedBackwardCandidate, ProductionPagingSolver,
    SourceCost, compile_and_certify_paging, solve_production_paging,
};

const SEARCH_POPULATION: usize = 32;
const SEARCH_BATCH: usize = 16;
const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductionSearchIdentity {
    pub circuit: String,
    pub layout_fixture: String,
    pub layer: usize,
    pub regime: BwdRegime,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductionOrderGenome {
    pub order: Vec<usize>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProductionSearchTelemetry {
    pub evaluations: usize,
    pub completed_tiers: Vec<usize>,
    pub first_winning_ordinal: Option<usize>,
    pub improvement_ordinals: Vec<usize>,
    pub exact_solver_calls: usize,
    pub solver_kinds: Vec<ProductionPagingSolver>,
    pub peak_dp_states: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProductionSearchProgress {
    pub tier_evaluations: usize,
    pub tier_completed: usize,
    pub evaluations: usize,
    pub solver: Option<ProductionPagingSolver>,
    pub dp_states: usize,
    pub peak_dp_states: usize,
}

pub struct ProductionBackwardPlan {
    pub problem: BackwardSearchProblem,
    pub candidate: CertifiedBackwardCandidate,
    pub order: Vec<usize>,
    pub telemetry: ProductionSearchTelemetry,
}

struct ProductionEvaluation {
    problem: BackwardSearchProblem,
    candidate: CertifiedBackwardCandidate,
}

struct ProductionOrderAdapter<'a> {
    canonical: &'a DagLayer,
    distilled: &'a DistilledLayer,
    problem: &'a BackwardSearchProblem,
    trace_len: usize,
    seeds: &'a [ProductionOrderGenome],
    telemetry: &'a TierTelemetry,
    tier_evaluations: usize,
    evaluation_offset: usize,
    progress: &'a (dyn Fn(ProductionSearchProgress) + Sync),
}

#[derive(Default)]
struct TierTelemetry {
    exact_solver_calls: AtomicUsize,
    solver_mask: AtomicU8,
    last_solver: AtomicU8,
    evaluations: AtomicUsize,
    dp_states: AtomicUsize,
    peak_dp_states: AtomicUsize,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct TierTelemetrySnapshot {
    exact_solver_calls: usize,
    solver_kinds: Vec<ProductionPagingSolver>,
    peak_dp_states: usize,
}

impl TierTelemetry {
    fn record(&self, solver: ProductionPagingSolver, peak_dp_states: usize) {
        self.exact_solver_calls.fetch_add(1, Ordering::Relaxed);
        let bit = match solver {
            ProductionPagingSolver::RetainAll => 1,
            ProductionPagingSolver::UniformIntervals => 2,
            ProductionPagingSolver::ResidentSets => 4,
        };
        self.solver_mask.fetch_or(bit, Ordering::Relaxed);
        self.last_solver.store(bit, Ordering::Relaxed);
        self.dp_states.store(peak_dp_states, Ordering::Relaxed);
        self.peak_dp_states
            .fetch_max(peak_dp_states, Ordering::Relaxed);
    }

    fn progress(&self, tier_evaluations: usize, evaluations: usize) -> ProductionSearchProgress {
        let solver = match self.last_solver.load(Ordering::Relaxed) {
            1 => Some(ProductionPagingSolver::RetainAll),
            2 => Some(ProductionPagingSolver::UniformIntervals),
            4 => Some(ProductionPagingSolver::ResidentSets),
            _ => None,
        };
        ProductionSearchProgress {
            tier_evaluations,
            tier_completed: self.evaluations.load(Ordering::Relaxed),
            evaluations,
            solver,
            dp_states: self.dp_states.load(Ordering::Relaxed),
            peak_dp_states: self.peak_dp_states.load(Ordering::Relaxed),
        }
    }

    fn snapshot(&self) -> TierTelemetrySnapshot {
        let mask = self.solver_mask.load(Ordering::Relaxed);
        let mut solver_kinds = Vec::new();
        if mask & 1 != 0 {
            solver_kinds.push(ProductionPagingSolver::RetainAll);
        }
        if mask & 2 != 0 {
            solver_kinds.push(ProductionPagingSolver::UniformIntervals);
        }
        if mask & 4 != 0 {
            solver_kinds.push(ProductionPagingSolver::ResidentSets);
        }
        TierTelemetrySnapshot {
            exact_solver_calls: self.exact_solver_calls.load(Ordering::Relaxed),
            solver_kinds,
            peak_dp_states: self.peak_dp_states.load(Ordering::Relaxed),
        }
    }
}

impl SearchAdapter for ProductionOrderAdapter<'_> {
    type Genome = ProductionOrderGenome;
    type Score = BackwardScore;
    type Evaluation = ProductionEvaluation;
    type Error = BackwardSearchError;
    type GuidedTrial = ();

    fn seeds(&self) -> Result<Vec<Self::Genome>, Self::Error> {
        Ok(self.seeds.to_vec())
    }

    fn seed_is_pinned(&self, seed_index: usize) -> bool {
        seed_index < self.seeds.len()
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
        let best = seed_scores
            .iter()
            .enumerate()
            .min_by_key(|(_, score)| *score)
            .map(|(index, _)| index)
            .unwrap_or(0);
        seeds[best].clone()
    }

    fn mutate(&self, genome: &mut Self::Genome, rng: &mut StableRng) {
        mutate_production_order(genome, rng);
    }

    fn score_batch(
        &self,
        candidates: &[(usize, Self::Genome)],
    ) -> Vec<Result<(Self::Score, Self::Evaluation), Self::Error>> {
        let results = candidates
            .par_iter()
            .map(|(ordinal, genome)| self.evaluate(*ordinal, genome))
            .collect();
        let tier_completed = self
            .telemetry
            .evaluations
            .fetch_add(candidates.len(), Ordering::Relaxed)
            + candidates.len();
        (self.progress)(self.telemetry.progress(
            self.tier_evaluations,
            self.evaluation_offset + tier_completed,
        ));
        results
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

impl ProductionOrderAdapter<'_> {
    fn evaluate(
        &self,
        ordinal: usize,
        genome: &ProductionOrderGenome,
    ) -> Result<(BackwardScore, ProductionEvaluation), BackwardSearchError> {
        self.evaluate_rebuilt_problem(
            ordinal,
            rebuild_for_stable_order(
                self.canonical,
                self.distilled,
                self.problem,
                self.trace_len,
                &genome.order,
            ),
        )
    }

    fn evaluate_rebuilt_problem(
        &self,
        ordinal: usize,
        problem: Result<BackwardSearchProblem, BackwardSearchError>,
    ) -> Result<(BackwardScore, ProductionEvaluation), BackwardSearchError> {
        let problem = problem?;
        let paging = solve_production_paging(&problem.demands)?;
        self.telemetry
            .record(paging.solver, paging.plan.telemetry.peak_live_states);
        let candidate =
            compile_and_certify_paging(self.distilled, &problem, &paging.plan, ordinal)?;
        Ok((candidate.score, ProductionEvaluation { problem, candidate }))
    }
}

struct CompletedTier {
    evaluations: usize,
    outcome: SearchDriverOutcome<ProductionOrderGenome, BackwardScore, ProductionEvaluation>,
    telemetry: TierTelemetrySnapshot,
}

pub fn search_production_backward(
    identity: &ProductionSearchIdentity,
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
    preceding_order: Option<&[usize]>,
) -> Result<ProductionBackwardPlan, BackwardSearchError> {
    search_production_backward_with_progress(
        identity,
        canonical,
        distilled,
        trace_len,
        budget_cells,
        preceding_order,
        &|_| {},
    )
}

pub fn search_production_backward_with_progress(
    identity: &ProductionSearchIdentity,
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
    preceding_order: Option<&[usize]>,
    progress: &(dyn Fn(ProductionSearchProgress) + Sync),
) -> Result<ProductionBackwardPlan, BackwardSearchError> {
    let (_, problem) =
        build_backward_search_problem(canonical, distilled, trace_len, budget_cells)?;
    let Some(problem) = problem else {
        return Err(BackwardSearchError::SearchDriverFailure {
            reason: "production backward problem is infeasible",
        });
    };
    let seeds = production_order_seeds(&problem, preceding_order)?;
    let seed = production_identity_seed(identity, budget_cells);
    let mut completed = Vec::new();

    let tier128 = run_production_tier_with_progress(
        canonical, distilled, &problem, trace_len, &seeds, seed, 128, 0, progress,
    )?;
    let improved_seed = tier128.outcome.best_ordinal >= seeds.len();
    let late_winner = tier128.outcome.best_ordinal >= 96;
    completed.push(tier128);

    if production_escalation_tiers(improved_seed, late_winner, false).contains(&512) {
        let tier512 = run_production_tier_with_progress(
            canonical, distilled, &problem, trace_len, &seeds, seed, 512, 128, progress,
        )?;
        let improved_512 =
            score_key(tier512.outcome.best_score) < score_key(completed[0].outcome.best_score);
        completed.push(tier512);
        if production_escalation_tiers(improved_seed, late_winner, improved_512).contains(&2048) {
            completed.push(run_production_tier_with_progress(
                canonical, distilled, &problem, trace_len, &seeds, seed, 2048, 640, progress,
            )?);
        }
    }

    finish_production_search(completed)
}

fn run_production_tier(
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    problem: &BackwardSearchProblem,
    trace_len: usize,
    seeds: &[ProductionOrderGenome],
    seed: u64,
    evaluations: usize,
) -> Result<CompletedTier, BackwardSearchError> {
    run_production_tier_with_progress(
        canonical,
        distilled,
        problem,
        trace_len,
        seeds,
        seed,
        evaluations,
        0,
        &|_| {},
    )
}

#[allow(clippy::too_many_arguments)]
fn run_production_tier_with_progress(
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    problem: &BackwardSearchProblem,
    trace_len: usize,
    seeds: &[ProductionOrderGenome],
    seed: u64,
    evaluations: usize,
    evaluation_offset: usize,
    progress: &(dyn Fn(ProductionSearchProgress) + Sync),
) -> Result<CompletedTier, BackwardSearchError> {
    let telemetry = TierTelemetry::default();
    progress(telemetry.progress(evaluations, evaluation_offset));
    let adapter = ProductionOrderAdapter {
        canonical,
        distilled,
        problem,
        trace_len,
        seeds,
        telemetry: &telemetry,
        tier_evaluations: evaluations,
        evaluation_offset,
        progress,
    };
    let outcome = run_search_driver(
        &adapter,
        SearchDriverConfig {
            population: SEARCH_POPULATION,
            evaluations,
            guided_evaluations: 0,
            score_batch: SEARCH_BATCH,
            seed,
        },
    )
    .map_err(map_search_driver_error)?;
    Ok(CompletedTier {
        evaluations,
        outcome,
        telemetry: telemetry.snapshot(),
    })
}

fn finish_production_search(
    completed: Vec<CompletedTier>,
) -> Result<ProductionBackwardPlan, BackwardSearchError> {
    let mut telemetry = ProductionSearchTelemetry::default();
    let mut best_index = 0usize;
    for (index, tier) in completed.iter().enumerate() {
        telemetry.evaluations = telemetry
            .evaluations
            .checked_add(tier.outcome.evaluations)
            .ok_or(BackwardSearchError::CostOverflow)?;
        telemetry.completed_tiers.push(tier.evaluations);
        telemetry.exact_solver_calls = telemetry
            .exact_solver_calls
            .checked_add(tier.telemetry.exact_solver_calls)
            .ok_or(BackwardSearchError::CostOverflow)?;
        telemetry.peak_dp_states = telemetry.peak_dp_states.max(tier.telemetry.peak_dp_states);
        for solver in &tier.telemetry.solver_kinds {
            if !telemetry.solver_kinds.contains(solver) {
                telemetry.solver_kinds.push(*solver);
            }
        }
        if tier.outcome.best_score < completed[best_index].outcome.best_score {
            best_index = index;
        }
    }

    let winning = completed
        .into_iter()
        .nth(best_index)
        .expect("the 128-evaluation production tier always completes first");
    telemetry.first_winning_ordinal = Some(winning.outcome.best_ordinal);
    telemetry.improvement_ordinals = winning.outcome.improvement_ordinals;
    let order = winning.outcome.best_genome.order;
    let evaluated = winning.outcome.best_evaluation;
    Ok(ProductionBackwardPlan {
        problem: evaluated.problem,
        candidate: evaluated.candidate,
        order,
        telemetry,
    })
}

fn map_search_driver_error(error: SearchDriverError<BackwardSearchError>) -> BackwardSearchError {
    match error {
        SearchDriverError::Adapter(error) => error,
        SearchDriverError::EmptySeeds => BackwardSearchError::SearchDriverFailure {
            reason: "empty production order seeds",
        },
        SearchDriverError::InvalidConfig(reason) => {
            BackwardSearchError::SearchDriverFailure { reason }
        }
        SearchDriverError::ScoreBatchLength { .. } => BackwardSearchError::SearchDriverFailure {
            reason: "production score batch length mismatch",
        },
    }
}

fn production_order_seeds(
    problem: &BackwardSearchProblem,
    preceding_order: Option<&[usize]>,
) -> Result<Vec<ProductionOrderGenome>, BackwardSearchError> {
    let constructive_order = encode_stable_order(problem, &problem.selected_order)?;
    let constructive_stable = decode_order_indices(problem, &constructive_order)?;
    let constructive = ProductionOrderGenome {
        order: constructive_order,
    };
    let mut seeds = vec![constructive];
    if let Some(order) = preceding_order {
        let preceding_stable = decode_order_indices(problem, order)?;
        if preceding_stable != constructive_stable {
            seeds.push(ProductionOrderGenome {
                order: order.to_vec(),
            });
        }
    }
    Ok(seeds)
}

fn mutate_production_order(genome: &mut ProductionOrderGenome, rng: &mut StableRng) {
    if genome.order.len() < 2 {
        return;
    }
    let first = rng.index(genome.order.len());
    let mut second = rng.index(genome.order.len() - 1);
    if second >= first {
        second += 1;
    }
    genome.order.swap(first, second);
}

fn rebuild_for_stable_order(
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    problem: &BackwardSearchProblem,
    trace_len: usize,
    order: &[usize],
) -> Result<BackwardSearchProblem, BackwardSearchError> {
    let stable_order = decode_order_indices(problem, order)?;
    let distilled_indices = problem
        .selected_order
        .iter()
        .cloned()
        .zip(problem.selected_order_indices.iter().copied())
        .collect::<BTreeMap<StableFragmentKey, usize>>();
    let order = stable_order
        .iter()
        .map(|fragment| {
            distilled_indices
                .get(fragment)
                .copied()
                .ok_or(BackwardSearchError::InvalidFragmentPermutation)
        })
        .collect::<Result<Vec<_>, _>>()?;
    build_problem_for_order(
        canonical,
        distilled,
        &order,
        trace_len,
        problem.budget_cells,
        problem.stream_reductions,
    )
}

fn encode_stable_order(
    problem: &BackwardSearchProblem,
    stable_order: &[StableFragmentKey],
) -> Result<Vec<usize>, BackwardSearchError> {
    stable_order
        .iter()
        .map(|fragment| {
            problem
                .fragment_domain
                .binary_search(fragment)
                .map_err(|_| BackwardSearchError::InvalidFragmentPermutation)
        })
        .collect()
}

fn production_escalation_tiers(
    improved_seed_at_128: bool,
    late_winner_at_128: bool,
    improved_512_over_128: bool,
) -> Vec<usize> {
    let mut tiers = vec![128];
    if improved_seed_at_128 || late_winner_at_128 {
        tiers.push(512);
        if improved_512_over_128 {
            tiers.push(2048);
        }
    }
    tiers
}

fn score_key(score: BackwardScore) -> (bool, u128, u128, usize, usize, usize) {
    (
        score.infeasible,
        score.whole_pass_dram_bytes,
        score.primitive_source_ops,
        score.instructions,
        score.encoded_lanes,
        score.arithmetic_ops,
    )
}

fn production_identity_seed(identity: &ProductionSearchIdentity, budget_cells: usize) -> u64 {
    let mut seed = FNV_OFFSET;
    hash_framed_bytes(&mut seed, identity.circuit.as_bytes());
    hash_framed_bytes(&mut seed, identity.layout_fixture.as_bytes());
    hash_bytes(&mut seed, &(identity.layer as u64).to_le_bytes());
    hash_bytes(
        &mut seed,
        &[match identity.regime {
            BwdRegime::R0 => 0,
            BwdRegime::Ext => 1,
        }],
    );
    hash_bytes(&mut seed, &(budget_cells as u64).to_le_bytes());
    seed
}

fn hash_framed_bytes(hash: &mut u64, bytes: &[u8]) {
    let length = u64::try_from(bytes.len()).expect("production identity length fits u64");
    hash_bytes(hash, &length.to_le_bytes());
    hash_bytes(hash, bytes);
}

fn hash_bytes(hash: &mut u64, bytes: &[u8]) {
    for &byte in bytes {
        *hash ^= u64::from(byte);
        *hash = hash.wrapping_mul(FNV_PRIME);
    }
}

pub fn compulsory_read_floor(
    problem: &BackwardSearchProblem,
) -> Result<SourceCost, BackwardSearchError> {
    let mut seen = BTreeSet::new();
    let mut floor = problem.materialization.fixed_writes;
    for demand in &problem.demands {
        if seen.insert(demand.expr) {
            floor = floor.checked_add(demand.miss_cost)?;
        }
    }
    Ok(floor)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup,
        RootId, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind, VirtualSetupKind,
    };

    use crate::bwd::distill::{DistilledLayer, distill};
    use crate::eval_plan::backward_search::problem::build_backward_search_problem;
    use crate::eval_plan::backward_search::solve_production_paging;
    use crate::eval_plan::search_driver::StableRng;

    use super::*;

    #[test]
    fn production_order_genome_has_constructive_and_previous_seeds() {
        let (canonical, distilled) = stable_domain_mismatch_fixture();
        let (_, problem) = build_backward_search_problem(&canonical, &distilled, 8, 4).unwrap();
        let problem = problem.unwrap();
        let constructive = stable_indices_for(&problem, &problem.selected_order);
        assert_ne!(
            constructive, problem.selected_order_indices,
            "fixture must distinguish stable-domain positions from raw indices"
        );
        let seeds = production_order_seeds(&problem, Some(&constructive)).unwrap();
        assert_eq!(seeds[0].order, constructive);
        assert_eq!(
            decode_order_indices(&problem, &seeds[0].order).unwrap(),
            problem.selected_order
        );
        assert_eq!(seeds.len(), 1, "identical previous order is deduplicated");

        let mut reversed = constructive;
        reversed.reverse();
        let seeds = production_order_seeds(&problem, Some(&reversed)).unwrap();
        assert_eq!(seeds.len(), 2);
        assert_eq!(seeds[1].order, reversed);
        assert_eq!(
            decode_order_indices(&problem, &seeds[1].order).unwrap(),
            problem
                .selected_order
                .iter()
                .cloned()
                .rev()
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn production_order_mutation_swaps_integer_positions() {
        let (canonical, distilled) = stable_domain_mismatch_fixture();
        let (_, problem) = build_backward_search_problem(&canonical, &distilled, 8, 4).unwrap();
        let problem = problem.unwrap();
        let original = stable_indices_for(&problem, &problem.selected_order);
        let mut genome = ProductionOrderGenome {
            order: original.clone(),
        };
        let mut rng = StableRng::new(17);
        mutate_production_order(&mut genome, &mut rng);
        let mut sorted = genome.order.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, (0..original.len()).collect::<Vec<_>>());
        assert_eq!(
            genome
                .order
                .iter()
                .zip(&original)
                .filter(|(left, right)| left != right)
                .count(),
            2,
            "one mutation is exactly one transposition"
        );
        let rebuilt =
            rebuild_for_stable_order(&canonical, &distilled, &problem, 8, &genome.order).unwrap();
        assert_eq!(
            decode_order_indices(&problem, &genome.order).unwrap(),
            rebuilt.selected_order
        );
        assert_eq!(rebuilt.stream_reductions, problem.stream_reductions);
    }

    #[test]
    fn malformed_production_permutations_are_rejected() {
        let (canonical, distilled) = stable_domain_mismatch_fixture();
        let (_, problem) = build_backward_search_problem(&canonical, &distilled, 8, 4).unwrap();
        let problem = problem.unwrap();
        let len = problem.fragment_domain.len();
        for malformed in [
            (0..len.saturating_sub(1)).collect::<Vec<_>>(),
            vec![0; len],
            (0..len)
                .map(|index| if index + 1 == len { len } else { index })
                .collect(),
        ] {
            assert_eq!(
                production_order_seeds(&problem, Some(&malformed)).unwrap_err(),
                BackwardSearchError::InvalidFragmentPermutation
            );
            assert_eq!(
                rebuild_for_stable_order(&canonical, &distilled, &problem, 8, &malformed)
                    .unwrap_err(),
                BackwardSearchError::InvalidFragmentPermutation
            );
        }
    }

    #[test]
    fn production_result_order_matches_rebuilt_selected_order_and_telemetry() {
        let canonical = stable_domain_mismatch_paging_trivial_layer();
        let distilled = distill(&canonical, BwdRegime::Ext, &HashMap::new(), None);
        let (_, initial) = build_backward_search_problem(&canonical, &distilled, 8, 4).unwrap();
        let initial = initial.unwrap();
        let mut preceding = stable_indices_for(&initial, &initial.selected_order);
        preceding.reverse();
        let result = search_production_backward(
            &test_identity(BwdRegime::Ext),
            &canonical,
            &distilled,
            8,
            4,
            Some(&preceding),
        )
        .unwrap();
        assert_eq!(
            decode_order_indices(&result.problem, &result.order).unwrap(),
            result.problem.selected_order
        );
        assert_eq!(
            result.telemetry.evaluations,
            result.telemetry.completed_tiers.iter().sum::<usize>()
        );
        assert_eq!(
            result.telemetry.exact_solver_calls, result.telemetry.evaluations,
            "every counted production evaluation reaches the exact pager"
        );
        assert_eq!(result.problem.stream_reductions, initial.stream_reductions);
        assert_eq!(
            result.telemetry.solver_kinds,
            vec![ProductionPagingSolver::RetainAll]
        );
        let largest_completed_tier = *result.telemetry.completed_tiers.last().unwrap();
        assert!(result.telemetry.first_winning_ordinal.unwrap() < largest_completed_tier);
        assert!(
            result
                .telemetry
                .improvement_ordinals
                .iter()
                .all(|&ordinal| ordinal < largest_completed_tier)
        );
    }

    #[test]
    fn production_observer_reports_bounded_deterministic_search_work() {
        let canonical = paging_trivial_four_fragment_layer();
        let distilled = distill(&canonical, BwdRegime::Ext, &HashMap::new(), None);
        let snapshots = std::sync::Mutex::new(Vec::<ProductionSearchProgress>::new());
        let result = search_production_backward_with_progress(
            &test_identity(BwdRegime::Ext),
            &canonical,
            &distilled,
            8,
            4,
            None,
            &|snapshot| snapshots.lock().unwrap().push(snapshot),
        )
        .unwrap();
        let snapshots = snapshots.into_inner().unwrap();
        assert!(!snapshots.is_empty());
        assert_eq!(snapshots[0].tier_evaluations, 128);
        assert_eq!(snapshots[0].evaluations, 0);
        assert_eq!(
            snapshots.last().unwrap().evaluations,
            result.telemetry.evaluations
        );
        assert!(snapshots.windows(2).all(|pair| {
            pair[0].tier_evaluations != pair[1].tier_evaluations
                || pair[0].evaluations <= pair[1].evaluations
        }));
        assert!(snapshots.last().unwrap().solver.is_some());
    }

    #[test]
    fn preceding_budget_seed_is_scored_inside_the_fresh_tier() {
        let canonical = stable_domain_mismatch_paging_trivial_layer();
        let distilled = distill(&canonical, BwdRegime::Ext, &HashMap::new(), None);
        let (_, problem) = build_backward_search_problem(&canonical, &distilled, 8, 4).unwrap();
        let problem = problem.unwrap();
        let mut preceding = stable_indices_for(&problem, &problem.selected_order);
        preceding.reverse();
        let seeds = production_order_seeds(&problem, Some(&preceding)).unwrap();
        assert_eq!(seeds.len(), 2);
        let tier = run_production_tier(
            &canonical,
            &distilled,
            &problem,
            8,
            &seeds,
            production_identity_seed(&test_identity(BwdRegime::Ext), 4),
            2,
        )
        .unwrap();
        assert_eq!(tier.outcome.evaluations, 2);
        assert_eq!(tier.telemetry.exact_solver_calls, 2);
        assert!(tier.outcome.best_ordinal < 2);
        let winning_problem = &tier.outcome.best_evaluation.problem;
        assert_eq!(
            decode_order_indices(&problem, &tier.outcome.best_genome.order).unwrap(),
            winning_problem.selected_order
        );
        assert_eq!(winning_problem.stream_reductions, problem.stream_reductions);
    }

    #[test]
    fn placement_failed_candidate_rebuild_is_fatal_before_paging() {
        let (canonical, distilled) = shared_source_fixture();
        let (_, problem) = build_backward_search_problem(&canonical, &distilled, 8, 4).unwrap();
        let problem = problem.unwrap();
        let telemetry = TierTelemetry::default();
        let seeds = [ProductionOrderGenome {
            order: stable_indices_for(&problem, &problem.selected_order),
        }];
        let adapter = ProductionOrderAdapter {
            canonical: &canonical,
            distilled: &distilled,
            problem: &problem,
            trace_len: 8,
            seeds: &seeds,
            telemetry: &telemetry,
            tier_evaluations: 1,
            evaluation_offset: 0,
            progress: &|_| {},
        };
        assert!(matches!(
            adapter.evaluate_rebuilt_problem(
                7,
                Err(BackwardSearchError::BackwardEvaluation(
                    crate::eval_plan::backward::BackwardEvaluationError::Concrete(
                        crate::eval_plan::ConcreteBindError::PlacementFailed {
                            budget_lanes: 16,
                            peak_live_lanes: 20,
                            telemetry: crate::eval_plan::PlacementTelemetry::default(),
                        }
                    )
                ))
            ),
            Err(BackwardSearchError::BackwardEvaluation(
                crate::eval_plan::backward::BackwardEvaluationError::Concrete(
                    crate::eval_plan::ConcreteBindError::PlacementFailed { .. }
                )
            ))
        ));
        assert_eq!(telemetry.snapshot().exact_solver_calls, 0);
    }

    #[test]
    fn empty_leaf_domain_still_searches_fragment_order() {
        let canonical = paging_trivial_four_fragment_layer();
        let distilled = distill(&canonical, BwdRegime::Ext, &HashMap::new(), None);
        let result = search_production_backward(
            &test_identity(BwdRegime::Ext),
            &canonical,
            &distilled,
            8,
            4,
            None,
        )
        .unwrap();
        assert!(result.problem.leaf_domain.is_empty());
        assert!(result.candidate.paging.actions.is_empty());
        assert_eq!(result.order.len(), 4);
        assert_eq!(result.telemetry.evaluations, 128);
        assert_eq!(
            result.telemetry.exact_solver_calls,
            result.telemetry.evaluations
        );
    }

    #[test]
    fn production_tiers_are_exactly_plan3_tiers() {
        assert_eq!(production_escalation_tiers(false, false, false), vec![128]);
        assert_eq!(
            production_escalation_tiers(true, false, false),
            vec![128, 512]
        );
        assert_eq!(
            production_escalation_tiers(false, true, false),
            vec![128, 512]
        );
        assert_eq!(
            production_escalation_tiers(true, false, true),
            vec![128, 512, 2048]
        );
    }

    #[test]
    fn production_identity_seed_is_stable_and_coordinate_sensitive() {
        let identity = test_identity(BwdRegime::R0);
        let seed = production_identity_seed(&identity, 4);
        assert_eq!(seed, 0xbbf2_c671_016e_083b);
        assert_eq!(seed, production_identity_seed(&identity, 4));
        assert_ne!(seed, production_identity_seed(&identity, 5));

        let mut changed = identity.clone();
        changed.circuit.push('x');
        assert_ne!(seed, production_identity_seed(&changed, 4));
        changed = identity.clone();
        changed.regime = BwdRegime::Ext;
        assert_ne!(seed, production_identity_seed(&changed, 4));
        changed = identity.clone();
        changed.layer += 1;
        assert_ne!(seed, production_identity_seed(&changed, 4));
        changed = identity.clone();
        changed.layout_fixture.push('x');
        assert_ne!(seed, production_identity_seed(&changed, 4));

        let left = ProductionSearchIdentity {
            circuit: "ab".to_owned(),
            layout_fixture: "c".to_owned(),
            ..identity.clone()
        };
        let right = ProductionSearchIdentity {
            circuit: "a".to_owned(),
            layout_fixture: "bc".to_owned(),
            ..identity
        };
        assert_ne!(
            production_identity_seed(&left, 4),
            production_identity_seed(&right, 4),
            "circuit/layout string boundaries are framed into the seed"
        );
    }

    #[test]
    fn compulsory_floor_bounds_exact_paging_cost() {
        let (canonical, distilled) = shared_source_fixture();
        let (_, problem) = build_backward_search_problem(&canonical, &distilled, 8, 4).unwrap();
        let problem = problem.unwrap();
        let floor = compulsory_read_floor(&problem).unwrap();
        let fixed_dram = problem.materialization.fixed_writes.dram_bytes().unwrap();
        let fixed_ops = problem
            .materialization
            .fixed_writes
            .ops
            .primitive_equivalents()
            .unwrap();

        let constrained = solve_production_paging(&problem.demands).unwrap().plan;
        assert!(constrained.objective.dram_bytes + fixed_dram >= floor.dram_bytes().unwrap());
        assert!(
            constrained.objective.primitive_source_ops + fixed_ops
                >= floor.ops.primitive_equivalents().unwrap()
        );

        let mut unlimited = problem.clone();
        for demand in &mut unlimited.demands {
            demand.gap_capacity_lanes = u8::MAX;
        }
        let unlimited = solve_production_paging(&unlimited.demands).unwrap().plan;
        assert_eq!(
            unlimited.objective.dram_bytes + fixed_dram,
            floor.dram_bytes().unwrap()
        );
        assert_eq!(
            unlimited.objective.primitive_source_ops + fixed_ops,
            floor.ops.primitive_equivalents().unwrap()
        );
    }

    fn test_identity(regime: BwdRegime) -> ProductionSearchIdentity {
        ProductionSearchIdentity {
            circuit: "synthetic".to_owned(),
            layout_fixture: "synthetic_layout_gkr.json".to_owned(),
            layer: 0,
            regime,
        }
    }

    fn shared_source_fixture() -> (DagLayer, DistilledLayer) {
        let layer = synthetic_two_shared_sources_layer();
        let distilled = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
        (layer, distilled)
    }

    fn stable_domain_mismatch_fixture() -> (DagLayer, DistilledLayer) {
        let mut layer = synthetic_two_shared_sources_layer();
        layer.roots.rotate_left(1);
        let distilled = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
        (layer, distilled)
    }

    fn stable_domain_mismatch_paging_trivial_layer() -> DagLayer {
        let mut layer = paging_trivial_four_fragment_layer();
        layer.roots.rotate_left(1);
        layer
    }

    fn stable_indices_for(
        problem: &BackwardSearchProblem,
        stable_order: &[StableFragmentKey],
    ) -> Vec<usize> {
        stable_order
            .iter()
            .map(|fragment| problem.fragment_domain.binary_search(fragment).unwrap())
            .collect()
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

    fn paging_trivial_four_fragment_layer() -> DagLayer {
        DagLayer {
            sources: [
                VirtualSetupKind::RangeCheck16Bits,
                VirtualSetupKind::RangeCheckTimestamp,
                VirtualSetupKind::InitsAndTeardownsLow,
                VirtualSetupKind::InitsAndTeardownsHigh,
            ]
            .into_iter()
            .map(|kind| SourceInfo {
                kind: SourceKind::VirtualSetup { kind },
            })
            .collect(),
            exprs: (0..4)
                .map(|source| Expr::Source(SourceId(source)))
                .chain([
                    Expr::Mul(vec![ExprId(0), ExprId(1)]),
                    Expr::Mul(vec![ExprId(0), ExprId(2)]),
                    Expr::Mul(vec![ExprId(0), ExprId(3)]),
                    Expr::Mul(vec![ExprId(1), ExprId(2)]),
                ])
                .collect(),
            batching: BatchingOrder {
                roots: (0..4).map(RootId).collect(),
            },
            roots: (0..4)
                .map(|index| claim_root(ExprId(4 + index), index as usize))
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
