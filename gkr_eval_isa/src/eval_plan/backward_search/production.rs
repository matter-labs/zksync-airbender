use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex, OnceLock};
use std::time::{Duration, Instant};

use gkr_eval_ir::DagLayer;
use rayon::prelude::*;

use crate::bwd::distill::DistilledLayer;
use crate::eval_plan::search_driver::{
    SearchAdapter, SearchDriverConfig, SearchDriverError, SearchDriverOutcome, StableRng,
    run_search_driver,
};

use super::pager::{
    PagingAction, ProductionPagingProgress, reconstruct_paging_plan,
    solve_production_paging_observed,
};
use super::problem::{
    BackwardSearchProblem, StableFragmentKey, build_backward_search_problem,
    build_problem_for_order, decode_order_indices,
};
use super::{
    BackwardScore, BackwardSearchError, CertifiedBackwardCandidate, ProductionPagingSolver,
    SourceCost, compile_and_certify_paging,
};

const SEARCH_POPULATION: usize = 32;
const SEARCH_BATCH: usize = 16;
pub const MAX_CONCURRENT_PRODUCTION_EVALUATIONS: usize = 4;
const LIVE_PROGRESS_INTERVAL: Duration = Duration::from_secs(1);
const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductionSearchIdentity {
    pub circuit: String,
    pub layout_fixture: String,
    pub layer: usize,
    pub regime: crate::BwdRegime,
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

struct EvaluationPermitGate {
    available: Mutex<usize>,
    wake: Condvar,
}

struct EvaluationPermit<'a>(&'a EvaluationPermitGate);

impl EvaluationPermitGate {
    fn acquire(&self) -> EvaluationPermit<'_> {
        let mut available = self.available.lock().expect("lock production permits");
        while *available == 0 {
            #[cfg(test)]
            {
                drop(available);
                observe_production_evaluation_test_stage(
                    ProductionEvaluationTestStage::PermitContended,
                );
                available = self.available.lock().expect("relock production permits");
                if *available != 0 {
                    continue;
                }
            }
            available = self
                .wake
                .wait(available)
                .expect("wait for production permit");
        }
        *available -= 1;
        EvaluationPermit(self)
    }
}

impl Drop for EvaluationPermit<'_> {
    fn drop(&mut self) {
        #[cfg(test)]
        observe_production_evaluation_test_stage(ProductionEvaluationTestStage::PermitReleasing);
        let mut available = self.0.available.lock().expect("release production permit");
        *available += 1;
        self.0.wake.notify_one();
    }
}

fn production_evaluation_gate() -> &'static EvaluationPermitGate {
    static GATE: OnceLock<EvaluationPermitGate> = OnceLock::new();
    GATE.get_or_init(|| EvaluationPermitGate {
        available: Mutex::new(MAX_CONCURRENT_PRODUCTION_EVALUATIONS),
        wake: Condvar::new(),
    })
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProductionEvaluationTestStage {
    WaitingForPermit,
    PermitContended,
    PermitAcquired,
    PagingCompleted,
    CertificationCompleted,
    PermitReleasing,
}

#[cfg(test)]
#[derive(Clone)]
struct ProductionEvaluationTestHookRegistration {
    scope: u64,
    callback: std::sync::Arc<dyn Fn(ProductionEvaluationTestStage) + Send + Sync>,
}

#[cfg(test)]
struct ProductionEvaluationTestHook {
    scope: u64,
    _owner: std::sync::MutexGuard<'static, ()>,
}

#[cfg(test)]
impl ProductionEvaluationTestHook {
    fn install(callback: impl Fn(ProductionEvaluationTestStage) + Send + Sync + 'static) -> Self {
        static NEXT_SCOPE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        let owner = production_evaluation_test_hook_owner()
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let scope = NEXT_SCOPE.fetch_add(1, Ordering::Relaxed);
        let mut active = production_evaluation_test_hook()
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        assert!(
            active.is_none(),
            "production evaluation test hook is unique"
        );
        *active = Some(ProductionEvaluationTestHookRegistration {
            scope,
            callback: std::sync::Arc::new(callback),
        });
        drop(active);
        Self {
            scope,
            _owner: owner,
        }
    }

    fn scope(&self) -> u64 {
        self.scope
    }
}

#[cfg(test)]
impl Drop for ProductionEvaluationTestHook {
    fn drop(&mut self) {
        let mut active = production_evaluation_test_hook()
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        assert_eq!(
            active.as_ref().map(|hook| hook.scope),
            Some(self.scope),
            "drop the active production evaluation test hook"
        );
        *active = None;
    }
}

#[cfg(test)]
fn production_evaluation_test_hook_owner() -> &'static Mutex<()> {
    static OWNER: OnceLock<Mutex<()>> = OnceLock::new();
    OWNER.get_or_init(|| Mutex::new(()))
}

#[cfg(test)]
type ProductionEvaluationTestHookSlot = Mutex<Option<ProductionEvaluationTestHookRegistration>>;

#[cfg(test)]
fn production_evaluation_test_hook() -> &'static ProductionEvaluationTestHookSlot {
    static HOOK: OnceLock<ProductionEvaluationTestHookSlot> = OnceLock::new();
    HOOK.get_or_init(|| Mutex::new(None))
}

#[cfg(test)]
std::thread_local! {
    static PRODUCTION_EVALUATION_TEST_SCOPE: std::cell::Cell<Option<u64>> = const {
        std::cell::Cell::new(None)
    };
}

#[cfg(test)]
fn with_production_evaluation_test_scope<T>(scope: u64, run: impl FnOnce() -> T) -> T {
    struct ResetScope(Option<u64>);

    impl Drop for ResetScope {
        fn drop(&mut self) {
            PRODUCTION_EVALUATION_TEST_SCOPE.with(|active| active.set(self.0));
        }
    }

    let previous = PRODUCTION_EVALUATION_TEST_SCOPE.with(|active| active.replace(Some(scope)));
    let _reset = ResetScope(previous);
    run()
}

#[cfg(test)]
fn observe_production_evaluation_test_stage(stage: ProductionEvaluationTestStage) {
    let Some(scope) = PRODUCTION_EVALUATION_TEST_SCOPE.with(std::cell::Cell::get) else {
        return;
    };
    let callback = production_evaluation_test_hook()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .as_ref()
        .filter(|hook| hook.scope == scope)
        .map(|hook| std::sync::Arc::clone(&hook.callback));
    if let Some(callback) = callback {
        callback(stage);
    }
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
    evaluations: AtomicUsize,
    paging: Mutex<PagingTelemetryState>,
}

#[derive(Default)]
struct PagingTelemetryState {
    latest: Option<ProductionPagingProgress>,
    solver_mask: u8,
    tier_peak_states: usize,
    last_forwarded_at: Option<Instant>,
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
        self.observe(ProductionPagingProgress {
            solver,
            current_states: peak_dp_states,
            peak_states: peak_dp_states,
        });
    }

    fn observe(&self, progress: ProductionPagingProgress) {
        let mut paging = self.paging.lock().expect("lock tier paging telemetry");
        paging.observe(progress);
    }

    fn observe_progress(
        &self,
        progress: ProductionPagingProgress,
        tier_evaluations: usize,
        evaluations: usize,
    ) -> Option<ProductionSearchProgress> {
        self.observe_progress_with_clock(progress, tier_evaluations, evaluations, Instant::now)
    }

    fn observe_progress_at(
        &self,
        progress: ProductionPagingProgress,
        tier_evaluations: usize,
        evaluations: usize,
        now: Instant,
    ) -> Option<ProductionSearchProgress> {
        self.observe_progress_with_clock(progress, tier_evaluations, evaluations, || now)
    }

    fn observe_progress_with_clock(
        &self,
        progress: ProductionPagingProgress,
        tier_evaluations: usize,
        evaluations: usize,
        now: impl FnOnce() -> Instant,
    ) -> Option<ProductionSearchProgress> {
        let mut paging = self.paging.lock().expect("lock tier paging telemetry");
        let now = now();
        paging.observe(progress);
        if progress.current_states == 0 && progress.peak_states == 0 {
            return None;
        }
        if paging
            .last_forwarded_at
            .is_some_and(|last| now.saturating_duration_since(last) < LIVE_PROGRESS_INTERVAL)
        {
            return None;
        }
        paging.last_forwarded_at = Some(now);
        Some(ProductionSearchProgress {
            tier_evaluations,
            tier_completed: self.evaluations.load(Ordering::Relaxed),
            evaluations,
            solver: Some(progress.solver),
            dp_states: progress.current_states,
            peak_dp_states: progress.peak_states,
        })
    }

    fn progress(&self, tier_evaluations: usize, evaluations: usize) -> ProductionSearchProgress {
        let paging = self.paging.lock().expect("lock tier paging telemetry");
        let latest = paging.latest;
        ProductionSearchProgress {
            tier_evaluations,
            tier_completed: self.evaluations.load(Ordering::Relaxed),
            evaluations,
            solver: latest.map(|progress| progress.solver),
            dp_states: latest.map_or(0, |progress| progress.current_states),
            peak_dp_states: latest.map_or(0, |progress| progress.peak_states),
        }
    }

    fn snapshot(&self) -> TierTelemetrySnapshot {
        let paging = self.paging.lock().expect("lock tier paging telemetry");
        let mask = paging.solver_mask;
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
            peak_dp_states: paging.tier_peak_states,
        }
    }
}

impl PagingTelemetryState {
    fn observe(&mut self, progress: ProductionPagingProgress) {
        self.solver_mask |= match progress.solver {
            ProductionPagingSolver::RetainAll => 1,
            ProductionPagingSolver::UniformIntervals => 2,
            ProductionPagingSolver::ResidentSets => 4,
        };
        self.tier_peak_states = self.tier_peak_states.max(progress.peak_states);
        self.latest = Some(progress);
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
        let (paging, candidate) = {
            #[cfg(test)]
            observe_production_evaluation_test_stage(
                ProductionEvaluationTestStage::WaitingForPermit,
            );
            let _permit = production_evaluation_gate().acquire();
            #[cfg(test)]
            observe_production_evaluation_test_stage(ProductionEvaluationTestStage::PermitAcquired);
            let paging = solve_production_paging_observed(&problem.demands, |paging_progress| {
                if let Some(progress) = self.telemetry.observe_progress(
                    paging_progress,
                    self.tier_evaluations,
                    self.evaluation_offset + self.telemetry.evaluations.load(Ordering::Relaxed),
                ) {
                    (self.progress)(progress);
                }
            })?;
            #[cfg(test)]
            observe_production_evaluation_test_stage(
                ProductionEvaluationTestStage::PagingCompleted,
            );
            let candidate =
                compile_and_certify_paging(self.distilled, &problem, &paging.plan, ordinal)?;
            #[cfg(test)]
            observe_production_evaluation_test_stage(
                ProductionEvaluationTestStage::CertificationCompleted,
            );
            (paging, candidate)
        };
        self.telemetry
            .record(paging.solver, paging.plan.telemetry.peak_live_states);
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

pub fn select_production_backward_seeds(
    identity: &ProductionSearchIdentity,
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
    preceding_order: Option<&[usize]>,
) -> Result<ProductionBackwardPlan, BackwardSearchError> {
    select_production_backward_seeds_with_progress(
        identity,
        canonical,
        distilled,
        trace_len,
        budget_cells,
        preceding_order,
        &|_| {},
    )
}

pub fn construct_production_backward_bypass(
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
) -> Result<ProductionBackwardPlan, BackwardSearchError> {
    let (_, problem) =
        build_backward_search_problem(canonical, distilled, trace_len, budget_cells)?;
    let Some(problem) = problem else {
        return Err(BackwardSearchError::SearchDriverFailure {
            reason: "production backward problem is infeasible",
        });
    };
    let order = encode_stable_order(&problem, &problem.selected_order)?;
    let actions = vec![PagingAction::Bypass; problem.demands.len()];
    let paging = reconstruct_paging_plan(&problem.demands, &actions)?;
    let candidate = compile_and_certify_paging(distilled, &problem, &paging, 0)?;
    Ok(ProductionBackwardPlan {
        problem,
        candidate,
        order,
        telemetry: ProductionSearchTelemetry::default(),
    })
}

pub fn select_production_backward_seeds_with_progress(
    _identity: &ProductionSearchIdentity,
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
    let mut seeds = production_order_seeds(&problem, preceding_order)?;
    let telemetry = TierTelemetry::default();
    progress(telemetry.progress(seeds.len(), 0));
    let mut evaluated = Vec::with_capacity(seeds.len());
    let mut improvement_ordinals = Vec::new();
    let mut best_score = None;
    {
        let adapter = ProductionOrderAdapter {
            canonical,
            distilled,
            problem: &problem,
            trace_len,
            seeds: &seeds,
            telemetry: &telemetry,
            tier_evaluations: seeds.len(),
            evaluation_offset: 0,
            progress,
        };
        for (ordinal, genome) in seeds.iter().cloned().enumerate() {
            let (score, evaluation) = if ordinal == 0 {
                adapter.evaluate_rebuilt_problem(ordinal, Ok(problem.clone()))?
            } else {
                adapter.evaluate(ordinal, &genome)?
            };
            if best_score.is_some_and(|best| score < best) {
                improvement_ordinals.push(ordinal);
            }
            if best_score.is_none_or(|best| score < best) {
                best_score = Some(score);
            }
            let completed = telemetry.evaluations.fetch_add(1, Ordering::Relaxed) + 1;
            progress(telemetry.progress(adapter.tier_evaluations, completed));
            evaluated.push((score, ordinal, genome, evaluation));
        }
    }

    let floor_bytes = compulsory_read_floor(&problem)?.dram_bytes()?;
    let initial_seed_count = seeds.len();
    // Exact-score one cheap alternative only where the existing seeds still
    // leave avoidable reads. The exact compiler remains the authority.
    if best_score.is_some_and(|score| score.whole_pass_dram_bytes > floor_bytes) {
        let order = budget_aware_seed_order(&problem)?;
        if !seeds.iter().any(|seed| seed.order == order) {
            seeds.push(ProductionOrderGenome { order });
        }
    }
    if seeds.len() > initial_seed_count {
        progress(telemetry.progress(seeds.len(), telemetry.evaluations.load(Ordering::Relaxed)));
        let adapter = ProductionOrderAdapter {
            canonical,
            distilled,
            problem: &problem,
            trace_len,
            seeds: &seeds,
            telemetry: &telemetry,
            tier_evaluations: seeds.len(),
            evaluation_offset: 0,
            progress,
        };
        for (ordinal, genome) in seeds.iter().cloned().enumerate().skip(initial_seed_count) {
            let (score, evaluation) = adapter.evaluate(ordinal, &genome)?;
            if best_score.is_some_and(|best| score < best) {
                improvement_ordinals.push(ordinal);
            }
            if best_score.is_none_or(|best| score < best) {
                best_score = Some(score);
            }
            let completed = telemetry.evaluations.fetch_add(1, Ordering::Relaxed) + 1;
            progress(telemetry.progress(adapter.tier_evaluations, completed));
            evaluated.push((score, ordinal, genome, evaluation));
        }
    }

    let snapshot = telemetry.snapshot();
    let (_, winning_ordinal, winning_genome, winning_evaluation) = evaluated
        .into_iter()
        .min_by_key(|(score, ordinal, _, _)| (*score, *ordinal))
        .expect("production order seeds always contain the constructive order");
    Ok(ProductionBackwardPlan {
        problem: winning_evaluation.problem,
        candidate: winning_evaluation.candidate,
        order: winning_genome.order,
        telemetry: ProductionSearchTelemetry {
            evaluations: telemetry.evaluations.load(Ordering::Relaxed),
            completed_tiers: Vec::new(),
            first_winning_ordinal: Some(winning_ordinal),
            improvement_ordinals,
            exact_solver_calls: snapshot.exact_solver_calls,
            solver_kinds: snapshot.solver_kinds,
            peak_dp_states: snapshot.peak_dp_states,
        },
    })
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

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProxyValue {
    width_lanes: usize,
    read_cost: u128,
    fragments: Vec<usize>,
}

/// Build one deterministic, budget-aware alternative order. Connected reuse
/// components stay contiguous, and fragments are appended individually.
fn budget_aware_greedy_order(
    fragment_count: usize,
    values: &[ProxyValue],
    capacity_lanes: usize,
) -> Vec<usize> {
    if fragment_count == 0 {
        return Vec::new();
    }

    let mut parent = (0..fragment_count).collect::<Vec<_>>();
    fn find(parent: &mut [usize], mut item: usize) -> usize {
        while parent[item] != item {
            parent[item] = parent[parent[item]];
            item = parent[item];
        }
        item
    }
    fn union(parent: &mut [usize], left: usize, right: usize) {
        let left = find(parent, left);
        let right = find(parent, right);
        if left != right {
            parent[right] = left;
        }
    }
    for value in values {
        if let Some((&first, rest)) = value.fragments.split_first() {
            for &fragment in rest {
                union(&mut parent, first, fragment);
            }
        }
    }
    let mut components = BTreeMap::<usize, Vec<usize>>::new();
    for fragment in 0..fragment_count {
        let root = find(&mut parent, fragment);
        components.entry(root).or_default().push(fragment);
    }
    let mut components = components.into_values().collect::<Vec<_>>();
    components.sort_by_key(|component| component[0]);

    let mut values_by_fragment = vec![Vec::new(); fragment_count];
    for (value_index, value) in values.iter().enumerate() {
        for &fragment in &value.fragments {
            values_by_fragment[fragment].push(value_index);
        }
    }

    let mut order = Vec::with_capacity(fragment_count);
    let mut placed = vec![false; fragment_count];
    let mut placed_uses = vec![0; values.len()];
    for component in components {
        for _ in 0..component.len() {
            let mut best = None;
            for &fragment in &component {
                if placed[fragment] {
                    continue;
                }
                let mut candidate_uses = placed_uses.clone();
                for &value in &values_by_fragment[fragment] {
                    candidate_uses[value] += 1;
                }
                let (spill_cost, live_cost, live_width) =
                    proxy_frontier_cost(values, &candidate_uses, capacity_lanes);
                let key = (spill_cost, live_cost, live_width, fragment);
                if best.as_ref().is_none_or(|(best_key, _)| key < *best_key) {
                    best = Some((key, fragment));
                }
            }
            let (_, fragment) = best.expect("an unplaced component fragment remains");
            placed[fragment] = true;
            for &value in &values_by_fragment[fragment] {
                placed_uses[value] += 1;
            }
            order.push(fragment);
        }
    }
    order
}

fn proxy_frontier_cost(
    values: &[ProxyValue],
    placed_uses: &[usize],
    capacity_lanes: usize,
) -> (u128, u128, usize) {
    let live = values
        .iter()
        .zip(placed_uses)
        .filter(|(value, placed)| **placed != 0 && **placed < value.fragments.len())
        .collect::<Vec<_>>();
    let live_cost = live.iter().fold(0u128, |cost, (value, _)| {
        cost.saturating_add(value.read_cost)
    });
    let live_width = live.iter().fold(0usize, |width, (value, _)| {
        width.saturating_add(value.width_lanes)
    });
    // A tiny 0/1 knapsack estimates the read cost that cannot remain resident
    // across this prefix boundary. Widths and capacity are physical lanes.
    let mut kept = vec![0u128; capacity_lanes.saturating_add(1)];
    for (value, _) in &live {
        if value.width_lanes > capacity_lanes {
            continue;
        }
        for lanes in (value.width_lanes..=capacity_lanes).rev() {
            kept[lanes] =
                kept[lanes].max(kept[lanes - value.width_lanes].saturating_add(value.read_cost));
        }
    }
    let retained_cost = kept.into_iter().max().unwrap_or(0);
    (
        live_cost.saturating_sub(retained_cost),
        live_cost,
        live_width,
    )
}

/// Project the exact problem's round-weighted source costs and observed cache
/// capacity into the cheap constructor model.
fn budget_aware_seed_order(
    problem: &BackwardSearchProblem,
) -> Result<Vec<usize>, BackwardSearchError> {
    let mut grouped = BTreeMap::new();
    for demand in &problem.demands {
        let fragment = problem
            .fragment_domain
            .binary_search(&demand.key.fragment)
            .map_err(|_| BackwardSearchError::InvalidFragmentPermutation)?;
        let read_cost = demand.miss_cost.dram_bytes()?;
        let entry = grouped
            .entry(demand.expr)
            .or_insert_with(|| (usize::from(demand.width_lanes), read_cost, BTreeSet::new()));
        if entry.0 != usize::from(demand.width_lanes) || entry.1 != read_cost {
            return Err(BackwardSearchError::PagingCertificateMismatch {
                observable: "fragment-order proxy source cost",
            });
        }
        entry.2.insert(fragment);
    }
    let values = grouped
        .into_values()
        .filter_map(|(width_lanes, read_cost, fragments)| {
            (fragments.len() > 1).then(|| ProxyValue {
                width_lanes,
                read_cost,
                fragments: fragments.into_iter().collect(),
            })
        })
        .collect::<Vec<_>>();
    let mut capacities = problem
        .demands
        .iter()
        .filter(|demand| demand.has_next)
        .map(|demand| usize::from(demand.gap_capacity_lanes))
        .collect::<Vec<_>>();
    capacities.sort_unstable();
    let capacity_lanes = capacities.get(capacities.len() / 2).copied().unwrap_or(0);
    Ok(budget_aware_greedy_order(
        problem.fragment_domain.len(),
        &values,
        capacity_lanes,
    ))
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
            crate::BwdRegime::R0 => 0,
            crate::BwdRegime::Ext => 1,
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
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::sync::atomic::AtomicBool;
    use std::sync::{Arc, Barrier, Condvar, Mutex};

    use gkr_eval_ir::{
        BatchingOrder, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup, RootId,
        RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind, VirtualSetupKind,
    };

    use crate::bwd::distill::{DistilledLayer, distill};
    use crate::eval_plan::backward_search::problem::build_backward_search_problem;
    use crate::eval_plan::backward_search::solve_production_paging;
    use crate::eval_plan::search_driver::StableRng;

    use super::*;

    #[test]
    fn budget_aware_greedy_keeps_expensive_pairs_out_of_foreign_spans() {
        let values = vec![
            ProxyValue {
                width_lanes: 4,
                read_cost: 100,
                fragments: vec![0, 4],
            },
            ProxyValue {
                width_lanes: 4,
                read_cost: 100,
                fragments: vec![1, 3],
            },
            ProxyValue {
                width_lanes: 4,
                read_cost: 1,
                fragments: vec![0, 2],
            },
            ProxyValue {
                width_lanes: 4,
                read_cost: 1,
                fragments: vec![1, 2],
            },
        ];

        let order = budget_aware_greedy_order(5, &values, 4);

        assert_eq!(order.len(), 5);
        let position = |fragment| order.iter().position(|&item| item == fragment).unwrap();
        assert_eq!(position(0).abs_diff(position(4)), 1);
        assert_eq!(position(1).abs_diff(position(3)), 1);
    }

    #[test]
    fn budget_aware_seed_orders_are_stable_domain_permutations() {
        let (canonical, distilled) = shared_source_fixture();
        let (_, problem) = build_backward_search_problem(&canonical, &distilled, 8, 4).unwrap();
        let problem = problem.unwrap();

        let order = budget_aware_seed_order(&problem).unwrap();

        let expected = (0..problem.fragment_domain.len()).collect::<BTreeSet<_>>();
        assert_eq!(order.iter().copied().collect::<BTreeSet<_>>(), expected);
    }

    #[test]
    fn production_seed_selector_evaluates_only_constructive_and_distinct_previous() {
        let selected = select_fixture_seeds(None).unwrap();
        assert_eq!(selected.telemetry.evaluations, 1);
        assert_eq!(selected.telemetry.exact_solver_calls, 1);
        assert!(selected.telemetry.completed_tiers.is_empty());
        assert_eq!(
            selected.telemetry.solver_kinds,
            vec![ProductionPagingSolver::RetainAll]
        );
        assert_eq!(selected.telemetry.first_winning_ordinal, Some(0));
        assert!(selected.telemetry.improvement_ordinals.is_empty());
        assert_eq!(
            selected.telemetry.peak_dp_states,
            selected.candidate.paging.telemetry.peak_live_states
        );

        let mut previous = stable_indices_for(&selected.problem, &selected.problem.selected_order);
        let deduplicated = select_fixture_seeds(Some(&previous)).unwrap();
        assert_eq!(deduplicated.telemetry.evaluations, 1);
        assert_eq!(deduplicated.telemetry.exact_solver_calls, 1);

        previous.reverse();
        let selected = select_fixture_seeds(Some(&previous)).unwrap();
        assert_eq!(selected.telemetry.evaluations, 2);
        assert_eq!(selected.telemetry.exact_solver_calls, 2);
        assert!(selected.telemetry.evaluations <= 2);
        assert!(selected.telemetry.completed_tiers.is_empty());
        let winner = selected.telemetry.first_winning_ordinal.unwrap();
        assert!(winner < selected.telemetry.evaluations);
        assert_eq!(
            selected.telemetry.improvement_ordinals,
            if winner == 1 { vec![1] } else { Vec::new() }
        );
    }

    #[test]
    fn production_bypass_constructor_certifies_without_search_or_solver_calls() {
        let (canonical, distilled) = shared_source_fixture();
        let selected = construct_production_backward_bypass(&canonical, &distilled, 8, 2).unwrap();
        assert!(
            selected
                .candidate
                .paging
                .actions
                .iter()
                .all(|action| *action == PagingAction::Bypass)
        );
        assert_eq!(selected.telemetry, ProductionSearchTelemetry::default());
        assert_eq!(
            selected.order,
            stable_indices_for(&selected.problem, &selected.problem.selected_order),
        );
    }

    #[test]
    fn production_evaluation_permits_bound_actual_exact_work() {
        assert_eq!(
            run_concurrent_actual_evaluation_probe(16),
            MAX_CONCURRENT_PRODUCTION_EVALUATIONS
        );
    }

    #[test]
    fn production_evaluation_permits_release_after_actual_unwind() {
        let inject = Arc::new(AtomicBool::new(true));
        let observed = Arc::new(Mutex::new(Vec::new()));
        let hook = ProductionEvaluationTestHook::install({
            let inject = Arc::clone(&inject);
            let observed = Arc::clone(&observed);
            move |stage| {
                observed.lock().unwrap().push(stage);
                if stage == ProductionEvaluationTestStage::PermitAcquired
                    && inject.swap(false, Ordering::SeqCst)
                {
                    panic!("injected permit-held evaluation unwind");
                }
            }
        });
        let scope = hook.scope();
        let result = catch_unwind(AssertUnwindSafe(|| {
            with_production_evaluation_test_scope(scope, || select_fixture_seeds(None))
        }));
        assert!(result.is_err());
        let observed = observed
            .lock()
            .unwrap()
            .iter()
            .filter(|stage| **stage != ProductionEvaluationTestStage::PermitContended)
            .copied()
            .collect::<Vec<_>>();
        assert_eq!(
            observed,
            vec![
                ProductionEvaluationTestStage::WaitingForPermit,
                ProductionEvaluationTestStage::PermitAcquired,
                ProductionEvaluationTestStage::PermitReleasing,
            ]
        );
        drop(hook);

        assert_eq!(
            run_concurrent_actual_evaluation_probe(16),
            MAX_CONCURRENT_PRODUCTION_EVALUATIONS
        );
    }

    #[test]
    fn production_seed_selector_reports_nontrivial_exact_solver_telemetry() {
        let (canonical, distilled) = shared_source_fixture();
        let selected = select_production_backward_seeds(
            &test_identity(crate::BwdRegime::Ext),
            &canonical,
            &distilled,
            8,
            2,
            None,
        )
        .unwrap();
        assert_eq!(selected.telemetry.evaluations, 1);
        assert_eq!(selected.telemetry.exact_solver_calls, 1);
        assert_eq!(
            selected.telemetry.solver_kinds,
            vec![ProductionPagingSolver::RetainAll]
        );
        assert_eq!(
            selected.telemetry.peak_dp_states,
            selected.candidate.paging.telemetry.peak_live_states
        );
    }

    #[test]
    fn tier_telemetry_concurrent_snapshots_are_candidate_coherent() {
        let telemetry = Arc::new(TierTelemetry::default());
        telemetry.observe(ProductionPagingProgress {
            solver: ProductionPagingSolver::ResidentSets,
            current_states: 1_600,
            peak_states: 1_600,
        });
        let candidates = Arc::new(
            (0..SEARCH_BATCH)
                .map(|candidate| ProductionPagingProgress {
                    solver: match candidate % 3 {
                        0 => ProductionPagingSolver::RetainAll,
                        1 => ProductionPagingSolver::UniformIntervals,
                        _ => ProductionPagingSolver::ResidentSets,
                    },
                    current_states: candidate * 10 + 1,
                    peak_states: candidate * 10 + 7,
                })
                .collect::<Vec<_>>(),
        );
        let barrier = Arc::new(Barrier::new(SEARCH_BATCH + 1));
        let snapshots = Arc::new(Mutex::new(Vec::new()));
        let threads = candidates
            .iter()
            .copied()
            .map(|candidate| {
                let telemetry = Arc::clone(&telemetry);
                let barrier = Arc::clone(&barrier);
                let snapshots = Arc::clone(&snapshots);
                std::thread::spawn(move || {
                    barrier.wait();
                    for _ in 0..256 {
                        telemetry.observe(candidate);
                        std::thread::yield_now();
                        snapshots.lock().unwrap().push(telemetry.progress(128, 0));
                    }
                })
            })
            .collect::<Vec<_>>();
        barrier.wait();
        for thread in threads {
            thread.join().unwrap();
        }

        let snapshots = snapshots.lock().unwrap();
        assert_eq!(snapshots.len(), SEARCH_BATCH * 256);
        for snapshot in snapshots.iter() {
            assert!(snapshot.dp_states <= snapshot.peak_dp_states);
            assert!(
                candidates.iter().any(|candidate| {
                    snapshot.solver == Some(candidate.solver)
                        && snapshot.dp_states == candidate.current_states
                        && snapshot.peak_dp_states == candidate.peak_states
                }),
                "incoherent candidate snapshot: {snapshot:?}"
            );
        }
    }

    #[test]
    fn tier_telemetry_forwards_initial_live_and_one_second_updates() {
        let telemetry = TierTelemetry::default();
        let started = std::time::Instant::now();
        assert_eq!(
            telemetry.observe_progress_at(
                ProductionPagingProgress {
                    solver: ProductionPagingSolver::ResidentSets,
                    current_states: 0,
                    peak_states: 0,
                },
                128,
                0,
                started,
            ),
            None,
        );

        let first = ProductionPagingProgress {
            solver: ProductionPagingSolver::UniformIntervals,
            current_states: 5,
            peak_states: 8,
        };
        let first_snapshot = telemetry
            .observe_progress_at(first, 128, 0, started)
            .expect("first nonzero live event is always forwarded");
        assert_eq!(first_snapshot.solver, Some(first.solver));
        assert_eq!(first_snapshot.dp_states, first.current_states);
        assert_eq!(first_snapshot.peak_dp_states, first.peak_states);

        assert_eq!(
            telemetry.observe_progress_at(
                ProductionPagingProgress {
                    solver: ProductionPagingSolver::RetainAll,
                    current_states: 11,
                    peak_states: 13,
                },
                128,
                0,
                started + std::time::Duration::from_millis(999),
            ),
            None,
        );

        let boundary = ProductionPagingProgress {
            solver: ProductionPagingSolver::ResidentSets,
            current_states: 17,
            peak_states: 19,
        };
        let boundary_snapshot = telemetry
            .observe_progress_at(
                boundary,
                128,
                0,
                started + std::time::Duration::from_secs(1),
            )
            .expect("one-second boundary permits the next live event");
        assert_eq!(boundary_snapshot.solver, Some(boundary.solver));
        assert_eq!(boundary_snapshot.dp_states, boundary.current_states);
        assert_eq!(boundary_snapshot.peak_dp_states, boundary.peak_states);
    }

    #[test]
    fn tier_telemetry_samples_forwarding_time_under_the_paging_lock() {
        let telemetry = TierTelemetry::default();
        let snapshot = telemetry.observe_progress_with_clock(
            ProductionPagingProgress {
                solver: ProductionPagingSolver::ResidentSets,
                current_states: 23,
                peak_states: 29,
            },
            128,
            0,
            || {
                assert!(matches!(
                    telemetry.paging.try_lock(),
                    Err(std::sync::TryLockError::WouldBlock)
                ));
                std::time::Instant::now()
            },
        );
        assert!(snapshot.is_some());
    }

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
        let distilled = distill(&canonical, crate::BwdRegime::Ext, &HashMap::new(), None);
        let (_, initial) = build_backward_search_problem(&canonical, &distilled, 8, 4).unwrap();
        let initial = initial.unwrap();
        let mut preceding = stable_indices_for(&initial, &initial.selected_order);
        preceding.reverse();
        let result = search_production_backward(
            &test_identity(crate::BwdRegime::Ext),
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
        let (canonical, distilled) = shared_source_fixture();
        let snapshots = std::sync::Mutex::new(Vec::<ProductionSearchProgress>::new());
        let result = search_production_backward_with_progress(
            &test_identity(crate::BwdRegime::Ext),
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
        assert!(snapshots.iter().any(|snapshot| {
            snapshot.tier_completed == 0
                && snapshot.solver.is_some()
                && snapshot.dp_states > 0
                && snapshot.dp_states <= snapshot.peak_dp_states
        }));
    }

    #[test]
    fn preceding_budget_seed_is_scored_inside_the_fresh_tier() {
        let canonical = stable_domain_mismatch_paging_trivial_layer();
        let distilled = distill(&canonical, crate::BwdRegime::Ext, &HashMap::new(), None);
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
            production_identity_seed(&test_identity(crate::BwdRegime::Ext), 4),
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
        let distilled = distill(&canonical, crate::BwdRegime::Ext, &HashMap::new(), None);
        let result = search_production_backward(
            &test_identity(crate::BwdRegime::Ext),
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
        let identity = test_identity(crate::BwdRegime::R0);
        let seed = production_identity_seed(&identity, 4);
        assert_eq!(seed, 0xbbf2_c671_016e_083b);
        assert_eq!(seed, production_identity_seed(&identity, 4));
        assert_ne!(seed, production_identity_seed(&identity, 5));

        let mut changed = identity.clone();
        changed.circuit.push('x');
        assert_ne!(seed, production_identity_seed(&changed, 4));
        changed = identity.clone();
        changed.regime = crate::BwdRegime::Ext;
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

    fn test_identity(regime: crate::BwdRegime) -> ProductionSearchIdentity {
        ProductionSearchIdentity {
            circuit: "synthetic".to_owned(),
            layout_fixture: "synthetic_layout_gkr.json".to_owned(),
            layer: 0,
            regime,
        }
    }

    fn select_fixture_seeds(
        preceding_order: Option<&[usize]>,
    ) -> Result<ProductionBackwardPlan, BackwardSearchError> {
        let canonical = stable_domain_mismatch_paging_trivial_layer();
        let distilled = distill(&canonical, crate::BwdRegime::Ext, &HashMap::new(), None);
        select_production_backward_seeds(
            &test_identity(crate::BwdRegime::Ext),
            &canonical,
            &distilled,
            8,
            4,
            preceding_order,
        )
    }

    fn run_concurrent_actual_evaluation_probe(work: usize) -> usize {
        #[derive(Default)]
        struct ProbeState {
            waiting: usize,
            acquired: usize,
            contended: usize,
            active: usize,
            peak: usize,
            release_first_wave: bool,
            stages: HashMap<std::thread::ThreadId, Vec<ProductionEvaluationTestStage>>,
        }

        let state = Arc::new((Mutex::new(ProbeState::default()), Condvar::new()));
        let hook = ProductionEvaluationTestHook::install({
            let state = Arc::clone(&state);
            move |stage| {
                let thread = std::thread::current().id();
                let (state_lock, wake) = &*state;
                let mut state = state_lock.lock().unwrap();
                state.stages.entry(thread).or_default().push(stage);
                match stage {
                    ProductionEvaluationTestStage::WaitingForPermit => {
                        state.waiting += 1;
                        wake.notify_all();
                    }
                    ProductionEvaluationTestStage::PermitAcquired => {
                        state.acquired += 1;
                        state.active += 1;
                        state.peak = state.peak.max(state.active);
                        wake.notify_all();
                        if state.acquired <= MAX_CONCURRENT_PRODUCTION_EVALUATIONS {
                            while !state.release_first_wave {
                                state = wake.wait(state).unwrap();
                            }
                        }
                    }
                    ProductionEvaluationTestStage::PermitContended => {
                        state.contended += 1;
                        wake.notify_all();
                    }
                    ProductionEvaluationTestStage::PermitReleasing => {
                        state.active -= 1;
                    }
                    ProductionEvaluationTestStage::PagingCompleted
                    | ProductionEvaluationTestStage::CertificationCompleted => {}
                }
            }
        });
        let scope = hook.scope();
        let start = Arc::new(Barrier::new(work + 1));
        let threads = (0..work)
            .map(|_| {
                let start = Arc::clone(&start);
                std::thread::spawn(move || {
                    start.wait();
                    with_production_evaluation_test_scope(scope, || select_fixture_seeds(None))
                        .unwrap();
                })
            })
            .collect::<Vec<_>>();
        start.wait();

        let (state_lock, wake) = &*state;
        let state_guard = state_lock.lock().unwrap();
        let (state_guard, timeout) = wake
            .wait_timeout_while(state_guard, Duration::from_secs(5), |state| {
                state.waiting < work
                    || state.acquired < MAX_CONCURRENT_PRODUCTION_EVALUATIONS
                    || state.contended == 0
            })
            .unwrap();
        let timed_out = timeout.timed_out();
        let waiting_before_release = state_guard.waiting;
        let acquired_when_ready = state_guard.acquired;
        let active_when_ready = state_guard.active;
        let contended_before_release = state_guard.contended;
        let acquired_before_release = state_guard.acquired;
        let mut state_guard = state_guard;
        state_guard.release_first_wave = true;
        wake.notify_all();
        drop(state_guard);

        for thread in threads {
            thread.join().unwrap();
        }
        assert!(!timed_out, "four actual evaluations must acquire permits");
        assert_eq!(waiting_before_release, work);
        assert_eq!(acquired_when_ready, MAX_CONCURRENT_PRODUCTION_EVALUATIONS);
        assert_eq!(active_when_ready, MAX_CONCURRENT_PRODUCTION_EVALUATIONS);
        assert!(
            contended_before_release > 0,
            "at least one additional real evaluation must contend for a permit"
        );
        assert_eq!(
            acquired_before_release, MAX_CONCURRENT_PRODUCTION_EVALUATIONS,
            "no fifth actual evaluation may enter while four permits are held"
        );
        let state = state_lock.lock().unwrap();
        assert_eq!(state.acquired, work);
        assert_eq!(state.active, 0);
        assert_eq!(state.stages.len(), work);
        for stages in state.stages.values() {
            let permit_held_stages = stages
                .iter()
                .filter(|stage| {
                    !matches!(
                        stage,
                        ProductionEvaluationTestStage::WaitingForPermit
                            | ProductionEvaluationTestStage::PermitContended
                    )
                })
                .copied()
                .collect::<Vec<_>>();
            assert_eq!(
                permit_held_stages,
                vec![
                    ProductionEvaluationTestStage::PermitAcquired,
                    ProductionEvaluationTestStage::PagingCompleted,
                    ProductionEvaluationTestStage::CertificationCompleted,
                    ProductionEvaluationTestStage::PermitReleasing,
                ]
            );
        }
        state.peak
    }

    fn shared_source_fixture() -> (DagLayer, DistilledLayer) {
        let layer = synthetic_two_shared_sources_layer();
        let distilled = distill(&layer, crate::BwdRegime::Ext, &HashMap::new(), None);
        (layer, distilled)
    }

    fn stable_domain_mismatch_fixture() -> (DagLayer, DistilledLayer) {
        let mut layer = synthetic_two_shared_sources_layer();
        layer.roots.rotate_left(1);
        let distilled = distill(&layer, crate::BwdRegime::Ext, &HashMap::new(), None);
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
