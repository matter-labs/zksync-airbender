use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::time::{Duration, Instant};

use cs::gkr_compiler::dag_ir::{DagLayer, ExprId};

use crate::bwd::distill::DistilledLayer;
use crate::bwd::plan::{BwdOccurrencePlan, PlanAction, plan_entries_fnv};
use crate::bwd::trace::{BwdFingerprint, BwdServeKind};
use crate::eval_plan::search_driver::{
    SearchAdapter, SearchDriverConfig, SearchDriverError, SearchDriverOutcome, StableRng,
    run_search_driver,
};

use super::genome::{
    BackwardAdapter, BackwardAdapterTelemetry, BackwardAdapterTelemetrySnapshot, BackwardGenome,
    BackwardSearchArm, decode_fragment_order, paging_seed,
};
use super::pager::{
    ExactPagingPlan, PagerOutcome, PagingAction, PagingObjective, PagingTelemetry,
    solve_exact_paging,
};
use super::problem::{
    BackwardSearchProblem, ProblemClassification, StableFragmentKey, build_backward_search_problem,
    build_problem_for_order,
};
use super::{
    BackwardScore, BackwardSearchError, CertifiedBackwardCandidate, MAX_PAGER_STATES,
    ScoredAcceptedBackwardCandidate, compile_and_certify_paging, compile_and_score_occurrence_plan,
};

const SEARCH_POPULATION: usize = 32;
const SEARCH_BATCH: usize = 16;
const SEARCH_SEED: u64 = 0x706c_616e_332d_7437;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExperimentArm {
    Uncached,
    Incumbent,
    ExactConstructive,
    OrderSearch,
    CacheSearch,
    JointSearch,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArmClassification {
    Searched,
    Trivial {
        reason: &'static str,
    },
    Infeasible {
        reason: String,
    },
    SolverCapped {
        cap: usize,
        demand_position: usize,
        peak_states: usize,
    },
    UnavailableIncumbent,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PagerRunTelemetry {
    pub calls: usize,
    pub generated_states: u64,
    pub merged_states: u64,
    pub peak_states: usize,
}

#[derive(Clone, Debug)]
pub struct ArmResult {
    pub arm: ExperimentArm,
    pub classification: ArmClassification,
    pub score: Option<BackwardScore>,
    pub order: Option<Vec<usize>>,
    pub plan: Option<BwdOccurrencePlan>,
    pub first_winning_ordinal: Option<usize>,
    pub improvement_ordinals: Vec<usize>,
    pub evaluations: usize,
    pub pager: PagerRunTelemetry,
    pub compile_time: Duration,
    pub wall_time: Duration,
    pub winning_tier: Option<usize>,
}

#[derive(Clone, Debug)]
pub struct InstanceResult {
    pub fixture: String,
    pub layer_index: usize,
    pub budget_cells: usize,
    pub uncached: ArmResult,
    pub incumbent: ArmResult,
    pub arm1: ArmResult,
    pub arm2: ArmResult,
    pub arm3: ArmResult,
    pub arm4: ArmResult,
}

#[derive(Clone, Debug)]
pub struct AcceptedIncumbent {
    pub order: Vec<usize>,
    pub plan: BwdOccurrencePlan,
}

impl InstanceResult {
    /// Stable report digest. Timings are intentionally omitted because they are
    /// observational telemetry, not deterministic search output.
    pub fn deterministic_digest(&self) -> u64 {
        let mut digest = 0xcbf2_9ce4_8422_2325;
        digest_usize(&mut digest, self.fixture.len());
        digest_bytes(&mut digest, self.fixture.as_bytes());
        digest_usize(&mut digest, self.layer_index);
        digest_usize(&mut digest, self.budget_cells);
        for arm in [
            &self.uncached,
            &self.incumbent,
            &self.arm1,
            &self.arm2,
            &self.arm3,
            &self.arm4,
        ] {
            digest_arm(&mut digest, arm);
        }
        digest
    }
}

pub fn escalation_tiers(
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

pub fn run_instance(
    fixture: &str,
    layer_index: usize,
    canonical: &DagLayer,
    d: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
    incumbent: Option<&AcceptedIncumbent>,
) -> Result<InstanceResult, BackwardSearchError> {
    run_instance_with_pager_cap(
        fixture,
        layer_index,
        canonical,
        d,
        trace_len,
        budget_cells,
        incumbent,
        MAX_PAGER_STATES,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_instance_with_pager_cap(
    fixture: &str,
    layer_index: usize,
    canonical: &DagLayer,
    d: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
    incumbent: Option<&AcceptedIncumbent>,
    pager_cap: usize,
) -> Result<InstanceResult, BackwardSearchError> {
    let (classification, problem) =
        build_backward_search_problem(canonical, d, trace_len, budget_cells)?;
    let Some(problem) = problem else {
        let ProblemClassification::Infeasible {
            false_floor,
            true_floor,
        } = classification
        else {
            unreachable!("only infeasible problems omit the built problem")
        };
        let reason = format!(
            "budget {budget_cells} is below both mode floors ({false_floor}, {true_floor})"
        );
        return Ok(classified_instance(
            fixture,
            layer_index,
            budget_cells,
            ArmClassification::Infeasible { reason },
        ));
    };

    let uncached = run_uncached_reference(d, &problem)?;
    let incumbent_result =
        run_incumbent_reference(canonical, d, trace_len, budget_cells, incumbent)?;
    if let ProblemClassification::Trivial { reason } = classification {
        let classification = ArmClassification::Trivial { reason };
        return Ok(InstanceResult {
            fixture: fixture.to_owned(),
            layer_index,
            budget_cells,
            uncached,
            incumbent: incumbent_result,
            arm1: classified_arm(ExperimentArm::ExactConstructive, classification.clone()),
            arm2: classified_arm(ExperimentArm::OrderSearch, classification.clone()),
            arm3: classified_arm(ExperimentArm::CacheSearch, classification.clone()),
            arm4: classified_arm(ExperimentArm::JointSearch, classification),
        });
    }

    let arm1 = run_exact_constructive(d, &problem, pager_cap)?;
    let Some(arm1_score) = arm1.score else {
        let capped = arm1.classification.clone();
        return Ok(InstanceResult {
            fixture: fixture.to_owned(),
            layer_index,
            budget_cells,
            uncached,
            incumbent: incumbent_result,
            arm1,
            arm2: classified_arm(ExperimentArm::OrderSearch, capped.clone()),
            arm3: classified_arm(ExperimentArm::CacheSearch, capped.clone()),
            arm4: classified_arm(ExperimentArm::JointSearch, capped),
        });
    };
    let arm1_plan = arm1
        .plan
        .as_ref()
        .expect("scored exact arm carries its certified plan");
    let exact = exact_from_plan(&problem, arm1_plan)?;

    let arm2_tier = run_staged_search(
        canonical,
        d,
        &problem,
        &exact,
        trace_len,
        BackwardSearchArm::OrderOnly,
        vec![BackwardGenome::constructive(&problem)],
        arm1_score,
    )?;
    let arm2 = match arm2_tier {
        StagedOutcome::Completed(tier) => tier.into_arm_result(ExperimentArm::OrderSearch),
        StagedOutcome::Capped(classification, telemetry, wall_time) => capped_arm(
            ExperimentArm::OrderSearch,
            classification,
            telemetry,
            wall_time,
        ),
    };

    let arm3 = run_staged_search(
        canonical,
        d,
        &problem,
        &exact,
        trace_len,
        BackwardSearchArm::CacheOnly,
        vec![paging_seed(&problem, &exact)?],
        arm1_score,
    )?
    .into_arm_result_or_capped(ExperimentArm::CacheSearch);

    let arm4 = if arm2.score.is_some() {
        let arm2_seed = joint_seed_from_arm2(canonical, d, &problem, trace_len, &arm2)?;
        run_staged_search(
            canonical,
            d,
            &problem,
            &exact,
            trace_len,
            BackwardSearchArm::Joint,
            vec![paging_seed(&problem, &exact)?, arm2_seed],
            min_score(arm1_score, arm2.score.expect("checked above")),
        )?
        .into_arm_result_or_capped(ExperimentArm::JointSearch)
    } else {
        classified_arm(ExperimentArm::JointSearch, arm2.classification.clone())
    };

    Ok(InstanceResult {
        fixture: fixture.to_owned(),
        layer_index,
        budget_cells,
        uncached,
        incumbent: incumbent_result,
        arm1,
        arm2,
        arm3,
        arm4,
    })
}

fn run_uncached_reference(
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
) -> Result<ArmResult, BackwardSearchError> {
    let started = Instant::now();
    let paging = paging_from_actions(problem, vec![PagingAction::Bypass; problem.demands.len()])?;
    let telemetry = BackwardAdapterTelemetry::default();
    let compile_started = Instant::now();
    let candidate = compile_and_certify_paging(d, problem, &paging, 0);
    telemetry.record_compile_time(compile_started.elapsed());
    candidate_to_reference_result(
        ExperimentArm::Uncached,
        candidate?,
        problem.selected_order_indices.clone(),
        telemetry.snapshot(),
        started.elapsed(),
    )
}

fn run_incumbent_reference(
    canonical: &DagLayer,
    d: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
    incumbent: Option<&AcceptedIncumbent>,
) -> Result<ArmResult, BackwardSearchError> {
    let Some(incumbent) = incumbent.filter(|_| budget_cells == 4) else {
        return Ok(classified_arm(
            ExperimentArm::Incumbent,
            ArmClassification::UnavailableIncumbent,
        ));
    };
    let started = Instant::now();
    validate_full_order(&incumbent.order, d.fragments.fragments.len())?;
    let problem = build_problem_for_order(
        canonical,
        d,
        &incumbent.order,
        trace_len,
        budget_cells,
        incumbent.plan.stream_reductions,
    )?;
    let candidate =
        compile_and_score_occurrence_plan(d, &problem, &incumbent.plan, &incumbent.order, 0)?;
    Ok(accepted_candidate_to_reference_result(
        candidate,
        incumbent.order.clone(),
        started.elapsed(),
    ))
}

fn run_exact_constructive(
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    pager_cap: usize,
) -> Result<ArmResult, BackwardSearchError> {
    let telemetry = BackwardAdapterTelemetry::default();
    let started = Instant::now();
    let outcome = solve_exact_paging(&problem.demands, pager_cap)?;
    telemetry.record_pager(&outcome);
    let paging = match outcome {
        PagerOutcome::Solved(paging) => paging,
        PagerOutcome::SolverCapped {
            cap,
            demand_position,
            peak_states,
        } => {
            return Ok(capped_arm(
                ExperimentArm::ExactConstructive,
                ArmClassification::SolverCapped {
                    cap,
                    demand_position,
                    peak_states,
                },
                telemetry.snapshot(),
                started.elapsed(),
            ));
        }
    };
    let compile_started = Instant::now();
    let candidate = compile_and_certify_paging(d, problem, &paging, 0);
    telemetry.record_compile_time(compile_started.elapsed());
    candidate_to_reference_result(
        ExperimentArm::ExactConstructive,
        candidate?,
        problem.selected_order_indices.clone(),
        telemetry.snapshot(),
        started.elapsed(),
    )
}

struct SeededAdapter<'a> {
    inner: BackwardAdapter<'a>,
    seeds: Vec<BackwardGenome>,
}

impl SearchAdapter for SeededAdapter<'_> {
    type Genome = BackwardGenome;
    type Score = BackwardScore;
    type Evaluation = Option<CertifiedBackwardCandidate>;
    type Error = BackwardSearchError;
    type GuidedTrial = ();

    fn seeds(&self) -> Result<Vec<Self::Genome>, Self::Error> {
        Ok(self.seeds.clone())
    }

    fn parent_eligible(&self, score: &Self::Score) -> bool {
        self.inner.parent_eligible(score)
    }

    fn population_fill_seed(
        &self,
        seeds: &[Self::Genome],
        seed_scores: &[Self::Score],
        population_len: usize,
    ) -> Self::Genome {
        self.inner
            .population_fill_seed(seeds, seed_scores, population_len)
    }

    fn mutate(&self, genome: &mut Self::Genome, rng: &mut StableRng) {
        self.inner.mutate(genome, rng);
    }

    fn score_batch(
        &self,
        candidates: &[(usize, Self::Genome)],
    ) -> Vec<Result<(Self::Score, Self::Evaluation), Self::Error>> {
        self.inner.score_batch(candidates)
    }

    fn guided_trials(
        &self,
        pre_guided_best: &Self::Genome,
        pre_guided_evaluation: &Self::Evaluation,
    ) -> Vec<Self::GuidedTrial> {
        self.inner
            .guided_trials(pre_guided_best, pre_guided_evaluation)
    }

    fn apply_guided_trial(
        &self,
        trial: &Self::GuidedTrial,
        live_best: &Self::Genome,
        live_evaluation: &Self::Evaluation,
    ) -> Self::Genome {
        self.inner
            .apply_guided_trial(trial, live_best, live_evaluation)
    }
}

struct TierOutcome {
    outcome: SearchDriverOutcome<BackwardGenome, BackwardScore, Option<CertifiedBackwardCandidate>>,
    order: Vec<usize>,
    telemetry: BackwardAdapterTelemetrySnapshot,
    wall_time: Duration,
    tier: usize,
}

enum StagedOutcome {
    Completed(TierOutcome),
    Capped(
        ArmClassification,
        BackwardAdapterTelemetrySnapshot,
        Duration,
    ),
}

impl StagedOutcome {
    fn into_arm_result_or_capped(self, arm: ExperimentArm) -> ArmResult {
        match self {
            Self::Completed(tier) => tier.into_arm_result(arm),
            Self::Capped(classification, telemetry, wall_time) => {
                capped_arm(arm, classification, telemetry, wall_time)
            }
        }
    }
}

impl TierOutcome {
    fn into_arm_result(self, arm: ExperimentArm) -> ArmResult {
        let candidate = self
            .outcome
            .best_evaluation
            .expect("parent-eligible backward winner is certified");
        ArmResult {
            arm,
            classification: ArmClassification::Searched,
            score: Some(self.outcome.best_score),
            order: Some(self.order),
            plan: Some(candidate.occurrence_plan),
            first_winning_ordinal: Some(self.outcome.best_ordinal),
            improvement_ordinals: self.outcome.improvement_ordinals,
            evaluations: self.outcome.evaluations,
            pager: pager_telemetry(self.telemetry),
            compile_time: self.telemetry.compile_time,
            wall_time: self.wall_time,
            winning_tier: Some(self.tier),
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn run_staged_search(
    canonical: &DagLayer,
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    exact_seed: &ExactPagingPlan,
    trace_len: usize,
    arm: BackwardSearchArm,
    seeds: Vec<BackwardGenome>,
    seed_floor: BackwardScore,
) -> Result<StagedOutcome, BackwardSearchError> {
    let tier128 = match run_tier(
        canonical, d, problem, exact_seed, trace_len, arm, &seeds, 128,
    )? {
        StagedOutcome::Completed(tier) => tier,
        capped => return Ok(capped),
    };
    let improved_seed = score_key(tier128.outcome.best_score) < score_key(seed_floor);
    let late_winner = tier128.outcome.best_ordinal >= 96;
    if !improved_seed && !late_winner {
        return Ok(StagedOutcome::Completed(tier128));
    }

    let tier512 = match run_tier(
        canonical, d, problem, exact_seed, trace_len, arm, &seeds, 512,
    )? {
        StagedOutcome::Completed(tier) => tier,
        capped => return Ok(capped),
    };
    if score_key(tier512.outcome.best_score) >= score_key(tier128.outcome.best_score) {
        return Ok(StagedOutcome::Completed(tier512));
    }

    run_tier(
        canonical, d, problem, exact_seed, trace_len, arm, &seeds, 2048,
    )
}

#[allow(clippy::too_many_arguments)]
fn run_tier(
    canonical: &DagLayer,
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    exact_seed: &ExactPagingPlan,
    trace_len: usize,
    arm: BackwardSearchArm,
    seeds: &[BackwardGenome],
    evaluations: usize,
) -> Result<StagedOutcome, BackwardSearchError> {
    let telemetry = BackwardAdapterTelemetry::default();
    let adapter = SeededAdapter {
        inner: BackwardAdapter::new(canonical, d, problem, exact_seed, trace_len, arm)
            .with_telemetry(&telemetry),
        seeds: seeds.to_vec(),
    };
    let started = Instant::now();
    let outcome = run_search_driver(
        &adapter,
        SearchDriverConfig {
            population: SEARCH_POPULATION,
            evaluations,
            guided_evaluations: 0,
            score_batch: SEARCH_BATCH,
            seed: SEARCH_SEED,
        },
    );
    let wall_time = started.elapsed();
    let snapshot = telemetry.snapshot();
    match outcome {
        Ok(outcome) => {
            let order = order_from_genome(problem, &outcome.best_genome)?;
            Ok(StagedOutcome::Completed(TierOutcome {
                outcome,
                order,
                telemetry: snapshot,
                wall_time,
                tier: evaluations,
            }))
        }
        Err(SearchDriverError::Adapter(BackwardSearchError::ExactPagerSolverCapped {
            cap,
            demand_position,
            peak_states,
        })) => Ok(StagedOutcome::Capped(
            ArmClassification::SolverCapped {
                cap,
                demand_position,
                peak_states,
            },
            snapshot,
            wall_time,
        )),
        Err(SearchDriverError::Adapter(error)) => Err(error),
        Err(SearchDriverError::EmptySeeds) => Err(BackwardSearchError::SearchDriverFailure {
            reason: "empty backward search seeds",
        }),
        Err(SearchDriverError::InvalidConfig(reason)) => {
            Err(BackwardSearchError::SearchDriverFailure { reason })
        }
        Err(SearchDriverError::ScoreBatchLength { .. }) => {
            Err(BackwardSearchError::SearchDriverFailure {
                reason: "backward score batch length mismatch",
            })
        }
    }
}

fn joint_seed_from_arm2(
    canonical: &DagLayer,
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    trace_len: usize,
    arm2: &ArmResult,
) -> Result<BackwardGenome, BackwardSearchError> {
    let order = arm2
        .order
        .as_ref()
        .expect("scored order arm carries an order");
    let plan = arm2.plan.as_ref().expect("scored order arm carries a plan");
    let ordered_problem = build_problem_for_order(
        canonical,
        d,
        order,
        trace_len,
        problem.budget_cells,
        problem.stream_reductions,
    )?;
    let paging = exact_from_plan(&ordered_problem, plan)?;
    paging_seed(&ordered_problem, &paging)
}

fn order_from_genome(
    problem: &BackwardSearchProblem,
    genome: &BackwardGenome,
) -> Result<Vec<usize>, BackwardSearchError> {
    let original_indices = problem
        .selected_order
        .iter()
        .cloned()
        .zip(problem.selected_order_indices.iter().copied())
        .collect::<BTreeMap<StableFragmentKey, usize>>();
    decode_fragment_order(problem, genome)?
        .into_iter()
        .map(|key| {
            original_indices
                .get(&key)
                .copied()
                .ok_or(BackwardSearchError::InvalidGenomeDomain {
                    gene: "winning fragment order",
                })
        })
        .collect()
}

fn candidate_to_reference_result(
    arm: ExperimentArm,
    candidate: CertifiedBackwardCandidate,
    order: Vec<usize>,
    telemetry: BackwardAdapterTelemetrySnapshot,
    wall_time: Duration,
) -> Result<ArmResult, BackwardSearchError> {
    Ok(ArmResult {
        arm,
        classification: ArmClassification::Searched,
        score: Some(candidate.score),
        order: Some(order),
        plan: Some(candidate.occurrence_plan),
        first_winning_ordinal: Some(0),
        improvement_ordinals: Vec::new(),
        evaluations: 1,
        pager: pager_telemetry(telemetry),
        compile_time: telemetry.compile_time,
        wall_time,
        winning_tier: None,
    })
}

fn accepted_candidate_to_reference_result(
    candidate: ScoredAcceptedBackwardCandidate,
    order: Vec<usize>,
    wall_time: Duration,
) -> ArmResult {
    ArmResult {
        arm: ExperimentArm::Incumbent,
        classification: ArmClassification::Searched,
        score: Some(candidate.score),
        order: Some(order),
        plan: Some(candidate.occurrence_plan),
        first_winning_ordinal: Some(0),
        improvement_ordinals: Vec::new(),
        evaluations: 1,
        pager: PagerRunTelemetry::default(),
        compile_time: candidate.compile_time,
        wall_time,
        winning_tier: None,
    }
}

fn classified_instance(
    fixture: &str,
    layer_index: usize,
    budget_cells: usize,
    classification: ArmClassification,
) -> InstanceResult {
    InstanceResult {
        fixture: fixture.to_owned(),
        layer_index,
        budget_cells,
        uncached: classified_arm(ExperimentArm::Uncached, classification.clone()),
        incumbent: classified_arm(
            ExperimentArm::Incumbent,
            ArmClassification::UnavailableIncumbent,
        ),
        arm1: classified_arm(ExperimentArm::ExactConstructive, classification.clone()),
        arm2: classified_arm(ExperimentArm::OrderSearch, classification.clone()),
        arm3: classified_arm(ExperimentArm::CacheSearch, classification.clone()),
        arm4: classified_arm(ExperimentArm::JointSearch, classification),
    }
}

fn classified_arm(arm: ExperimentArm, classification: ArmClassification) -> ArmResult {
    ArmResult {
        arm,
        classification,
        score: None,
        order: None,
        plan: None,
        first_winning_ordinal: None,
        improvement_ordinals: Vec::new(),
        evaluations: 0,
        pager: PagerRunTelemetry::default(),
        compile_time: Duration::ZERO,
        wall_time: Duration::ZERO,
        winning_tier: None,
    }
}

fn capped_arm(
    arm: ExperimentArm,
    classification: ArmClassification,
    telemetry: BackwardAdapterTelemetrySnapshot,
    wall_time: Duration,
) -> ArmResult {
    let mut result = classified_arm(arm, classification);
    result.pager = pager_telemetry(telemetry);
    result.compile_time = telemetry.compile_time;
    result.wall_time = wall_time;
    result
}

fn pager_telemetry(snapshot: BackwardAdapterTelemetrySnapshot) -> PagerRunTelemetry {
    PagerRunTelemetry {
        calls: snapshot.pager_calls,
        generated_states: snapshot.pager_generated_states,
        merged_states: snapshot.pager_merged_states,
        peak_states: snapshot.pager_peak_states,
    }
}

fn validate_full_order(order: &[usize], fragments: usize) -> Result<(), BackwardSearchError> {
    if order.len() != fragments
        || order.iter().copied().collect::<BTreeSet<_>>().len() != fragments
        || order.iter().any(|&index| index >= fragments)
    {
        return Err(BackwardSearchError::InvalidGenomeDomain {
            gene: "accepted incumbent full-decomposition order",
        });
    }
    Ok(())
}

fn exact_from_plan(
    problem: &BackwardSearchProblem,
    plan: &BwdOccurrencePlan,
) -> Result<ExactPagingPlan, BackwardSearchError> {
    if plan.epoch != problem.epoch
        || plan.stream_reductions != problem.stream_reductions
        || plan.entries_fnv != plan_entries_fnv(&plan.entries)
        || plan.entries.len() != problem.all_domain_serves.len()
        || plan
            .entries
            .iter()
            .zip(&problem.all_domain_serves)
            .any(|(entry, fp)| entry.fp != *fp)
    {
        return Err(BackwardSearchError::PagingCertificateMismatch {
            observable: "accepted incumbent plan identity",
        });
    }
    let mut demands = BTreeMap::<FingerprintKey, VecDeque<usize>>::new();
    for (index, demand) in problem.demands.iter().enumerate() {
        demands
            .entry(demand.fp.into())
            .or_default()
            .push_back(index);
    }
    let mut actions = vec![PagingAction::Bypass; problem.demands.len()];
    for entry in &plan.entries {
        if let Some(index) = demands
            .get_mut(&entry.fp.into())
            .and_then(VecDeque::pop_front)
        {
            actions[index] = match entry.action {
                PlanAction::Bypass => PagingAction::Bypass,
                PlanAction::Retain => PagingAction::Retain,
            };
        } else if entry.action == PlanAction::Retain {
            return Err(BackwardSearchError::PagingCertificateMismatch {
                observable: "accepted incumbent non-leaf retain",
            });
        }
    }
    if demands.values().any(|queue| !queue.is_empty()) {
        return Err(BackwardSearchError::PagingCertificateMismatch {
            observable: "accepted incumbent leaf coverage",
        });
    }
    paging_from_actions(problem, actions)
}

fn paging_from_actions(
    problem: &BackwardSearchProblem,
    actions: Vec<PagingAction>,
) -> Result<ExactPagingPlan, BackwardSearchError> {
    if actions.len() != problem.demands.len() {
        return Err(BackwardSearchError::PagingActionCount {
            expected: problem.demands.len(),
            actual: actions.len(),
        });
    }
    let mut residents = BTreeMap::<ExprId, u8>::new();
    let mut live_lanes_after = Vec::with_capacity(actions.len());
    let mut objective = PagingObjective::default();
    let mut misses = 0u32;
    let mut peak_live_lanes = 0u8;
    for (position, (demand, action)) in problem.demands.iter().zip(&actions).enumerate() {
        if residents.remove(&demand.expr).is_some() {
            objective.evictions = objective
                .evictions
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
        } else {
            misses = misses
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
            objective.dram_bytes = objective
                .dram_bytes
                .checked_add(demand.miss_cost.dram_bytes()?)
                .ok_or(BackwardSearchError::CostOverflow)?;
            objective.primitive_source_ops = objective
                .primitive_source_ops
                .checked_add(demand.miss_cost.ops.primitive_equivalents()?)
                .ok_or(BackwardSearchError::CostOverflow)?;
        }
        if *action == PagingAction::Retain {
            if !demand.has_next {
                return Err(BackwardSearchError::CacheGenomeInfeasible {
                    demand_position: position,
                });
            }
            residents.insert(demand.expr, demand.width_lanes);
            objective.admissions = objective
                .admissions
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
        }
        let live = residents.values().try_fold(0u8, |total, width| {
            total
                .checked_add(*width)
                .ok_or(BackwardSearchError::CostOverflow)
        })?;
        if live > demand.gap_capacity_lanes {
            return Err(BackwardSearchError::CacheGenomeInfeasible {
                demand_position: position,
            });
        }
        peak_live_lanes = peak_live_lanes.max(live);
        live_lanes_after.push(live);
    }
    Ok(ExactPagingPlan {
        actions,
        live_lanes_after,
        objective,
        predicted_misses: misses,
        refused_retains: 0,
        telemetry: PagingTelemetry {
            peak_live_lanes,
            ..PagingTelemetry::default()
        },
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FingerprintKey {
    term: u32,
    kind: u8,
    value: u32,
    consumer: Option<u32>,
}

impl From<BwdFingerprint> for FingerprintKey {
    fn from(fp: BwdFingerprint) -> Self {
        Self {
            term: fp.term,
            kind: match fp.kind {
                BwdServeKind::RootOutput => 0,
                BwdServeKind::Operand => 1,
            },
            value: fp.value.0,
            consumer: fp.consumer.map(|consumer| consumer.0),
        }
    }
}

fn min_score(left: BackwardScore, right: BackwardScore) -> BackwardScore {
    if score_key(left) <= score_key(right) {
        left
    } else {
        right
    }
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

fn digest_arm(digest: &mut u64, result: &ArmResult) {
    digest_usize(digest, result.arm as usize);
    digest_classification(digest, &result.classification);
    if let Some(score) = result.score {
        digest_usize(digest, 1);
        digest_usize(digest, usize::from(score.infeasible));
        digest_bytes(digest, &score.whole_pass_dram_bytes.to_le_bytes());
        digest_bytes(digest, &score.primitive_source_ops.to_le_bytes());
        for value in [
            score.instructions,
            score.encoded_lanes,
            score.arithmetic_ops,
            score.ordinal,
        ] {
            digest_usize(digest, value);
        }
    } else {
        digest_usize(digest, 0);
    }
    if let Some(order) = &result.order {
        digest_usize(digest, 1);
        digest_usize(digest, order.len());
        for value in order {
            digest_usize(digest, *value);
        }
    } else {
        digest_usize(digest, 0);
    }
    if let Some(plan) = &result.plan {
        digest_usize(digest, 1);
        digest_bytes(digest, &plan.epoch.to_le_bytes());
        digest_bytes(digest, &plan.entries_fnv.to_le_bytes());
        digest_usize(digest, usize::from(plan.stream_reductions));
        digest_usize(digest, plan.entries.len());
    } else {
        digest_usize(digest, 0);
    }
    digest_usize(digest, result.first_winning_ordinal.unwrap_or(usize::MAX));
    digest_usize(digest, result.improvement_ordinals.len());
    for &ordinal in &result.improvement_ordinals {
        digest_usize(digest, ordinal);
    }
    for value in [
        result.evaluations,
        result.pager.calls,
        result.pager.peak_states,
        result.winning_tier.unwrap_or(0),
    ] {
        digest_usize(digest, value);
    }
    digest_bytes(digest, &result.pager.generated_states.to_le_bytes());
    digest_bytes(digest, &result.pager.merged_states.to_le_bytes());
}

fn digest_classification(digest: &mut u64, classification: &ArmClassification) {
    match classification {
        ArmClassification::Searched => digest_usize(digest, 0),
        ArmClassification::Trivial { reason } => {
            digest_usize(digest, 1);
            digest_usize(digest, reason.len());
            digest_bytes(digest, reason.as_bytes());
        }
        ArmClassification::Infeasible { reason } => {
            digest_usize(digest, 2);
            digest_usize(digest, reason.len());
            digest_bytes(digest, reason.as_bytes());
        }
        ArmClassification::SolverCapped {
            cap,
            demand_position,
            peak_states,
        } => {
            digest_usize(digest, 3);
            digest_usize(digest, *cap);
            digest_usize(digest, *demand_position);
            digest_usize(digest, *peak_states);
        }
        ArmClassification::UnavailableIncumbent => digest_usize(digest, 4),
    }
}

fn digest_usize(digest: &mut u64, value: usize) {
    digest_bytes(digest, &value.to_le_bytes());
}

fn digest_bytes(digest: &mut u64, bytes: &[u8]) {
    for byte in bytes {
        *digest = (*digest ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet, HashMap};

    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup,
        RootId, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
    };

    use crate::bwd::compile::FragmentBackend;
    use crate::bwd::construct::construct_fragment_order;
    use crate::bwd::distill::stable_distilled_site_domain;
    use crate::bwd::distill::{DistilledLayer, distill};
    use crate::bwd::fif::coordinate_correct_frozen_with_backend;
    use crate::bwd::plan::PlanAction;
    use crate::bwd::price::compound_batch_plan;

    use super::{
        AcceptedIncumbent, ArmClassification, InstanceResult, escalation_tiers, run_instance,
        run_instance_with_pager_cap,
    };

    #[test]
    fn every_searched_arm_keeps_its_required_exact_incumbent() {
        let result = run_synthetic_instance().unwrap();
        assert!(result.arm2.score <= result.arm1.score);
        assert!(result.arm3.score <= result.arm1.score);
        assert!(result.arm4.score <= result.arm2.score);
    }

    #[test]
    fn tier_escalation_matches_the_approved_rules() {
        assert_eq!(escalation_tiers(false, false, false), vec![128]);
        assert_eq!(escalation_tiers(true, false, false), vec![128, 512]);
        assert_eq!(escalation_tiers(false, true, false), vec![128, 512]);
        assert_eq!(escalation_tiers(true, false, true), vec![128, 512, 2048]);
    }

    #[test]
    fn capped_required_seed_caps_dependent_arm_without_substitution() {
        let result = run_with_pager_cap(1).unwrap();
        assert!(matches!(
            result.arm1.classification,
            ArmClassification::SolverCapped { .. }
        ));
        assert!(matches!(
            result.arm2.classification,
            ArmClassification::SolverCapped { .. }
        ));
        assert!(result.arm1.score.is_none());
        assert!(result.arm2.score.is_none());
    }

    #[test]
    fn arm3_primary_delta_is_definitionally_zero() {
        let result = run_synthetic_instance().unwrap();
        assert_eq!(
            result.arm3.score.unwrap().whole_pass_dram_bytes,
            result.arm1.score.unwrap().whole_pass_dram_bytes
        );
    }

    #[test]
    fn searched_arm_telemetry_is_complete_and_auditable() {
        let result = run_synthetic_instance().unwrap();
        for arm in [&result.arm2, &result.arm3, &result.arm4] {
            assert!(matches!(arm.winning_tier, Some(128 | 512 | 2048)));
            assert_eq!(arm.evaluations, arm.winning_tier.unwrap());
            assert!(arm.first_winning_ordinal.unwrap() < arm.evaluations);
            assert!(
                arm.improvement_ordinals
                    .iter()
                    .all(|&ordinal| ordinal < arm.evaluations)
            );
        }
        assert_eq!(result.arm2.pager.calls, result.arm2.evaluations);
        assert_eq!(result.arm3.pager.calls, 0);
        assert_eq!(result.arm4.pager.calls, 0);
    }

    #[test]
    fn accepted_c4_incumbent_replays_but_other_budgets_do_not_compile_it() {
        let first = run_synthetic_instance().unwrap();
        assert!(matches!(
            first.incumbent.classification,
            ArmClassification::UnavailableIncumbent
        ));
        let incumbent = AcceptedIncumbent {
            order: first.arm1.order.clone().unwrap(),
            plan: first.arm1.plan.clone().unwrap(),
        };
        let (layer, distilled) = synthetic_fixture();
        let c4 = run_instance("synthetic", 0, &layer, &distilled, 8, 4, Some(&incumbent)).unwrap();
        assert_eq!(c4.incumbent.score, first.arm1.score);

        let c3 = run_instance("synthetic", 0, &layer, &distilled, 8, 3, Some(&incumbent)).unwrap();
        assert!(matches!(
            c3.incumbent.classification,
            ArmClassification::UnavailableIncumbent
        ));
        let c2 = run_instance("synthetic", 0, &layer, &distilled, 8, 2, Some(&incumbent)).unwrap();
        assert!(matches!(
            c2.incumbent.classification,
            ArmClassification::UnavailableIncumbent
        ));
        assert_eq!(c2.incumbent.evaluations, 0);
        assert_eq!(c3.incumbent.evaluations, 0);
    }

    #[test]
    fn stale_incumbent_plan_remains_an_error() {
        let first = run_synthetic_instance().unwrap();
        let mut plan = first.arm1.plan.clone().unwrap();
        plan.epoch ^= 1;
        let incumbent = AcceptedIncumbent {
            order: first.arm1.order.clone().unwrap(),
            plan,
        };
        let (layer, distilled) = synthetic_fixture();
        assert!(run_instance("synthetic", 0, &layer, &distilled, 8, 4, Some(&incumbent),).is_err());
    }

    #[test]
    fn compound_retaining_incumbent_is_replayed_without_leaf_projection() {
        let (layer, distilled) = synthetic_shared_compound_fixture();
        let order = construct_fragment_order(
            &layer,
            &distilled,
            &stable_distilled_site_domain(&distilled),
        );
        let frozen = coordinate_correct_frozen_with_backend(
            &distilled,
            16,
            &FragmentBackend {
                order: order.clone(),
            },
        )
        .unwrap();
        let mut counts = BTreeMap::new();
        for (fp, _) in &frozen.domain_serves {
            *counts.entry(fp.value).or_insert(0usize) += 1;
        }
        let compound = counts
            .into_iter()
            .find_map(|(value, count)| {
                (count >= 2 && !matches!(distilled.layer.exprs[value.0 as usize], Expr::Source(_)))
                    .then_some(value)
            })
            .expect("fixture has a repeated compound serve");
        let plan = compound_batch_plan(&frozen, &BTreeSet::from([compound]));
        assert!(
            plan.entries
                .iter()
                .any(|entry| { entry.fp.value == compound && entry.action == PlanAction::Retain })
        );
        let incumbent = AcceptedIncumbent { order, plan };
        let result =
            run_instance("compound", 0, &layer, &distilled, 8, 4, Some(&incumbent)).unwrap();
        assert!(result.incumbent.score.is_some());
        assert!(matches!(
            result.incumbent.classification,
            ArmClassification::Searched
        ));
    }

    #[test]
    fn deterministic_digest_excludes_all_timing_fields() {
        let result = run_synthetic_instance().unwrap();
        let mut retimed = result.clone();
        for arm in [
            &mut retimed.uncached,
            &mut retimed.incumbent,
            &mut retimed.arm1,
            &mut retimed.arm2,
            &mut retimed.arm3,
            &mut retimed.arm4,
        ] {
            arm.compile_time += std::time::Duration::from_secs(3);
            arm.wall_time += std::time::Duration::from_secs(7);
        }
        assert_eq!(
            result.deterministic_digest(),
            retimed.deterministic_digest()
        );
    }

    #[test]
    fn search_is_thread_deterministic() {
        let result = run_synthetic_instance().unwrap();
        println!("PLAN3-SEARCH-DIGEST {:016x}", result.deterministic_digest());
    }

    fn run_synthetic_instance() -> Result<InstanceResult, super::BackwardSearchError> {
        let (layer, distilled) = synthetic_fixture();
        run_instance("synthetic", 0, &layer, &distilled, 8, 4, None)
    }

    fn run_with_pager_cap(cap: usize) -> Result<InstanceResult, super::BackwardSearchError> {
        let (layer, distilled) = synthetic_fixture();
        run_instance_with_pager_cap("synthetic", 0, &layer, &distilled, 8, 4, None, cap)
    }

    fn synthetic_fixture() -> (DagLayer, DistilledLayer) {
        let layer = synthetic_two_shared_sources_layer();
        let distilled = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
        (layer, distilled)
    }

    fn synthetic_shared_compound_fixture() -> (DagLayer, DistilledLayer) {
        let mut sources = Vec::new();
        let mut exprs = Vec::new();
        let mut read = || {
            let source = SourceId(sources.len() as u32);
            sources.push(read_source(sources.len()));
            let expr = ExprId(exprs.len() as u32);
            exprs.push(Expr::Source(source));
            expr
        };
        let ru0 = read();
        let ru1 = read();
        let rw = read();
        let rv = read();
        let ra = read();
        let rb = read();
        let rc = read();
        let rd = read();
        let mut add = |expr: Expr| {
            let id = ExprId(exprs.len() as u32);
            exprs.push(expr);
            id
        };
        let u = add(Expr::Add(vec![ru0, ru1]));
        let w = add(Expr::Mul(vec![u, rw]));
        let v = add(Expr::Mul(vec![w, rv]));
        let m_va = add(Expr::Mul(vec![v, ra]));
        let m_vb = add(Expr::Mul(vec![v, rb]));
        let m_wc = add(Expr::Mul(vec![w, rc]));
        let m_ud = add(Expr::Mul(vec![u, rd]));
        let root = add(Expr::Add(vec![m_va, m_vb, m_wc, m_ud]));
        let layer = DagLayer {
            sources,
            exprs,
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            roots: vec![claim_root(root, 0)],
            resolutions: BTreeMap::new(),
        };
        let distilled = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
        (layer, distilled)
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
