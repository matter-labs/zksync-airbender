use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::sync::Mutex;

use super::search_driver::{
    SearchAdapter, SearchDriverConfig, SearchDriverError, StableRng, run_search_driver,
};
use super::{
    EvaluationGenome, FitnessError, PlacementStatus, PlanFitness, PlanSearchContext,
    ScoredEvaluation, ValueFingerprint,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MutationSearchConfig {
    pub population: usize,
    pub evaluations: usize,
    /// Additional evaluations reserved for ready-frontier/staging refinement
    /// after cache and root-order search has selected its winner.
    pub staging_evaluations: usize,
    pub seed: u64,
    /// Number of independently selected cache genes nudged in each offspring.
    pub cache_mutations: usize,
}

impl Default for MutationSearchConfig {
    fn default() -> Self {
        Self {
            population: 16,
            evaluations: 512,
            staging_evaluations: 64,
            seed: 0,
            cache_mutations: 2,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum MutationSearchError {
    InvalidConfig(&'static str),
    Fitness(FitnessError),
}

impl From<FitnessError> for MutationSearchError {
    fn from(value: FitnessError) -> Self {
        Self::Fitness(value)
    }
}

pub struct MutationSearchOutcome {
    pub neutral_fitness: PlanFitness,
    pub retentive_fitness: PlanFitness,
    pub best_genome: EvaluationGenome,
    pub best: ScoredEvaluation,
    pub evaluations: usize,
    pub telemetry: SearchTelemetry,
}

pub struct StagingRefinementOutcome {
    pub best_genome: EvaluationGenome,
    pub best: ScoredEvaluation,
    pub evaluations: usize,
    pub improvements: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SearchTelemetry {
    pub guided_evaluations: usize,
    pub guided_improvements: usize,
    pub guided_order_evaluations: usize,
    pub guided_order_improvements: usize,
    pub staging_evaluations: usize,
    pub staging_improvements: usize,
    pub greedy_placed: usize,
    pub relocation_placed: usize,
    pub exact_attempts: usize,
    pub exact_successes: usize,
    pub exact_failures: usize,
    pub exact_skipped: usize,
    pub placement_infeasible: usize,
    pub elaboration_infeasible: usize,
    pub ext_nodes: u64,
    pub base_nodes: u64,
}

impl SearchTelemetry {
    fn record(&mut self, scored: &ScoredEvaluation) {
        self.ext_nodes += scored.placement_telemetry.ext_nodes;
        self.base_nodes += scored.placement_telemetry.base_nodes;
        match scored.placement {
            PlacementStatus::Concrete if scored.placement_telemetry.relocation_fallback => {
                self.relocation_placed += 1;
                if scored.placement_telemetry.exact_attempted {
                    self.exact_attempts += 1;
                    self.exact_failures += 1;
                }
            }
            PlacementStatus::Concrete if scored.placement_telemetry.exact_attempted => {
                self.exact_attempts += 1;
                self.exact_successes += 1;
            }
            PlacementStatus::Concrete => self.greedy_placed += 1,
            PlacementStatus::Unverified => self.exact_skipped += 1,
            PlacementStatus::PlacementInfeasible => {
                self.exact_attempts += 1;
                self.exact_failures += 1;
                self.placement_infeasible += 1;
            }
            PlacementStatus::ElaborationInfeasible => self.elaboration_infeasible += 1,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct ForwardScore {
    fitness: PlanFitness,
    parent_eligible: bool,
}

impl PartialEq for ForwardScore {
    fn eq(&self, other: &Self) -> bool {
        self.fitness == other.fitness
    }
}

impl Eq for ForwardScore {}

impl PartialOrd for ForwardScore {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ForwardScore {
    fn cmp(&self, other: &Self) -> Ordering {
        self.fitness.cmp(&other.fitness)
    }
}

#[derive(Default)]
struct ForwardAdapterState {
    incumbent_fitness: Option<PlanFitness>,
    seed_fitness: Vec<PlanFitness>,
    telemetry: SearchTelemetry,
    guided_order: Vec<bool>,
}

struct ForwardSearchAdapter<'a, 'ctx> {
    context: &'a PlanSearchContext<'ctx>,
    cache_mutations: usize,
    state: Mutex<ForwardAdapterState>,
}

impl SearchAdapter for ForwardSearchAdapter<'_, '_> {
    type Genome = EvaluationGenome;
    type Score = ForwardScore;
    type Evaluation = ScoredEvaluation;
    type Error = FitnessError;
    type GuidedTrial = GuidedTrial;

    fn seeds(&self) -> Result<Vec<Self::Genome>, Self::Error> {
        Ok(vec![
            EvaluationGenome::neutral(self.context),
            EvaluationGenome::retentive(self.context),
        ])
    }

    fn parent_eligible(&self, score: &Self::Score) -> bool {
        score.parent_eligible
    }

    fn population_fill_seed(
        &self,
        seeds: &[Self::Genome],
        seed_scores: &[Self::Score],
        population_len: usize,
    ) -> Self::Genome {
        if seed_scores[1].parent_eligible && population_len & 1 != 0 {
            seeds[1].clone()
        } else {
            seeds[0].clone()
        }
    }

    fn mutate(&self, genome: &mut Self::Genome, rng: &mut StableRng) {
        mutate(genome, self.cache_mutations, rng);
    }

    fn score_batch(
        &self,
        candidates: &[(usize, Self::Genome)],
    ) -> Vec<Result<(Self::Score, Self::Evaluation), Self::Error>> {
        let mut state = self.state.lock().expect("forward search adapter lock");
        candidates
            .iter()
            .map(|(ordinal, genome)| {
                let scored = if *ordinal < 2 {
                    self.context.score(genome)
                } else {
                    self.context.score_for_search(
                        genome,
                        state
                            .incumbent_fitness
                            .expect("neutral seed establishes incumbent fitness"),
                    )
                }?;
                state.telemetry.record(&scored);
                if *ordinal < 2 {
                    state.seed_fitness.push(scored.fitness);
                }
                let parent_eligible =
                    *ordinal == 0 || scored.placement == PlacementStatus::Concrete;
                if state.incumbent_fitness.is_none()
                    || (parent_eligible
                        && scored.fitness
                            < state
                                .incumbent_fitness
                                .expect("checked incumbent fitness is present"))
                {
                    state.incumbent_fitness = Some(scored.fitness);
                }
                Ok((
                    ForwardScore {
                        fitness: scored.fitness,
                        parent_eligible,
                    },
                    scored,
                ))
            })
            .collect()
    }

    fn guided_trials(
        &self,
        pre_guided_best: &Self::Genome,
        pre_guided_evaluation: &Self::Evaluation,
    ) -> Vec<Self::GuidedTrial> {
        let trials = guided_trials(self.context, pre_guided_evaluation, pre_guided_best);
        self.state
            .lock()
            .expect("forward search adapter lock")
            .guided_order = trials
            .iter()
            .map(|trial| matches!(trial, GuidedTrial::Order { .. }))
            .collect();
        trials
    }

    fn apply_guided_trial(
        &self,
        trial: &Self::GuidedTrial,
        live_best: &Self::Genome,
        _live_evaluation: &Self::Evaluation,
    ) -> Self::Genome {
        let mut genome = live_best.clone();
        match trial {
            GuidedTrial::Order { moving, anchor } => {
                move_unit_after(&mut genome.root_order_key, *moving, *anchor);
            }
            GuidedTrial::Cache { index, target } => {
                genome.cache_priority[*index] = *target;
            }
        }
        genome
    }
}

/// Deterministic sparse-mutation evolutionary search.
///
/// The population starts with the no-cache neutral genome and, when concretely
/// placeable, the backing-leaf-retentive baseline, then sparse mutations of those
/// feasible seeds. An infeasible retentive baseline is still measured and
/// reported, but is not used as a parent: sparse mutations cannot efficiently
/// repair a genome that exceeds the physical lane budget in many places.
/// Each subsequent candidate mutates a two-way tournament winner, optionally
/// swapping two unit-order keys and nudging a fixed number of cache genes. The
/// parent and offspring compete in one elitist population, so the best score is
/// monotonic. This deliberately small driver validates the genome/fitness loop;
/// crossover and parallel scoring can be added after real-layer measurements.
pub fn mutation_search(
    context: &PlanSearchContext<'_>,
    config: MutationSearchConfig,
) -> Result<MutationSearchOutcome, MutationSearchError> {
    validate_config(config)?;
    let guided_budget = if config.evaluations >= 128 {
        // Once a concrete incumbent exists, replay attribution is substantially
        // denser signal than sparse random mutation: one guided evaluation can
        // name the exact future demand that closes a recomputation interval.
        // Very wide root-order spaces still need more population diversity;
        // otherwise use the final half to cover more than the first handful of
        // intervals. The 128-evaluation cap keeps larger runs from displacing
        // broad mutation.
        let divisor = if context.materialized_roots().len() > config.evaluations.saturating_mul(4) {
            4
        } else {
            2
        };
        (config.evaluations / divisor).min(128)
    } else {
        0
    };
    let adapter = ForwardSearchAdapter {
        context,
        cache_mutations: config.cache_mutations,
        state: Mutex::new(ForwardAdapterState::default()),
    };
    let outcome = run_search_driver(
        &adapter,
        SearchDriverConfig {
            population: config.population,
            evaluations: config.evaluations,
            guided_evaluations: guided_budget,
            score_batch: 1,
            seed: config.seed,
        },
    )
    .map_err(|error| match error {
        SearchDriverError::Adapter(error) => MutationSearchError::Fitness(error),
        SearchDriverError::InvalidConfig(message) => MutationSearchError::InvalidConfig(message),
        SearchDriverError::EmptySeeds => {
            MutationSearchError::InvalidConfig("forward search adapter produced no seeds")
        }
        SearchDriverError::ScoreBatchLength { .. } => {
            MutationSearchError::InvalidConfig("forward score batch returned the wrong length")
        }
    })?;
    let mut best_genome = outcome.best_genome;
    let mut best = outcome.best_evaluation;
    let evaluations = outcome.evaluations;
    let state = adapter
        .state
        .into_inner()
        .expect("forward search adapter lock");
    let [neutral_fitness, retentive_fitness] = state
        .seed_fitness
        .try_into()
        .expect("forward adapter always evaluates two seeds");
    let mut telemetry = state.telemetry;
    telemetry.guided_evaluations = guided_budget;
    telemetry.guided_order_evaluations = state
        .guided_order
        .iter()
        .take(outcome.guided_candidates)
        .filter(|guided_order| **guided_order)
        .count();
    telemetry.guided_improvements = outcome.guided_improvement_ordinals.len();
    let evolutionary_limit = config.evaluations - guided_budget;
    telemetry.guided_order_improvements = outcome
        .guided_improvement_ordinals
        .iter()
        .filter(|ordinal| {
            let guided_index = **ordinal - evolutionary_limit;
            state
                .guided_order
                .get(guided_index)
                .copied()
                .unwrap_or(false)
        })
        .count();

    // Intermediate candidates use a cheap relocating certificate after greedy
    // fixed placement. Rebind only the selected genome through the complete
    // fixed two-pass search, falling back to moves only if that also fails.
    best = context.score(&best_genome)?;

    if config.staging_evaluations != 0 {
        let refined = staging_refinement(context, &best_genome, config.staging_evaluations)?;
        telemetry.staging_evaluations = refined.evaluations;
        telemetry.staging_improvements = refined.improvements;
        best_genome = refined.best_genome;
        best = refined.best;
    }

    Ok(MutationSearchOutcome {
        neutral_fitness,
        retentive_fitness,
        best_genome,
        best,
        evaluations,
        telemetry,
    })
}

/// Explicitly-budgeted subset refinement over the sparse computed staging
/// domain. Candidates whose enclosing operation was observed as an unfused
/// additive product are tried first. Complete ready-at-entry frontiers are
/// evaluated before up to twelve candidates are explored in increasing subset
/// cardinality. This captures both legacy-style whole-op readiness and
/// deliberate splitting without making the domain exponential at corpus scale.
/// `mutation_search` invokes this with a separate explicit budget after its
/// cache/root-order winner is fixed, so staging never displaces those trials.
pub fn staging_refinement(
    context: &PlanSearchContext<'_>,
    genome: &EvaluationGenome,
    limit: usize,
) -> Result<StagingRefinementOutcome, MutationSearchError> {
    let mut best_genome = genome.clone();
    let mut best = context.score(&best_genome)?;
    let mut weights = BTreeMap::<ValueFingerprint, usize>::new();
    if let Some(plan) = &best.plan {
        for (&expr, attribution) in &plan.attribution {
            let unfused = attribution
                .additive_demands
                .saturating_sub(attribution.fma_fusions);
            if unfused != 0 {
                weights.insert(context.expression_fingerprint(expr), unfused);
            }
        }
    }
    let mut candidates = context
        .site_index()
        .staging_pairs()
        .iter()
        .enumerate()
        .filter(|(index, _)| best_genome.staging_priority[*index] <= 0.0)
        .map(|(index, pair)| {
            let suffix = &pair.staged.path[pair.boundary.path.len()..];
            let enclosing_value = if suffix.len() >= 2
                && suffix[0].operation == super::ReductionOp::Add
                && suffix[1].operation == super::ReductionOp::Mul
            {
                suffix[0].child
            } else {
                pair.boundary.value
            };
            (index, weights.get(&enclosing_value).copied().unwrap_or(0))
        })
        .collect::<Vec<_>>();
    candidates.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    // A fused instruction is a frontier decision, not merely a collection of
    // unrelated value decisions. Try every complete boundary frontier first;
    // individual/subset trials below can still choose a deliberate split.
    let pairs = context.site_index().staging_pairs();
    let mut frontiers = Vec::<(usize, usize, Vec<usize>)>::new();
    for &(index, weight) in &candidates {
        let pair = &pairs[index];
        if let Some((_, total_weight, members)) = frontiers
            .iter_mut()
            .find(|(representative, _, _)| pairs[*representative].boundary == pair.boundary)
        {
            *total_weight += weight;
            members.push(index);
        } else {
            frontiers.push((index, weight, vec![index]));
        }
    }
    frontiers.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    let mut trials = Vec::<Vec<usize>>::new();
    let mut seen_trials = BTreeSet::new();
    let frontier_limit = (limit / 4).min(8);
    for (_, _, mut members) in frontiers
        .into_iter()
        .filter(|(_, weight, members)| *weight != 0 && members.len() > 1)
        .take(frontier_limit)
    {
        members.sort_unstable();
        if seen_trials.insert(members.clone()) {
            trials.push(members);
        }
    }

    candidates.truncate(12);
    let mut subsets = (1usize..(1usize << candidates.len())).collect::<Vec<_>>();
    subsets.sort_by_key(|subset| (subset.count_ones(), *subset));
    for subset in subsets {
        let mut members = Vec::new();
        let mut staged_sites = HashSet::new();
        let mut conflicting_timing = false;
        for (bit, &(index, _)) in candidates.iter().enumerate() {
            if subset & (1usize << bit) != 0 {
                if !staged_sites.insert(&pairs[index].staged) {
                    conflicting_timing = true;
                    break;
                }
                members.push(index);
            }
        }
        if conflicting_timing {
            continue;
        }
        members.sort_unstable();
        if seen_trials.insert(members.clone()) {
            trials.push(members);
        }
    }

    let mut evaluations = 0;
    let mut improvements = 0;
    for members in trials {
        if evaluations == limit {
            break;
        }
        let mut candidate = genome.clone();
        for index in members {
            candidate.staging_priority[index] = 1.0;
        }
        let scored = context.score_for_search(&candidate, best.fitness)?;
        evaluations += 1;
        if scored.placement == PlacementStatus::Concrete && scored.fitness < best.fitness {
            best_genome = candidate;
            best = scored;
            improvements += 1;
        }
    }
    best = context.score(&best_genome)?;
    Ok(StagingRefinementOutcome {
        best_genome,
        best,
        evaluations,
        improvements,
    })
}

#[derive(Clone, Copy)]
enum GuidedTrial {
    Order { moving: usize, anchor: usize },
    Cache { index: usize, target: f64 },
}

fn guided_trials(
    context: &PlanSearchContext<'_>,
    best: &ScoredEvaluation,
    genome: &EvaluationGenome,
) -> Vec<GuidedTrial> {
    // Bound locality probes so the majority of even the smallest guided slice
    // remains available for exact cache intervals. On wide root sets, allowing
    // order trials to consume the slice starves the replay attribution that
    // motivated the guided phase in the first place.
    const ORDER_TRIAL_LIMIT: usize = 8;
    let mut trials = guided_root_order_trials(context, best, genome);
    trials.truncate(ORDER_TRIAL_LIMIT);
    trials.extend(
        guided_interval_trials(context, best, genome)
            .into_iter()
            .map(|(index, target)| GuidedTrial::Cache { index, target }),
    );
    trials
}

fn replay_by_value(
    context: &PlanSearchContext<'_>,
    best: &ScoredEvaluation,
) -> BTreeMap<ValueFingerprint, usize> {
    let Some(plan) = &best.plan else {
        return BTreeMap::new();
    };
    let mut replay_by_value = BTreeMap::<ValueFingerprint, usize>::new();
    for (&expr, attribution) in &plan.attribution {
        if attribution.computations <= 1 {
            continue;
        }
        let replay = attribution
            .arithmetic_ops
            .saturating_sub(attribution.arithmetic_ops / attribution.computations);
        if replay != 0 {
            *replay_by_value
                .entry(context.expression_fingerprint(expr))
                .or_default() += replay;
        }
    }
    replay_by_value
}

fn guided_root_order_trials(
    context: &PlanSearchContext<'_>,
    best: &ScoredEvaluation,
    genome: &EvaluationGenome,
) -> Vec<GuidedTrial> {
    let replay_by_value = replay_by_value(context, best);
    let mut values = replay_by_value.into_iter().collect::<Vec<_>>();
    values.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    let mut unit_order = (0..genome.root_order_key.len()).collect::<Vec<_>>();
    unit_order.sort_by(|&a, &b| {
        genome.root_order_key[a]
            .total_cmp(&genome.root_order_key[b])
            .then_with(|| a.cmp(&b))
    });
    let mut positions = vec![0usize; unit_order.len()];
    for (position, &unit) in unit_order.iter().enumerate() {
        positions[unit] = position;
    }

    let mut trials = Vec::new();
    for (value, _) in values {
        let mut units = context
            .site_index()
            .sites()
            .iter()
            .filter(|site| site.value == value)
            .filter_map(|site| context.unit_index_for_root_key(&site.root))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        units.sort_by_key(|&unit| positions[unit]);
        for pair in units.windows(2) {
            let first = pair[0];
            let second = pair[1];
            if positions[second] != positions[first] + 1 {
                trials.push(GuidedTrial::Order {
                    moving: second,
                    anchor: first,
                });
                trials.push(GuidedTrial::Order {
                    moving: first,
                    anchor: second,
                });
            }
        }
    }
    trials
}

fn move_unit_after(keys: &mut [f64], moving: usize, anchor: usize) {
    if moving == anchor {
        return;
    }
    let mut order = (0..keys.len()).collect::<Vec<_>>();
    order.sort_by(|&a, &b| keys[a].total_cmp(&keys[b]).then_with(|| a.cmp(&b)));
    let Some(moving_position) = order.iter().position(|&unit| unit == moving) else {
        return;
    };
    order.remove(moving_position);
    let Some(anchor_position) = order.iter().position(|&unit| unit == anchor) else {
        return;
    };
    order.insert(anchor_position + 1, moving);

    let mut sorted_keys = keys.to_vec();
    sorted_keys.sort_by(f64::total_cmp);
    for (position, unit) in order.into_iter().enumerate() {
        keys[unit] = sorted_keys[position];
    }
}

fn guided_interval_trials(
    context: &PlanSearchContext<'_>,
    best: &ScoredEvaluation,
    genome: &EvaluationGenome,
) -> Vec<(usize, f64)> {
    let replay_by_value = replay_by_value(context, best);
    let Some(plan) = &best.plan else {
        return Vec::new();
    };

    // A positive gene describes a *future demand*, not the point at which a
    // value is produced. Select the last demand that was actually traversed by
    // this winner. Using structural-index order here can select an earlier or
    // even pruned occurrence and therefore fail to span the replay interval we
    // are trying to remove.
    let mut sites = replay_by_value
        .into_iter()
        .filter_map(|(value, replay)| {
            let site = plan.sites.iter().rev().find(|site| site.value == value)?;
            context
                .site_index()
                .position(site)
                .map(|index| (index, replay))
        })
        .collect::<Vec<_>>();
    sites.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    const TARGETS: [f64; 3] = [1.0, 0.5, 0.25];
    let mut trials = Vec::new();
    // Cover distinct replay intervals before tuning the priority of an interval
    // already tested. With a small guided slice, site-major ordering spent
    // three evaluations on each value and barely reached the ranked tail.
    for target in TARGETS {
        for &(index, _) in &sites {
            if genome.cache_priority[index] != target {
                trials.push((index, target));
            }
        }
    }
    trials
}

#[cfg(test)]
mod tests {
    use super::move_unit_after;

    #[test]
    fn move_unit_after_preserves_keys_and_changes_only_order() {
        let mut keys = vec![0.0, 0.25, 0.5, 0.75];
        move_unit_after(&mut keys, 3, 0);

        let mut order = (0..keys.len()).collect::<Vec<_>>();
        order.sort_by(|&a, &b| keys[a].total_cmp(&keys[b]).then_with(|| a.cmp(&b)));
        let mut sorted = keys.clone();
        sorted.sort_by(f64::total_cmp);
        assert_eq!(order, vec![0, 3, 1, 2]);
        assert_eq!(sorted, vec![0.0, 0.25, 0.5, 0.75]);
    }
}

fn validate_config(config: MutationSearchConfig) -> Result<(), MutationSearchError> {
    if config.population == 0 {
        return Err(MutationSearchError::InvalidConfig(
            "population must be positive",
        ));
    }
    if config.evaluations < 2 {
        return Err(MutationSearchError::InvalidConfig(
            "evaluations must cover neutral and retentive baselines",
        ));
    }
    if config.cache_mutations == 0 {
        return Err(MutationSearchError::InvalidConfig(
            "cache_mutations must be positive",
        ));
    }
    Ok(())
}

fn mutate(genome: &mut EvaluationGenome, cache_mutations: usize, rng: &mut StableRng) {
    if genome.root_order_key.len() >= 2 && rng.next_u64() & 1 == 0 {
        let first = rng.index(genome.root_order_key.len());
        let mut second = rng.index(genome.root_order_key.len() - 1);
        if second >= first {
            second += 1;
        }
        genome.root_order_key.swap(first, second);
    }

    if genome.cache_priority.is_empty() {
        return;
    }
    const STEPS: [f64; 4] = [-0.5, -0.25, 0.25, 0.5];
    for _ in 0..cache_mutations {
        let index = rng.index(genome.cache_priority.len());
        let step = STEPS[rng.index(STEPS.len())];
        genome.cache_priority[index] = (genome.cache_priority[index] + step).clamp(-1.0, 1.0);
    }
}
