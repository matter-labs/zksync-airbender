use std::collections::{BTreeMap, BTreeSet, HashSet};

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

#[derive(Clone)]
struct Candidate {
    genome: EvaluationGenome,
    fitness: PlanFitness,
    ordinal: usize,
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
    let neutral = EvaluationGenome::neutral(context);
    let neutral_scored = context.score(&neutral)?;
    let mut telemetry = SearchTelemetry::default();
    telemetry.record(&neutral_scored);
    let neutral_fitness = neutral_scored.fitness;
    let retentive = EvaluationGenome::retentive(context);
    let retentive_scored = context.score(&retentive)?;
    telemetry.record(&retentive_scored);
    let retentive_fitness = retentive_scored.fitness;
    let mut best_genome = neutral.clone();
    let mut best = neutral_scored;
    let mut population = vec![Candidate {
        genome: neutral.clone(),
        fitness: neutral_fitness,
        ordinal: 0,
    }];
    let mut evaluations = 1usize;
    let mut next_ordinal = 1usize;
    let mut rng = StableRng::new(config.seed);
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
    let evolutionary_limit = config.evaluations - guided_budget;

    if evaluations < config.evaluations {
        if retentive_fitness < best.fitness {
            best_genome = retentive.clone();
            best = retentive_scored;
        }
        if !retentive_fitness.infeasible {
            population.push(Candidate {
                genome: retentive.clone(),
                fitness: retentive_fitness,
                ordinal: next_ordinal,
            });
        }
        evaluations += 1;
        next_ordinal += 1;
    }

    while population.len() < config.population && evaluations < evolutionary_limit {
        let mut genome = if !retentive_fitness.infeasible && population.len() & 1 != 0 {
            retentive.clone()
        } else {
            neutral.clone()
        };
        mutate(&mut genome, config.cache_mutations, &mut rng);
        let scored = context.score_for_search(&genome, best.fitness)?;
        telemetry.record(&scored);
        let fitness = scored.fitness;
        evaluations += 1;
        if scored.placement == PlacementStatus::Concrete && fitness < best.fitness {
            best_genome = genome.clone();
            best = scored;
        }
        population.push(Candidate {
            genome,
            fitness,
            ordinal: next_ordinal,
        });
        next_ordinal += 1;
    }
    rank_and_truncate(&mut population, config.population);

    while evaluations < evolutionary_limit {
        let parent = tournament(&population, &mut rng).genome.clone();
        let mut genome = parent;
        mutate(&mut genome, config.cache_mutations, &mut rng);
        let scored = context.score_for_search(&genome, best.fitness)?;
        telemetry.record(&scored);
        let fitness = scored.fitness;
        evaluations += 1;
        if scored.placement == PlacementStatus::Concrete && fitness < best.fitness {
            best_genome = genome.clone();
            best = scored;
        }
        population.push(Candidate {
            genome,
            fitness,
            ordinal: next_ordinal,
        });
        next_ordinal += 1;
        rank_and_truncate(&mut population, config.population);
    }

    // The last bounded slice first probes root-order locality for values the
    // current winner recomputed, then probes their exact cache intervals. The
    // order trials preserve every cache gene; the cache trials preserve root
    // order and change one future-demand gene.
    let guided_trials = guided_trials(context, &best, &best_genome);
    let mut guided_cursor = 0usize;
    while evaluations < config.evaluations {
        let mut genome = best_genome.clone();
        let guided_order = if let Some(trial) = guided_trials.get(guided_cursor) {
            let guided_order = matches!(trial, GuidedTrial::Order { .. });
            match trial {
                GuidedTrial::Order { moving, anchor } => {
                    move_unit_after(&mut genome.root_order_key, *moving, *anchor);
                }
                GuidedTrial::Cache { index, target } => {
                    genome.cache_priority[*index] = *target;
                }
            }
            guided_cursor += 1;
            guided_order
        } else {
            mutate(&mut genome, config.cache_mutations, &mut rng);
            false
        };
        let scored = context.score_for_search(&genome, best.fitness)?;
        telemetry.record(&scored);
        telemetry.guided_evaluations += 1;
        telemetry.guided_order_evaluations += usize::from(guided_order);
        evaluations += 1;
        if scored.placement == PlacementStatus::Concrete && scored.fitness < best.fitness {
            best_genome = genome;
            best = scored;
            telemetry.guided_improvements += 1;
            telemetry.guided_order_improvements += usize::from(guided_order);
        }
    }

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

fn rank_and_truncate(population: &mut Vec<Candidate>, capacity: usize) {
    population.sort_by_key(|candidate| (candidate.fitness, candidate.ordinal));
    population.truncate(capacity);
}

fn tournament<'a>(population: &'a [Candidate], rng: &mut StableRng) -> &'a Candidate {
    let first = &population[rng.index(population.len())];
    let second = &population[rng.index(population.len())];
    if (first.fitness, first.ordinal) <= (second.fitness, second.ordinal) {
        first
    } else {
        second
    }
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

/// Fixed xorshift64* stream: no platform hash seeds or external RNG dependency.
struct StableRng {
    state: u64,
}

impl StableRng {
    fn new(seed: u64) -> Self {
        let state = seed ^ 0x9e37_79b9_7f4a_7c15;
        Self {
            // Xorshift's all-zero state is absorbing.
            state: if state == 0 {
                0xd1b5_4a32_d192_ed03
            } else {
                state
            },
        }
    }

    fn next_u64(&mut self) -> u64 {
        let mut value = self.state;
        value ^= value >> 12;
        value ^= value << 25;
        value ^= value >> 27;
        self.state = value;
        value.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn index(&mut self, length: usize) -> usize {
        debug_assert!(length > 0);
        (self.next_u64() % length as u64) as usize
    }
}
