pub(crate) trait SearchAdapter: Sync {
    type Genome: Clone + Send + Sync;
    type Score: Clone + Ord + Send;
    type Evaluation: Send;
    type Error: Send;
    type GuidedTrial: Send;

    fn seeds(&self) -> Result<Vec<Self::Genome>, Self::Error>;
    fn seed_is_pinned(&self, _seed_index: usize) -> bool {
        false
    }
    fn parent_eligible(&self, score: &Self::Score) -> bool;
    fn population_fill_seed(
        &self,
        seeds: &[Self::Genome],
        seed_scores: &[Self::Score],
        population_len: usize,
    ) -> Self::Genome;
    fn mutate(&self, genome: &mut Self::Genome, rng: &mut StableRng);
    fn score_batch(
        &self,
        candidates: &[(usize, Self::Genome)],
    ) -> Vec<Result<(Self::Score, Self::Evaluation), Self::Error>>;
    fn guided_trials(
        &self,
        pre_guided_best: &Self::Genome,
        pre_guided_evaluation: &Self::Evaluation,
    ) -> Vec<Self::GuidedTrial>;
    fn apply_guided_trial(
        &self,
        trial: &Self::GuidedTrial,
        live_best: &Self::Genome,
        live_evaluation: &Self::Evaluation,
    ) -> Self::Genome;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SearchDriverError<E> {
    Adapter(E),
    EmptySeeds,
    InvalidConfig(&'static str),
    ScoreBatchLength { expected: usize, actual: usize },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SearchDriverConfig {
    pub population: usize,
    pub evaluations: usize,
    pub guided_evaluations: usize,
    pub score_batch: usize,
    pub seed: u64,
}

#[derive(Debug)]
pub(crate) struct SearchDriverOutcome<G, S, E> {
    pub best_genome: G,
    pub best_score: S,
    pub best_evaluation: E,
    pub best_ordinal: usize,
    pub evaluations: usize,
    pub improvement_ordinals: Vec<usize>,
    pub guided_candidates: usize,
    pub guided_improvement_ordinals: Vec<usize>,
}

#[derive(Clone)]
struct Candidate<G, S> {
    genome: G,
    score: S,
    ordinal: usize,
    pinned: bool,
}

struct Evaluated<G, S, E> {
    genome: G,
    score: S,
    evaluation: E,
    ordinal: usize,
}

pub(crate) fn run_search_driver<A: SearchAdapter>(
    adapter: &A,
    config: SearchDriverConfig,
) -> Result<SearchDriverOutcome<A::Genome, A::Score, A::Evaluation>, SearchDriverError<A::Error>> {
    validate_config(config)?;
    let seeds = adapter.seeds().map_err(SearchDriverError::Adapter)?;
    if seeds.is_empty() {
        return Err(SearchDriverError::EmptySeeds);
    }
    let pinned_seeds = (0..seeds.len())
        .filter(|&index| adapter.seed_is_pinned(index))
        .count();
    if pinned_seeds > config.population {
        return Err(SearchDriverError::InvalidConfig(
            "pinned seeds exceed population",
        ));
    }
    if config.evaluations < seeds.len() {
        return Err(SearchDriverError::InvalidConfig(
            "evaluations must cover every seed",
        ));
    }
    let evolutionary_limit = config.evaluations - config.guided_evaluations;
    if evolutionary_limit < seeds.len() {
        return Err(SearchDriverError::InvalidConfig(
            "evolutionary evaluations must cover every seed",
        ));
    }

    let mut population = Vec::with_capacity(config.population + config.score_batch);
    let mut seed_scores = Vec::with_capacity(seeds.len());
    let mut best = None::<Evaluated<A::Genome, A::Score, A::Evaluation>>;
    let mut improvement_ordinals = Vec::new();
    let mut next_ordinal = 0usize;

    for chunk in seeds.chunks(config.score_batch) {
        let candidates = chunk
            .iter()
            .cloned()
            .map(|genome| {
                let ordinal = next_ordinal;
                next_ordinal += 1;
                (ordinal, genome)
            })
            .collect::<Vec<_>>();
        let evaluated = score_batch(adapter, candidates)?;
        for candidate in evaluated {
            seed_scores.push(candidate.score.clone());
            if adapter.parent_eligible(&candidate.score) {
                population.push(Candidate {
                    genome: candidate.genome.clone(),
                    score: candidate.score.clone(),
                    ordinal: candidate.ordinal,
                    pinned: adapter.seed_is_pinned(candidate.ordinal),
                });
            }
            if best
                .as_ref()
                .is_none_or(|best| candidate.score < best.score)
                && (best.is_none() || adapter.parent_eligible(&candidate.score))
            {
                if best.is_some() {
                    improvement_ordinals.push(candidate.ordinal);
                }
                best = Some(candidate);
            }
        }
    }

    if population.is_empty() && evolutionary_limit > seeds.len() {
        return Err(SearchDriverError::InvalidConfig(
            "adapter produced no parent-eligible seeds",
        ));
    }

    let mut rng = StableRng::new(config.seed);
    while population.len() < config.population && next_ordinal < evolutionary_limit {
        let batch_len = config
            .score_batch
            .min(config.population - population.len())
            .min(evolutionary_limit - next_ordinal);
        let candidates = (0..batch_len)
            .map(|pending| {
                let mut genome =
                    adapter.population_fill_seed(&seeds, &seed_scores, population.len() + pending);
                adapter.mutate(&mut genome, &mut rng);
                let ordinal = next_ordinal;
                next_ordinal += 1;
                (ordinal, genome)
            })
            .collect::<Vec<_>>();
        for candidate in score_batch(adapter, candidates)? {
            let population_candidate = Candidate {
                genome: candidate.genome.clone(),
                score: candidate.score.clone(),
                ordinal: candidate.ordinal,
                pinned: false,
            };
            update_best(adapter, &mut best, candidate, &mut improvement_ordinals);
            population.push(population_candidate);
        }
    }
    rank_and_truncate(&mut population, config.population);

    while next_ordinal < evolutionary_limit {
        let batch_len = config.score_batch.min(evolutionary_limit - next_ordinal);
        let candidates = (0..batch_len)
            .map(|_| {
                let parent = tournament(&population, &mut rng).genome.clone();
                let mut genome = parent;
                adapter.mutate(&mut genome, &mut rng);
                let ordinal = next_ordinal;
                next_ordinal += 1;
                (ordinal, genome)
            })
            .collect::<Vec<_>>();
        let evaluated = score_batch(adapter, candidates)?;
        for candidate in evaluated {
            let population_candidate = Candidate {
                genome: candidate.genome.clone(),
                score: candidate.score.clone(),
                ordinal: candidate.ordinal,
                pinned: false,
            };
            update_best(adapter, &mut best, candidate, &mut improvement_ordinals);
            population.push(population_candidate);
        }
        rank_and_truncate(&mut population, config.population);
    }

    let mut best = best.expect("nonempty seeds always select an incumbent");
    let guided_trials = if config.guided_evaluations == 0 {
        Vec::new()
    } else {
        adapter.guided_trials(&best.genome, &best.evaluation)
    };
    let guided_candidates = guided_trials.len().min(config.guided_evaluations);
    let mut guided_cursor = 0usize;
    let mut guided_improvement_ordinals = Vec::new();
    while next_ordinal < config.evaluations {
        let use_guided = guided_cursor < guided_candidates;
        let available = if use_guided {
            guided_candidates - guided_cursor
        } else {
            config.evaluations - next_ordinal
        };
        let batch_len = config
            .score_batch
            .min(config.evaluations - next_ordinal)
            .min(available);
        let candidates = (0..batch_len)
            .map(|_| {
                let genome = if use_guided {
                    let genome = adapter.apply_guided_trial(
                        &guided_trials[guided_cursor],
                        &best.genome,
                        &best.evaluation,
                    );
                    guided_cursor += 1;
                    genome
                } else {
                    let mut genome = best.genome.clone();
                    adapter.mutate(&mut genome, &mut rng);
                    genome
                };
                let ordinal = next_ordinal;
                next_ordinal += 1;
                (ordinal, genome)
            })
            .collect::<Vec<_>>();
        for candidate in score_batch(adapter, candidates)? {
            if adapter.parent_eligible(&candidate.score) && candidate.score < best.score {
                improvement_ordinals.push(candidate.ordinal);
                guided_improvement_ordinals.push(candidate.ordinal);
                best = candidate;
            }
        }
    }

    Ok(SearchDriverOutcome {
        best_genome: best.genome,
        best_score: best.score,
        best_evaluation: best.evaluation,
        best_ordinal: best.ordinal,
        evaluations: next_ordinal,
        improvement_ordinals,
        guided_candidates,
        guided_improvement_ordinals,
    })
}

fn validate_config<E>(config: SearchDriverConfig) -> Result<(), SearchDriverError<E>> {
    if config.population == 0 {
        return Err(SearchDriverError::InvalidConfig(
            "population must be positive",
        ));
    }
    if config.evaluations == 0 {
        return Err(SearchDriverError::InvalidConfig(
            "evaluations must be positive",
        ));
    }
    if config.guided_evaluations > config.evaluations {
        return Err(SearchDriverError::InvalidConfig(
            "guided evaluations exceed total evaluations",
        ));
    }
    if config.score_batch == 0 {
        return Err(SearchDriverError::InvalidConfig(
            "score batch must be positive",
        ));
    }
    Ok(())
}

fn score_batch<A: SearchAdapter>(
    adapter: &A,
    candidates: Vec<(usize, A::Genome)>,
) -> Result<Vec<Evaluated<A::Genome, A::Score, A::Evaluation>>, SearchDriverError<A::Error>> {
    let expected = candidates.len();
    let results = adapter.score_batch(&candidates);
    if results.len() != expected {
        return Err(SearchDriverError::ScoreBatchLength {
            expected,
            actual: results.len(),
        });
    }
    let mut evaluated = candidates
        .into_iter()
        .zip(results)
        .map(|((ordinal, genome), result)| {
            result
                .map(|(score, evaluation)| Evaluated {
                    genome,
                    score,
                    evaluation,
                    ordinal,
                })
                .map_err(SearchDriverError::Adapter)
        })
        .collect::<Result<Vec<_>, _>>()?;
    evaluated.sort_by_key(|candidate| candidate.ordinal);
    Ok(evaluated)
}

fn update_best<A: SearchAdapter>(
    adapter: &A,
    best: &mut Option<Evaluated<A::Genome, A::Score, A::Evaluation>>,
    candidate: Evaluated<A::Genome, A::Score, A::Evaluation>,
    improvement_ordinals: &mut Vec<usize>,
) {
    if adapter.parent_eligible(&candidate.score)
        && best
            .as_ref()
            .is_none_or(|best| candidate.score < best.score)
    {
        if best.is_some() {
            improvement_ordinals.push(candidate.ordinal);
        }
        *best = Some(candidate);
    }
}

fn rank_and_truncate<G, S: Ord>(population: &mut Vec<Candidate<G, S>>, capacity: usize) {
    population.sort_by(|left, right| {
        left.score
            .cmp(&right.score)
            .then_with(|| left.ordinal.cmp(&right.ordinal))
    });
    let pinned = population
        .iter()
        .filter(|candidate| candidate.pinned)
        .count();
    debug_assert!(pinned <= capacity);
    let mut unpinned_slots = capacity - pinned;
    population.retain(|candidate| {
        if candidate.pinned {
            true
        } else if unpinned_slots != 0 {
            unpinned_slots -= 1;
            true
        } else {
            false
        }
    });
}

fn tournament<'a, G, S: Ord>(
    population: &'a [Candidate<G, S>],
    rng: &mut StableRng,
) -> &'a Candidate<G, S> {
    let first = &population[rng.index(population.len())];
    let second = &population[rng.index(population.len())];
    if (&first.score, first.ordinal) <= (&second.score, second.ordinal) {
        first
    } else {
        second
    }
}

/// Fixed xorshift64* stream: no platform hash seeds or external RNG dependency.
pub(crate) struct StableRng {
    state: u64,
}

impl StableRng {
    pub(crate) fn new(seed: u64) -> Self {
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

    pub(crate) fn next_u64(&mut self) -> u64 {
        let mut value = self.state;
        value ^= value >> 12;
        value ^= value << 25;
        value ^= value >> 27;
        self.state = value;
        value.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    pub(crate) fn index(&mut self, length: usize) -> usize {
        debug_assert!(length > 0);
        (self.next_u64() % length as u64) as usize
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::{SearchAdapter, SearchDriverConfig, StableRng, run_search_driver};

    struct ToyAdapter {
        equal_scores: bool,
        candidates: Mutex<Vec<(usize, i32)>>,
    }

    impl ToyAdapter {
        fn new(equal_scores: bool) -> Self {
            Self {
                equal_scores,
                candidates: Mutex::new(Vec::new()),
            }
        }

        fn candidate_digest(&self) -> u64 {
            self.candidates
                .lock()
                .expect("toy candidate trace lock")
                .iter()
                .fold(0xcbf2_9ce4_8422_2325, |digest, (ordinal, genome)| {
                    ordinal
                        .to_le_bytes()
                        .into_iter()
                        .chain(genome.to_le_bytes())
                        .fold(digest, |digest, byte| {
                            (digest ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3)
                        })
                })
        }
    }

    impl SearchAdapter for ToyAdapter {
        type Genome = i32;
        type Score = i32;
        type Evaluation = ();
        type Error = ();
        type GuidedTrial = i32;

        fn seeds(&self) -> Result<Vec<Self::Genome>, Self::Error> {
            Ok(vec![0, 10])
        }

        fn parent_eligible(&self, _score: &Self::Score) -> bool {
            true
        }

        fn population_fill_seed(
            &self,
            seeds: &[Self::Genome],
            _seed_scores: &[Self::Score],
            population_len: usize,
        ) -> Self::Genome {
            seeds[population_len & 1]
        }

        fn mutate(&self, genome: &mut Self::Genome, rng: &mut StableRng) {
            *genome = rng.index(101) as i32;
        }

        fn score_batch(
            &self,
            candidates: &[(usize, Self::Genome)],
        ) -> Vec<Result<(Self::Score, Self::Evaluation), Self::Error>> {
            self.candidates
                .lock()
                .expect("toy candidate trace lock")
                .extend_from_slice(candidates);
            candidates
                .iter()
                .map(|(_, genome)| {
                    let score = if self.equal_scores {
                        0
                    } else {
                        (50 - genome).abs()
                    };
                    Ok((score, ()))
                })
                .collect()
        }

        fn guided_trials(
            &self,
            _best: &Self::Genome,
            _evaluation: &Self::Evaluation,
        ) -> Vec<Self::GuidedTrial> {
            vec![1, -1]
        }

        fn apply_guided_trial(
            &self,
            trial: &Self::GuidedTrial,
            _best: &Self::Genome,
            _evaluation: &Self::Evaluation,
        ) -> Self::Genome {
            *trial
        }
    }

    struct ToyOutcome {
        best_genome: i32,
        best_score: i32,
        evaluations: usize,
        improvement_ordinals: Vec<usize>,
        candidate_digest: u64,
    }

    fn run_toy_search(score_batch: usize, evaluations: usize, seed: u64) -> ToyOutcome {
        let adapter = ToyAdapter::new(false);
        let outcome = run_search_driver(
            &adapter,
            SearchDriverConfig {
                population: 8,
                evaluations,
                guided_evaluations: 8,
                score_batch,
                seed,
            },
        )
        .expect("run toy search");
        ToyOutcome {
            best_genome: outcome.best_genome,
            best_score: outcome.best_score,
            evaluations: outcome.evaluations,
            improvement_ordinals: outcome.improvement_ordinals,
            candidate_digest: adapter.candidate_digest(),
        }
    }

    #[test]
    fn search_driver_counts_seeds_and_merges_batches_by_ordinal() {
        let one = run_toy_search(1, 128, 7);
        let eight = run_toy_search(8, 128, 7);
        assert_eq!(one.best_genome, eight.best_genome);
        assert_eq!(one.best_score, eight.best_score);
        assert_eq!(one.evaluations, 128);
        assert!(!one.improvement_ordinals.is_empty());
        assert_eq!(one.improvement_ordinals, eight.improvement_ordinals);
        assert_eq!(one.candidate_digest, eight.candidate_digest);
    }

    #[test]
    fn stable_ordinal_breaks_complete_score_ties() {
        let adapter = ToyAdapter::new(true);
        let outcome = run_search_driver(
            &adapter,
            SearchDriverConfig {
                population: 2,
                evaluations: 16,
                guided_evaluations: 4,
                score_batch: 4,
                seed: 3,
            },
        )
        .expect("run equal-score search");
        assert_eq!(outcome.best_ordinal, 0);
        assert_eq!(outcome.best_genome, 0);
        assert!(outcome.improvement_ordinals.is_empty());
    }

    struct PinnedSeedAdapter {
        pinned_parent_uses: AtomicUsize,
        mutations: AtomicUsize,
        pin_both: bool,
    }

    impl SearchAdapter for PinnedSeedAdapter {
        type Genome = i32;
        type Score = i32;
        type Evaluation = ();
        type Error = ();
        type GuidedTrial = ();

        fn seeds(&self) -> Result<Vec<Self::Genome>, Self::Error> {
            Ok(vec![1_000, 0])
        }

        fn seed_is_pinned(&self, seed_index: usize) -> bool {
            self.pin_both || seed_index == 0
        }

        fn parent_eligible(&self, _score: &Self::Score) -> bool {
            true
        }

        fn population_fill_seed(
            &self,
            seeds: &[Self::Genome],
            _seed_scores: &[Self::Score],
            population_len: usize,
        ) -> Self::Genome {
            seeds[population_len % seeds.len()]
        }

        fn mutate(&self, genome: &mut Self::Genome, _rng: &mut StableRng) {
            self.mutations.fetch_add(1, Ordering::Relaxed);
            if *genome == 1_000 {
                self.pinned_parent_uses.fetch_add(1, Ordering::Relaxed);
            }
            *genome = 0;
        }

        fn score_batch(
            &self,
            candidates: &[(usize, Self::Genome)],
        ) -> Vec<Result<(Self::Score, Self::Evaluation), Self::Error>> {
            candidates
                .iter()
                .map(|(_, genome)| Ok((*genome, ())))
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
            *live_best
        }
    }

    #[test]
    fn worse_pinned_seed_survives_repeated_truncation_and_remains_a_parent() {
        let adapter = PinnedSeedAdapter {
            pinned_parent_uses: AtomicUsize::new(0),
            mutations: AtomicUsize::new(0),
            pin_both: false,
        };
        run_search_driver(
            &adapter,
            SearchDriverConfig {
                population: 2,
                evaluations: 128,
                guided_evaluations: 0,
                score_batch: 1,
                seed: 17,
            },
        )
        .expect("run pinned-seed search");
        assert_eq!(adapter.mutations.load(Ordering::Relaxed), 126);
        assert!(adapter.pinned_parent_uses.load(Ordering::Relaxed) > 1);
    }

    #[test]
    fn pinned_seed_count_must_fit_population() {
        let adapter = PinnedSeedAdapter {
            pinned_parent_uses: AtomicUsize::new(0),
            mutations: AtomicUsize::new(0),
            pin_both: true,
        };
        assert_eq!(
            run_search_driver(
                &adapter,
                SearchDriverConfig {
                    population: 1,
                    evaluations: 2,
                    guided_evaluations: 0,
                    score_batch: 1,
                    seed: 0,
                },
            )
            .unwrap_err(),
            super::SearchDriverError::InvalidConfig("pinned seeds exceed population"),
        );
    }

    #[test]
    fn guided_trials_precede_guided_random_fill() {
        let adapter = ToyAdapter::new(true);
        let outcome = run_search_driver(
            &adapter,
            SearchDriverConfig {
                population: 2,
                evaluations: 5,
                guided_evaluations: 3,
                score_batch: 2,
                seed: 9,
            },
        )
        .expect("run guided toy search");
        assert_eq!(outcome.evaluations, 5);
        assert_eq!(
            adapter
                .candidates
                .into_inner()
                .expect("toy candidate trace lock"),
            vec![(0, 0), (1, 10), (2, 1), (3, -1), (4, 71)],
        );
    }

    struct ChangingGuidedAdapter {
        enumerations: Mutex<usize>,
        candidates: Mutex<Vec<(usize, i32)>>,
    }

    impl SearchAdapter for ChangingGuidedAdapter {
        type Genome = i32;
        type Score = i32;
        type Evaluation = i32;
        type Error = ();
        type GuidedTrial = i32;

        fn seeds(&self) -> Result<Vec<Self::Genome>, Self::Error> {
            Ok(vec![0])
        }

        fn parent_eligible(&self, _score: &Self::Score) -> bool {
            true
        }

        fn population_fill_seed(
            &self,
            seeds: &[Self::Genome],
            _seed_scores: &[Self::Score],
            _population_len: usize,
        ) -> Self::Genome {
            seeds[0]
        }

        fn mutate(&self, genome: &mut Self::Genome, _rng: &mut StableRng) {
            *genome = -100;
        }

        fn score_batch(
            &self,
            candidates: &[(usize, Self::Genome)],
        ) -> Vec<Result<(Self::Score, Self::Evaluation), Self::Error>> {
            self.candidates
                .lock()
                .expect("changing guided trace lock")
                .extend_from_slice(candidates);
            candidates
                .iter()
                .map(|(_, genome)| Ok(((30 - genome).abs(), *genome)))
                .collect()
        }

        fn guided_trials(
            &self,
            pre_guided_best: &Self::Genome,
            pre_guided_evaluation: &Self::Evaluation,
        ) -> Vec<Self::GuidedTrial> {
            *self
                .enumerations
                .lock()
                .expect("guided enumeration counter lock") += 1;
            assert_eq!(pre_guided_best, pre_guided_evaluation);
            if *pre_guided_best == 0 {
                vec![10, 20]
            } else {
                vec![99]
            }
        }

        fn apply_guided_trial(
            &self,
            trial: &Self::GuidedTrial,
            live_best: &Self::Genome,
            live_evaluation: &Self::Evaluation,
        ) -> Self::Genome {
            assert_eq!(live_best, live_evaluation);
            live_best + trial
        }
    }

    #[test]
    fn guided_descriptors_are_frozen_once_and_applied_to_live_incumbent() {
        let adapter = ChangingGuidedAdapter {
            enumerations: Mutex::new(0),
            candidates: Mutex::new(Vec::new()),
        };
        let outcome = run_search_driver(
            &adapter,
            SearchDriverConfig {
                population: 1,
                evaluations: 4,
                guided_evaluations: 3,
                score_batch: 1,
                seed: 0,
            },
        )
        .expect("run changing-guided search");

        assert_eq!(outcome.best_genome, 30);
        assert_eq!(outcome.guided_improvement_ordinals, vec![1, 2]);
        assert_eq!(
            adapter
                .enumerations
                .into_inner()
                .expect("guided enumeration counter lock"),
            1,
        );
        assert_eq!(
            adapter
                .candidates
                .into_inner()
                .expect("changing guided trace lock"),
            vec![(0, 0), (1, 10), (2, 30), (3, -100)],
        );
    }

    #[derive(Clone, Copy)]
    enum EdgeMode {
        Normal,
        EmptySeeds,
        SeedError,
        ScoreError,
        ShortBatch,
        PositionalResults,
        IneligibleLowerScore,
        AllIneligible,
    }

    struct EdgeAdapter(EdgeMode);

    impl SearchAdapter for EdgeAdapter {
        type Genome = i32;
        type Score = i32;
        type Evaluation = ();
        type Error = &'static str;
        type GuidedTrial = ();

        fn seeds(&self) -> Result<Vec<Self::Genome>, Self::Error> {
            if matches!(self.0, EdgeMode::SeedError) {
                return Err("seed failed");
            }
            Ok(match self.0 {
                EdgeMode::EmptySeeds => Vec::new(),
                EdgeMode::PositionalResults => vec![100, 200],
                EdgeMode::IneligibleLowerScore => vec![0, 1],
                _ => vec![0, 10],
            })
        }

        fn parent_eligible(&self, score: &Self::Score) -> bool {
            match self.0 {
                EdgeMode::IneligibleLowerScore => *score >= 0,
                EdgeMode::AllIneligible => false,
                _ => true,
            }
        }

        fn population_fill_seed(
            &self,
            seeds: &[Self::Genome],
            _seed_scores: &[Self::Score],
            _population_len: usize,
        ) -> Self::Genome {
            seeds[0]
        }

        fn mutate(&self, _genome: &mut Self::Genome, _rng: &mut StableRng) {}

        fn score_batch(
            &self,
            candidates: &[(usize, Self::Genome)],
        ) -> Vec<Result<(Self::Score, Self::Evaluation), Self::Error>> {
            match self.0 {
                EdgeMode::ScoreError => vec![Err("score failed"); candidates.len()],
                EdgeMode::ShortBatch => Vec::new(),
                EdgeMode::PositionalResults => candidates
                    .iter()
                    .enumerate()
                    .map(|(position, _)| Ok((if position == 0 { 10 } else { 0 }, ())))
                    .collect(),
                EdgeMode::IneligibleLowerScore => candidates
                    .iter()
                    .map(|(_, genome)| Ok((if *genome == 0 { 0 } else { -1 }, ())))
                    .collect(),
                EdgeMode::AllIneligible => candidates
                    .iter()
                    .map(|(_, genome)| Ok((-genome.abs() - 1, ())))
                    .collect(),
                _ => candidates
                    .iter()
                    .map(|(_, genome)| Ok((genome.abs(), ())))
                    .collect(),
            }
        }

        fn guided_trials(
            &self,
            _best: &Self::Genome,
            _evaluation: &Self::Evaluation,
        ) -> Vec<Self::GuidedTrial> {
            Vec::new()
        }

        fn apply_guided_trial(
            &self,
            _trial: &Self::GuidedTrial,
            best: &Self::Genome,
            _evaluation: &Self::Evaluation,
        ) -> Self::Genome {
            *best
        }
    }

    fn edge_config() -> SearchDriverConfig {
        SearchDriverConfig {
            population: 2,
            evaluations: 2,
            guided_evaluations: 0,
            score_batch: 2,
            seed: 0,
        }
    }

    #[test]
    fn empty_seeds_are_rejected() {
        assert_eq!(
            run_search_driver(&EdgeAdapter(EdgeMode::EmptySeeds), edge_config()).unwrap_err(),
            super::SearchDriverError::EmptySeeds,
        );
    }

    #[test]
    fn invalid_configuration_and_budget_edges_are_rejected() {
        let adapter = EdgeAdapter(EdgeMode::Normal);
        for (config, message) in [
            (
                SearchDriverConfig {
                    population: 0,
                    ..edge_config()
                },
                "population must be positive",
            ),
            (
                SearchDriverConfig {
                    evaluations: 0,
                    ..edge_config()
                },
                "evaluations must be positive",
            ),
            (
                SearchDriverConfig {
                    guided_evaluations: 3,
                    ..edge_config()
                },
                "guided evaluations exceed total evaluations",
            ),
            (
                SearchDriverConfig {
                    score_batch: 0,
                    ..edge_config()
                },
                "score batch must be positive",
            ),
            (
                SearchDriverConfig {
                    evaluations: 1,
                    ..edge_config()
                },
                "evaluations must cover every seed",
            ),
            (
                SearchDriverConfig {
                    evaluations: 2,
                    guided_evaluations: 1,
                    ..edge_config()
                },
                "evolutionary evaluations must cover every seed",
            ),
        ] {
            assert_eq!(
                run_search_driver(&adapter, config).unwrap_err(),
                super::SearchDriverError::InvalidConfig(message),
            );
        }
    }

    #[test]
    fn adapter_errors_and_wrong_batch_lengths_are_reported() {
        assert_eq!(
            run_search_driver(&EdgeAdapter(EdgeMode::SeedError), edge_config()).unwrap_err(),
            super::SearchDriverError::Adapter("seed failed"),
        );
        assert_eq!(
            run_search_driver(&EdgeAdapter(EdgeMode::ScoreError), edge_config()).unwrap_err(),
            super::SearchDriverError::Adapter("score failed"),
        );
        assert_eq!(
            run_search_driver(&EdgeAdapter(EdgeMode::ShortBatch), edge_config()).unwrap_err(),
            super::SearchDriverError::ScoreBatchLength {
                expected: 2,
                actual: 0,
            },
        );
    }

    #[test]
    fn batch_results_remain_positionally_associated_with_ordinals() {
        let outcome = run_search_driver(&EdgeAdapter(EdgeMode::PositionalResults), edge_config())
            .expect("run positional result search");
        assert_eq!(outcome.best_genome, 200);
        assert_eq!(outcome.best_ordinal, 1);
    }

    #[test]
    fn ineligible_lower_score_does_not_replace_incumbent() {
        let outcome =
            run_search_driver(&EdgeAdapter(EdgeMode::IneligibleLowerScore), edge_config())
                .expect("run ineligible result search");
        assert_eq!(outcome.best_genome, 0);
        assert_eq!(outcome.best_score, 0);
        assert_eq!(outcome.best_ordinal, 0);

        let error = run_search_driver(
            &EdgeAdapter(EdgeMode::AllIneligible),
            SearchDriverConfig {
                evaluations: 3,
                ..edge_config()
            },
        )
        .unwrap_err();
        assert_eq!(
            error,
            super::SearchDriverError::InvalidConfig("adapter produced no parent-eligible seeds",),
        );
    }
}
