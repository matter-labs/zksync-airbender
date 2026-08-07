//! Compile-in-loop genetic search.

use crate::forward::artifact::ForwardLayerArtifact;
use crate::search::SearchConfig;

use super::genome::{clamp_bias, decode_unit_order, Genome, CACHE_PRIORITY_BOUND};
use super::scorer::{genome_from_schedule, score, CandidateScore, LayerCtx};

struct SeedRng {
    state: u64,
}

impl SeedRng {
    fn new(seed: u64) -> Self {
        Self {
            state: seed ^ 0x9e37_79b9_7f4a_7c15,
        }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn next_unit(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 * (1.0 / ((1u64 << 53) as f64))
    }

    fn next_signed(&mut self) -> f64 {
        self.next_unit() * 2.0 - 1.0
    }

    fn next_gaussian(&mut self) -> f64 {
        let u1 = self.next_unit().max(1e-12);
        let u2 = self.next_unit();
        (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos()
    }
}

fn default_worker_count() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

fn score_genomes_parallel(
    ctx: &LayerCtx,
    entries: Vec<Genome>,
    workers: usize,
) -> Vec<(Genome, CandidateScore)> {
    if entries.is_empty() {
        return Vec::new();
    }
    let worker_count = workers.max(1).min(entries.len());
    let chunk_size = entries.len().div_ceil(worker_count);
    let mut chunks: Vec<Vec<Genome>> = Vec::with_capacity(worker_count);
    let mut current = Vec::with_capacity(chunk_size);
    for entry in entries {
        current.push(entry);
        if current.len() == chunk_size {
            chunks.push(current);
            current = Vec::with_capacity(chunk_size);
        }
    }
    if !current.is_empty() {
        chunks.push(current);
    }

    std::thread::scope(|scope| {
        let handles: Vec<_> = chunks
            .into_iter()
            .map(|chunk| {
                scope.spawn(move || {
                    chunk
                        .into_iter()
                        .map(|genome| {
                            let score = score(&genome, ctx);
                            (genome, score)
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|handle| match handle.join() {
                Ok(v) => v,
                Err(payload) => std::panic::resume_unwind(payload),
            })
            .collect::<Vec<_>>()
    })
}

const BLX_ALPHA: f64 = 0.3;

fn blx_alpha(a: f64, b: f64, lo: f64, hi: f64, rng: &mut SeedRng) -> f64 {
    let (min, max) = (a.min(b), a.max(b));
    let d = max - min;
    let low = min - BLX_ALPHA * d;
    let high = max + BLX_ALPHA * d;
    (low + rng.next_unit() * (high - low)).clamp(lo, hi)
}

fn ga_crossover(p1: &Genome, p2: &Genome, rng: &mut SeedRng) -> Genome {
    let n = p1.root_order_key.len();
    let o1 = decode_unit_order(&p1.root_order_key);
    let o2 = decode_unit_order(&p2.root_order_key);
    let child_order = if n <= 1 {
        o1
    } else {
        let a = (rng.next_u64() as usize) % n;
        let b = (rng.next_u64() as usize) % n;
        let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
        let mut in_child = vec![false; n];
        let mut child = vec![usize::MAX; n];
        for k in lo..=hi {
            child[k] = o1[k];
            in_child[o1[k]] = true;
        }
        let mut fill = 0usize;
        for &u in &o2 {
            if in_child[u] {
                continue;
            }
            while fill < n && child[fill] != usize::MAX {
                fill += 1;
            }
            child[fill] = u;
            in_child[u] = true;
        }
        child
    };
    let mut root_order_key = vec![0.0f64; n];
    for (pos, &unit) in child_order.iter().enumerate() {
        root_order_key[unit] = (pos as f64 + 0.5) / n as f64;
    }
    let cache_priority = p1
        .cache_priority
        .iter()
        .zip(&p2.cache_priority)
        .map(|(&a, &b)| blx_alpha(a, b, -CACHE_PRIORITY_BOUND, CACHE_PRIORITY_BOUND, rng))
        .collect();
    Genome {
        root_order_key,
        cache_priority,
    }
}

fn ga_mutate(g: &mut Genome, rate: f64, sigma: f64, rng: &mut SeedRng) {
    for key in &mut g.root_order_key {
        if rng.next_unit() < rate {
            *key = (*key + rng.next_gaussian() * sigma).clamp(0.0, 1.0);
        }
    }
    for gene in &mut g.cache_priority {
        if rng.next_unit() < rate {
            *gene = clamp_bias(*gene + rng.next_gaussian() * sigma);
        }
    }
}

fn ga_tournament_idx(pop: &[(Genome, CandidateScore)], k: usize, rng: &mut SeedRng) -> usize {
    let mut best: Option<usize> = None;
    for _ in 0..k.max(1) {
        let i = (rng.next_u64() as usize) % pop.len();
        best = Some(match best {
            None => i,
            Some(b) => {
                if pop[i].1.cmp(&pop[b].1).then(i.cmp(&b)).is_lt() {
                    i
                } else {
                    b
                }
            }
        });
    }
    best.expect("k>=1 so best is set")
}

fn optimize_from_population(
    ctx: &LayerCtx,
    seeds: Vec<Genome>,
    cfg: &SearchConfig,
    seed: u64,
) -> (Genome, CandidateScore) {
    let budget = cfg.evaluations;
    assert!(budget > 0, "eval budget must be positive");
    assert!(
        cfg.elitism < cfg.population,
        "elitism ({}) must be < pop ({})",
        cfg.elitism,
        cfg.population
    );

    let seeds = if seeds.is_empty() {
        vec![Genome::neutral(ctx.n_order_keys(), ctx.n_sites())]
    } else {
        seeds
    };
    let workers = default_worker_count();
    let mut rng = SeedRng::new(seed);
    let initial: Vec<_> = seeds.into_iter().take(budget).collect();
    let mut evals = initial.len();
    let mut population = score_genomes_parallel(ctx, initial, workers);
    assert!(!population.is_empty(), "seed population must be non-empty");

    let mut best = population[0].clone();
    for candidate in &population[1..] {
        if candidate.1 < best.1 {
            best = candidate.clone();
        }
    }

    while evals < budget {
        population.sort_by(|a, b| a.1.cmp(&b.1));
        let mut next: Vec<(Genome, CandidateScore)> = population
            .iter()
            .take(cfg.elitism.min(population.len()))
            .cloned()
            .collect();

        let cohort_cap = cfg
            .population
            .saturating_sub(next.len())
            .min(budget.saturating_sub(evals));
        let mut cohort = Vec::with_capacity(cohort_cap);
        for _ in 0..cohort_cap {
            let first = ga_tournament_idx(&population, cfg.tournament, &mut rng);
            let second = ga_tournament_idx(&population, cfg.tournament, &mut rng);
            let mut child = if rng.next_unit() < cfg.crossover_rate {
                ga_crossover(&population[first].0, &population[second].0, &mut rng)
            } else {
                population[first].0.clone()
            };
            ga_mutate(&mut child, cfg.mutation_rate, cfg.mutation_sigma, &mut rng);
            cohort.push(child);
        }
        if cohort.is_empty() {
            break;
        }

        let scored = score_genomes_parallel(ctx, cohort, workers);
        evals += scored.len();

        for candidate in &scored {
            if candidate.1 < best.1 {
                best = candidate.clone();
            }
        }
        next.extend(scored);
        while next.len() < cfg.population && next.len() < population.len() {
            next.push(population[next.len()].clone());
        }
        population = next;
    }

    best
}

fn reuse_weighted_genome(ctx: &LayerCtx) -> Genome {
    let mut genome = Genome::neutral(ctx.n_order_keys(), ctx.n_sites());
    if ctx.sites.is_empty() {
        return genome;
    }
    use std::collections::BTreeMap;
    let mut demand_count: BTreeMap<u32, u32> = BTreeMap::new();
    for site in &ctx.sites {
        *demand_count.entry(site.value.0).or_default() += 1;
    }
    let width = |value: u32| -> f64 {
        let f = crate::forward::compile::expr_operand_field(
            ctx.layer,
            gkr_eval_ir::ExprId(value),
            ctx.cross_layer_fields,
        );
        if f == crate::forward::isa::OperandField::Ext {
            4.0
        } else {
            1.0
        }
    };
    let density = |value: u32| demand_count[&value] as f64 / width(value);
    let max_density = ctx
        .sites
        .iter()
        .map(|s| density(s.value.0))
        .fold(0.0f64, f64::max);
    if max_density > 0.0 {
        for (gene, site) in genome.cache_priority.iter_mut().zip(&ctx.sites) {
            *gene = density(site.value.0) / max_density;
        }
    }
    genome
}

fn seeded_population(ctx: &LayerCtx, total: usize, run_offset: u64) -> Vec<Genome> {
    let n_units = ctx.n_order_keys();
    let n_sites = ctx.n_sites();
    let mut genomes = Vec::with_capacity(total);
    if total == 0 {
        return genomes;
    }
    genomes.push(Genome::neutral(n_units, n_sites));
    if genomes.len() < total {
        let mut reversed = Genome::neutral(n_units, n_sites);
        let n = reversed.root_order_key.len();
        let denom = n.max(1) as f64;
        for (idx, key) in reversed.root_order_key.iter_mut().enumerate() {
            *key = (n - 1 - idx) as f64 / denom;
        }
        genomes.push(reversed);
    }
    if genomes.len() < total {
        genomes.push(reuse_weighted_genome(ctx));
    }
    while genomes.len() < total {
        let seed = run_offset
            .wrapping_mul(0x9E37_79B9_7F4A_7C15)
            .wrapping_add((genomes.len() - 3) as u64);
        let mut rng = SeedRng::new(seed);
        let mut genome = Genome::neutral(n_units, n_sites);
        for key in &mut genome.root_order_key {
            *key = rng.next_unit();
        }
        for bias in &mut genome.cache_priority {
            *bias = rng.next_signed();
        }
        genomes.push(genome);
    }
    genomes
}

// ── search_layer: the per-layer driver the producer calls ────────────────────

pub(super) fn search_layer(
    ctx: &LayerCtx,
    cfg: &SearchConfig,
    seed: u64,
    incumbent: Option<&ForwardLayerArtifact>,
) -> ForwardLayerArtifact {
    let mut seeds = seeded_population(ctx, cfg.population.min(cfg.evaluations), seed);
    if let Some(ls) = incumbent {
        seeds[0] = genome_from_schedule(ls, ctx);
    }
    let (best_genome, best_score) = optimize_from_population(ctx, seeds, cfg, seed);

    assert!(
        !best_score.infeasible,
        "search_layer: best candidate infeasible at budget {} ({} units, {} sites)",
        ctx.budget,
        ctx.n_order_keys(),
        ctx.n_sites()
    );

    let mut schedule = super::scorer::decode_schedule(&best_genome, ctx);
    schedule.predicted_traffic = best_score.dram_traffic;

    assert!(
        ctx.floor <= schedule.predicted_traffic,
        "search_layer: floor {} above achieved traffic {}",
        ctx.floor,
        schedule.predicted_traffic
    );

    schedule
}
