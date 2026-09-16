//! Deterministic partitioning of continuation atoms by shared sources.
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainContinuationPartition {
    pub words: Vec<u16>,
    /// Sources folded here, in source-id order. Earlier partitions own the rest.
    pub fold_sources: Vec<u16>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainContinuationPartitionPlan {
    pub parts: Vec<MainContinuationPartition>,
    pub source_incidences: usize,
    pub max_sources: usize,
    work_square: usize,
}

impl MainContinuationPartitionPlan {
    fn objective(&self) -> (usize, usize, usize) {
        (self.source_incidences, self.max_sources, self.work_square)
    }
}

struct Candidates {
    program: Vec<u16>,
    sources: usize,
    assignments: Vec<Vec<u8>>,
}

struct Atom {
    start: usize,
    end: usize,
    sources: BTreeSet<u16>,
    work: usize,
}

fn atoms(words: &[u16], sources: usize) -> Result<Vec<Atom>, &'static str> {
    let mut out = Vec::new();
    let mut at = 0;
    while at < words.len() {
        let start = at;
        let header = words.get(at..at + 3).ok_or("truncated atom")?;
        let members = match header[0] >> 13 {
            0 | 1 => 1,
            2 => {
                at += 3;
                usize::from(header[1])
            }
            _ => return Err("invalid atom class"),
        };
        if members == 0 {
            return Err("empty group");
        }
        let mut used = BTreeSet::new();
        let mut work = 0;
        for _ in 0..members {
            let term = words.get(at..at + 3).ok_or("truncated member")?;
            used.insert(term[1]);
            match term[0] >> 13 {
                0 => work += 1,
                1 => {
                    used.insert(term[2]);
                    work += 8;
                }
                _ => return Err("invalid member class"),
            }
            at += 3;
        }
        if used.iter().any(|&s| usize::from(s) >= sources) {
            return Err("source out of bounds");
        }
        out.push(Atom {
            start,
            end: at,
            sources: used,
            work,
        });
    }
    if out.is_empty() {
        return Err("empty program");
    }
    Ok(out)
}

fn validate(input: &Candidates) -> Result<Vec<MainContinuationPartitionPlan>, &'static str> {
    let atoms = atoms(&input.program, input.sources)?;
    let mut plans = Vec::new();
    for assignment in &input.assignments {
        if assignment.len() != atoms.len() {
            return Err("atom coverage mismatch");
        }
        let k = usize::from(*assignment.iter().max().ok_or("empty assignment")?) + 1;
        if ![2, 4, 8].contains(&k) {
            return Err("unsupported partition count");
        }
        let mut seen = BTreeSet::new();
        let mut parts = Vec::new();
        let mut source_incidences = 0;
        let mut max_sources = 0;
        let mut work_square = 0;
        for part in 0..k {
            let mut words = Vec::new();
            let mut used = BTreeSet::new();
            let mut work = 0;
            for (atom, &owner) in atoms.iter().zip(assignment) {
                if usize::from(owner) == part {
                    words.extend_from_slice(&input.program[atom.start..atom.end]);
                    used.extend(&atom.sources);
                    work += atom.work;
                }
            }
            if words.is_empty() {
                return Err("empty partition");
            }
            let fold_sources = used.difference(&seen).copied().collect();
            source_incidences += used.len();
            max_sources = max_sources.max(used.len());
            work_square += work * work;
            seen.extend(used);
            parts.push(MainContinuationPartition {
                words,
                fold_sources,
            });
        }
        if seen.len() != input.sources {
            return Err("incomplete source coverage");
        }
        plans.push(MainContinuationPartitionPlan {
            parts,
            source_incidences,
            max_sources,
            work_square,
        });
    }
    Ok(plans)
}

struct Order(u64);
impl Order {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn shuffle(&mut self, values: &mut [usize]) {
        for i in (1..values.len()).rev() {
            let j = self.next() as usize % (i + 1);
            values.swap(i, j);
        }
    }
}

fn objective(sizes: &[usize], loads: &[usize]) -> (usize, usize, usize) {
    (
        sizes.iter().sum(),
        *sizes.iter().max().unwrap(),
        loads.iter().map(|w| w * w).sum(),
    )
}

/// Build bounded candidates once during symbolic program preparation. Starting
/// with contiguous whole atoms guarantees a legal assignment for every feasible
/// K. Heavy atoms seed additional regions; moves/swaps reduce source overlap.
pub fn compile_main_continuation_partitions(
    words: &[u16],
    sources: usize,
) -> Result<Vec<MainContinuationPartitionPlan>, &'static str> {
    let aa = atoms(words, sources)?;
    let n = aa.len();
    let mut assignments = Vec::new();
    let total: usize = aa.iter().map(|a| a.work).sum();
    for k in [2, 4, 8] {
        if n < k {
            continue;
        }
        let mut prefix = vec![0];
        for a in &aa {
            prefix.push(prefix.last().unwrap() + a.work);
        }
        let mut cuts = vec![0];
        for part in 1..k {
            let lo = cuts.last().unwrap() + 1;
            let hi = n - (k - part);
            let cut = (lo..=hi)
                .min_by_key(|&i| ((prefix[i] * k).abs_diff(total * part), i))
                .unwrap();
            cuts.push(cut);
        }
        cuts.push(n);
        let mut reference = vec![0; n];
        let mut cap = (115 * total).div_ceil(100 * k);
        for part in 0..k {
            reference[cuts[part]..cuts[part + 1]].fill(part as u8);
            cap = cap.max(prefix[cuts[part + 1]] - prefix[cuts[part]]);
        }
        cap = cap.max(aa.iter().map(|a| a.work).max().unwrap());
        let mut candidates = Vec::new();
        for trial in 0..9 {
            let mut order = Order(trial as u64);
            let mut assignment = reference.clone();
            let mut counts = vec![vec![0usize; sources]; k];
            let mut loads = vec![0usize; k];
            let mut indices: Vec<_> = (0..n).collect();
            if trial != 0 {
                order.shuffle(&mut indices);
                indices.sort_by_key(|&i| std::cmp::Reverse(aa[i].work));
                let mut feasible = true;
                for &i in &indices {
                    let a = &aa[i];
                    let owner = (0..k)
                        .filter(|&q| loads[q] + a.work <= cap)
                        .min_by_key(|&q| {
                            (
                                a.sources
                                    .iter()
                                    .filter(|&&s| counts[q][usize::from(s)] == 0)
                                    .count(),
                                loads[q],
                                q,
                            )
                        });
                    let Some(q) = owner else {
                        feasible = false;
                        break;
                    };
                    assignment[i] = q as u8;
                    loads[q] += a.work;
                    for &s in &a.sources {
                        counts[q][usize::from(s)] += 1;
                    }
                }
                if !feasible || loads.contains(&0) {
                    continue;
                }
            } else {
                for (a, &q) in aa.iter().zip(&assignment) {
                    loads[usize::from(q)] += a.work;
                    for &s in &a.sources {
                        counts[usize::from(q)][usize::from(s)] += 1;
                    }
                }
            }
            let mut sizes: Vec<_> = counts
                .iter()
                .map(|c| c.iter().filter(|&&v| v != 0).count())
                .collect();
            let mut score = objective(&sizes, &loads);
            for _ in 0..12 {
                order.shuffle(&mut indices);
                let mut changed = false;
                for &i in &indices {
                    let a = &aa[i];
                    let old = usize::from(assignment[i]);
                    if loads[old] == a.work {
                        continue;
                    }
                    let removed = a
                        .sources
                        .iter()
                        .filter(|&&s| counts[old][usize::from(s)] == 1)
                        .count();
                    let mut best = None;
                    for q in 0..k {
                        if q == old || loads[q] + a.work > cap {
                            continue;
                        }
                        let added = a
                            .sources
                            .iter()
                            .filter(|&&s| counts[q][usize::from(s)] == 0)
                            .count();
                        if added > removed {
                            continue;
                        }
                        let mut next_sizes = sizes.clone();
                        let mut next_loads = loads.clone();
                        next_sizes[old] -= removed;
                        next_sizes[q] += added;
                        next_loads[old] -= a.work;
                        next_loads[q] += a.work;
                        let next = objective(&next_sizes, &next_loads);
                        if next < score
                            && best.as_ref().is_none_or(|(prior, _, _, _)| next < *prior)
                        {
                            best = Some((next, q, next_sizes, next_loads));
                        }
                    }
                    if let Some((next, q, next_sizes, next_loads)) = best {
                        score = next;
                        sizes = next_sizes;
                        loads = next_loads;
                        for &s in &a.sources {
                            counts[old][usize::from(s)] -= 1;
                            counts[q][usize::from(s)] += 1;
                        }
                        assignment[i] = q as u8;
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            for _ in 0..1500 {
                let i = order.next() as usize % n;
                let j = order.next() as usize % n;
                let p = usize::from(assignment[i]);
                let q = usize::from(assignment[j]);
                if p == q {
                    continue;
                }
                let mut next_loads = loads.clone();
                next_loads[p] = loads[p] - aa[i].work + aa[j].work;
                next_loads[q] = loads[q] - aa[j].work + aa[i].work;
                if next_loads[p] > cap || next_loads[q] > cap {
                    continue;
                }
                let mut next_sizes = sizes.clone();
                for &s in aa[i].sources.difference(&aa[j].sources) {
                    next_sizes[p] -= usize::from(counts[p][usize::from(s)] == 1);
                    next_sizes[q] += usize::from(counts[q][usize::from(s)] == 0);
                }
                for &s in aa[j].sources.difference(&aa[i].sources) {
                    next_sizes[q] -= usize::from(counts[q][usize::from(s)] == 1);
                    next_sizes[p] += usize::from(counts[p][usize::from(s)] == 0);
                }
                let next = objective(&next_sizes, &next_loads);
                if next < score {
                    score = next;
                    sizes = next_sizes;
                    loads = next_loads;
                    for &s in aa[i].sources.difference(&aa[j].sources) {
                        counts[p][usize::from(s)] -= 1;
                        counts[q][usize::from(s)] += 1;
                    }
                    for &s in aa[j].sources.difference(&aa[i].sources) {
                        counts[q][usize::from(s)] -= 1;
                        counts[p][usize::from(s)] += 1;
                    }
                    assignment.swap(i, j);
                }
            }
            candidates.push((score, assignment));
        }
        // Keep only candidates that can win at some active-cache capacity.
        let mut caps: Vec<_> = candidates.iter().map(|(s, _)| s.1).collect();
        caps.sort_unstable();
        caps.dedup();
        for limit in caps {
            let (_, a) = candidates
                .iter()
                .filter(|(s, _)| s.1 <= limit)
                .min_by_key(|(s, _)| *s)
                .unwrap();
            if !assignments.contains(a) {
                assignments.push(a.clone());
            }
        }
    }
    validate(&Candidates {
        program: words.to_vec(),
        sources,
        assignments,
    })
}

/// Overlap counts folded E4 traffic, including sources with BF inputs.
/// `resident_blocks` is blocks per SM times the device SM count.
pub fn select_main_continuation_partition(
    plans: &[MainContinuationPartitionPlan],
    sources: usize,
    e4_sources: usize,
    rows: usize,
    row_tiles: usize,
    resident_blocks: usize,
    l2_bytes: usize,
) -> Option<&MainContinuationPartitionPlan> {
    assert!(sources > 0);
    assert!(e4_sources <= sources);
    assert!(resident_blocks > 0);
    assert!(l2_bytes > 0);
    if row_tiles < resident_blocks {
        return None;
    }
    let e4_fraction = e4_sources as f64 / sources as f64;
    let mut best = None;
    let mut best_score = 0.0;
    for k in [2, 4, 8] {
        let candidates = || plans.iter().filter(|p| p.parts.len() == k);
        let fits = |p: &&MainContinuationPartitionPlan| {
            (p.max_sources as u128) * 128 * 32 * resident_blocks as u128 <= l2_bytes as u128
        };
        let Some(plan) = candidates().filter(fits).min_by_key(|p| p.objective()) else {
            continue;
        };
        let overlap = plan.source_incidences - sources;
        let score = sources as f64
            - plan.source_incidences as f64 / k as f64
            - 1.5 * overlap as f64
            - 2.0 * (k - 1) as f64 * (4.0 - 3.0 * e4_fraction);
        // Ties select fewer partitions.
        if score > best_score && 128.0 * rows as f64 * score >= l2_bytes as f64 / 4.0 {
            best_score = score;
            best = Some(plan);
        }
    }
    best
}

#[cfg(test)]
#[path = "main_continuation_partitions_tests.rs"]
mod tests;
