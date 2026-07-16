//! Score, zero-search baselines, and CELF priced greedy (spec M2 §6).
//!
//! [`Score`] is the walker's objective: `(traffic, instrs)` compared
//! lexicographically — traffic (DRAM touches) dominates, instruction count
//! only breaks ties. The two field order is binding: `derive(Ord)` on a
//! struct is lexicographic over fields in declaration order, so `traffic`
//! must be declared first. The objective is never blended into a single
//! scalar — that would let a large `instrs` improvement mask a real traffic
//! regression, which is exactly backwards for a DRAM-bound cost model.
//!
//! [`neutral_genome`] / [`naive_fill_genome`] wrap [`crate::genome::Genome`]'s
//! two endpoint constructors (`ceiling`/`all_admit`) as the zero-search
//! baselines every real search (this greedy, and Task 7's GA) must beat.
//!
//! [`greedy`] is lazy (CELF) greedy over the site domain: round 0 prices
//! every admissible locus's marginal gain with one walk each, then a
//! max-heap of stale gains lets later rounds skip re-evaluating loci whose
//! last-known gain is already worse than the current top's fresh gain
//! (submodularity's lazy-forward-selection argument — O1: "greedy is
//! oracle-grade when the model is the emitter", i.e. when the score is a
//! real walk over the real oracle rather than a proxy, lazy greedy's picks
//! are as good as eagerly re-scoring every candidate every round, just far
//! cheaper). Gains are compared lexicographically via the same
//! `(traffic_saved, instrs_saved)` ordering as `Score`; ties break on the
//! lowest locus index (`Reverse(locus)` in the max-heap key) so two runs
//! over the same table produce the identical sequence of admissions.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use cs::gkr_compiler::dag_ir::ExprId;

use crate::dag::LayerView;
use crate::genome::{decode, Genome};
use crate::oracle::SiteTable;
use crate::walk::flatten_budgeted;

/// The walker's objective: DRAM traffic first, instruction count as a
/// tiebreak. `derive(Ord)` is lexicographic over fields in declaration
/// order — `traffic` must stay first, this is spec-binding, not incidental.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Score {
    pub traffic: u64,
    pub instrs: u64,
}

/// One `flatten_budgeted` walk over `g` decoded against `table`, reduced to
/// its `Score`.
pub fn score(view: &LayerView<'_>, table: &SiteTable, g: &Genome, budget: Option<u32>) -> Score {
    let out = flatten_budgeted(view, &decode(g, table), budget);
    Score { traffic: out.stats.traffic, instrs: out.stats.instrs }
}

/// Zero-search baseline: refuses every site (`Genome::ceiling`) — decodes to
/// `NeutralOracle`-equivalent behavior (all-recompute ceiling).
pub fn neutral_genome(table: &SiteTable, n_roots: usize) -> Genome {
    Genome::ceiling(table, n_roots)
}

/// Zero-search baseline: admits every admissible site at a flat priority
/// (`Genome::all_admit`) — naive "cache everything" fill, no ranking.
pub fn naive_fill_genome(table: &SiteTable, n_roots: usize) -> Genome {
    Genome::all_admit(table, n_roots)
}

/// Lazy (CELF) greedy over the admissible site domain: round 0 prices every
/// candidate's marginal gain with one walk each; each subsequent round pops
/// the max-heap's top stale gain, re-evaluates it fresh, and commits it only
/// if the fresh gain still beats the (still-stale) runner-up — otherwise
/// reinserts it with its fresh gain and continues. Stops the moment the best
/// available gain (stale or fresh) is not a strict lexicographic
/// improvement over the current score.
///
/// Encodes the result as a `Genome`: the `rank`-th site enabled (0-indexed,
/// in commit order) gets gene `(enabled.len() - rank) as u16` — earlier
/// (higher marginal-gain) picks get the highest genes, so they're the last
/// evicted if a downstream consumer ever thresholds this genome. Disabled
/// loci keep gene `0`, `threshold` is `0`, `root_keys` is the identity
/// order (greedy never touches root visitation, only cache admission).
pub fn greedy(
    view: &LayerView<'_>,
    table: &SiteTable,
    n_roots: usize,
    budget: Option<u32>,
) -> Genome {
    let genome_of = |enabled: &[u32]| -> Genome {
        let mut keep = vec![0u16; table.len()];
        for (rank, &locus) in enabled.iter().enumerate() {
            keep[locus as usize] = (enabled.len() - rank) as u16;
        }
        Genome { root_keys: (0..n_roots as u32).collect(), keep, threshold: 0 }
    };
    let mut enabled: Vec<u32> = Vec::new();
    let mut current = score(view, table, &genome_of(&enabled), budget);

    // (gain vs current, locus). Gains are lexicographic improvements encoded
    // as (traffic_saved, instrs_saved) — larger is better in the heap.
    let mut heap: BinaryHeap<((i64, i64), Reverse<u32>)> = BinaryHeap::new();
    let gain_of = |current: Score, candidate: Score| -> (i64, i64) {
        (
            current.traffic as i64 - candidate.traffic as i64,
            current.instrs as i64 - candidate.instrs as i64,
        )
    };
    let admissible: Vec<u32> =
        (0..table.len() as u32).filter(|&l| table.sites[l as usize].admissible).collect();
    for &l in &admissible {
        let mut trial = enabled.clone();
        trial.push(l);
        let s = score(view, table, &genome_of(&trial), budget);
        heap.push((gain_of(current, s), Reverse(l)));
    }
    while let Some((stale_gain, Reverse(l))) = heap.pop() {
        if stale_gain <= (0, 0) {
            break; // even the stale (optimistic) bound is no improvement
        }
        let mut trial = enabled.clone();
        trial.push(l);
        let s = score(view, table, &genome_of(&trial), budget);
        let fresh = gain_of(current, s);
        let next_best = heap.peek().map(|&(g, _)| g).unwrap_or((i64::MIN, i64::MIN));
        if fresh >= next_best {
            if fresh <= (0, 0) {
                break;
            }
            enabled.push(l);
            current = s;
        } else {
            heap.push((fresh, Reverse(l)));
        }
    }
    genome_of(&enabled)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn score_is_lexicographic() {
        assert!(Score { traffic: 5, instrs: 900 } < Score { traffic: 6, instrs: 1 });
        assert!(Score { traffic: 5, instrs: 1 } < Score { traffic: 5, instrs: 2 });
    }

    #[test]
    fn greedy_finds_the_shared_compound() {
        // shared_diamond: caching the shared compound is the single best (and
        // only useful) decision — greedy must reach the floor.
        let layer = crate::dag::testdag::shared_diamond();
        let cross = std::collections::HashMap::new();
        let v = LayerView::new(&layer, &cross, None);
        let roots: Vec<ExprId> = layer.roots.iter().map(|r| r.expr).collect();
        let report = crate::analysis::size_layer(&v, &roots);
        let table = SiteTable::enumerate(&v);
        let g = greedy(&v, &table, layer.roots.len(), Some(16));
        assert_eq!(score(&v, &table, &g, Some(16)).traffic, report.floor);
    }

    #[test]
    fn greedy_never_loses_to_zero_search_baselines() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let roots: Vec<ExprId> = dag.layers[0].roots.iter().map(|r| r.expr).collect();
        let report = crate::analysis::size_layer(&v, &roots);
        let table = SiteTable::enumerate(&v);
        let n = dag.layers[0].roots.len();
        for budget in [Some(report.peak + 2), Some(16)] {
            let s_greedy = score(&v, &table, &greedy(&v, &table, n, budget), budget);
            let s_neutral = score(&v, &table, &neutral_genome(&table, n), budget);
            let s_naive = score(&v, &table, &naive_fill_genome(&table, n), budget);
            assert!(s_greedy <= s_neutral, "greedy {s_greedy:?} vs neutral {s_neutral:?} @ {budget:?}");
            assert!(s_greedy <= s_naive, "greedy {s_greedy:?} vs naive {s_naive:?} @ {budget:?}");
            assert!(s_greedy.traffic >= report.floor, "bracket");
        }
    }

    #[test]
    fn greedy_is_deterministic() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let table = SiteTable::enumerate(&v);
        let n = dag.layers[0].roots.len();
        let a = greedy(&v, &table, n, Some(12));
        let b = greedy(&v, &table, n, Some(12));
        assert_eq!(a, b);
    }
}
