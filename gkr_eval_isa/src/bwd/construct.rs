//! Task 7 (CS-M0 §3): constructive backward unit order.
//!
//! `search.rs`'s GA (Task 8) explores unit permutations by mutation from
//! random/guided seeds. This module instead CONSTRUCTS one deterministic
//! order directly from the reuse structure, in three stages:
//!
//! 1. [`match_blocks`] — greedy max-weight matching (cap `K = 2`) over the
//!    unit-reuse graph ([`ReuseStructure::weighted_edges`]), forming blocks of
//!    at most 2 units that share a reused value.
//! 2. [`chain_blocks`] — a nearest-neighbor chain over those blocks, so
//!    blocks connected by a shared value stay close together too.
//! 3. [`projected_greedy`] — a bounded-lookahead (`W = 8`) insertion pass over
//!    the block chain that reorders BLOCKS (never splits one back apart) to
//!    minimize live-value pressure: at each step, of the next `W` unplaced
//!    blocks, prefer the one that closes more values than it opens, breaking
//!    ties toward the block that touches more already-open values, and
//!    finally toward the block's original position in the chain.
//!
//! Every stage is a pure function of its inputs — no wall-clock, no
//! `HashMap`-iteration-order dependence — so [`construct_unit_order`] is
//! deterministic: two calls with the same arguments produce byte-identical
//! output.

use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::{DagLayer, SiteKey};

use super::distill::{DistilledLayer, StableBwdSiteKey};
use super::structure::{ReuseEdge, ReuseStructure};

/// A contiguous run of 1 or 2 canonical unit indices. [`match_blocks`] forms
/// these; every later stage treats a block as an atomic step so a matched
/// reuse pair is never split back apart.
type Block = Vec<usize>;

/// Stage 1: greedy max-weight matching, cap `K = 2`. Deterministic: edges are
/// visited `(weight desc, left asc, right asc)`; an edge is taken iff both
/// endpoints are still unmatched. Units left unmatched after the pass become
/// singleton blocks (appended in ascending unit-index order). The returned
/// `Vec`'s ORDER is not itself semantic — [`chain_blocks`] re-sequences it —
/// only its determinism and the block CONTENTS are.
fn match_blocks(n_units: usize, weighted_edges: &[ReuseEdge]) -> Vec<Block> {
    let mut sorted: Vec<&ReuseEdge> = weighted_edges.iter().collect();
    sorted.sort_by(|a, b| {
        b.weight
            .cmp(&a.weight)
            .then(a.left.cmp(&b.left))
            .then(a.right.cmp(&b.right))
    });

    let mut matched = vec![false; n_units];
    let mut blocks: Vec<Block> = Vec::new();
    for edge in sorted {
        let (lo, hi) = (edge.left.min(edge.right), edge.left.max(edge.right));
        if lo == hi || matched[lo] || matched[hi] {
            continue;
        }
        matched[lo] = true;
        matched[hi] = true;
        blocks.push(vec![lo, hi]);
    }
    for unit in 0..n_units {
        if !matched[unit] {
            blocks.push(vec![unit]);
        }
    }
    blocks
}

/// Sum of pairwise edge weights between every unit of `x` and every unit of
/// `y` (0 for an absent edge). Used by both [`chain_blocks`] (block-to-block
/// weight) and nowhere else — [`projected_greedy`] works off the raw
/// value/unit incidence instead, since its live-set metric is not a pairwise
/// sum.
fn block_weight(edge_weight: &BTreeMap<(usize, usize), usize>, x: &[usize], y: &[usize]) -> usize {
    let mut total = 0usize;
    for &u in x {
        for &v in y {
            let key = (u.min(v), u.max(v));
            total = total.saturating_add(edge_weight.get(&key).copied().unwrap_or(0));
        }
    }
    total
}

/// Stage 2: nearest-neighbor chain over blocks. Starts from the block
/// containing unit 0; each following step appends the unmatched block with
/// the greatest total edge weight to the CURRENT CHAIN TAIL (the last
/// appended block only, not the whole chain so far) — ties broken by the
/// candidate block's smallest unit index.
fn chain_blocks(blocks: Vec<Block>, weighted_edges: &[ReuseEdge]) -> Vec<Block> {
    let edge_weight: BTreeMap<(usize, usize), usize> = weighted_edges
        .iter()
        .map(|e| ((e.left.min(e.right), e.left.max(e.right)), e.weight))
        .collect();

    let mut remaining = blocks;
    let start = remaining
        .iter()
        .position(|block| block.contains(&0))
        .expect("unit 0 must belong to exactly one block");
    let mut chain = vec![remaining.remove(start)];

    while !remaining.is_empty() {
        let tail = chain.last().expect("chain is never empty here");
        // (weight, min_unit) is minimized/maximized via explicit comparison
        // below (weight desc, min_unit asc), then the winning remaining-list
        // index is applied.
        let mut best: Option<(usize, usize, usize)> = None;
        for (index, candidate) in remaining.iter().enumerate() {
            let weight = block_weight(&edge_weight, tail, candidate);
            let min_unit = *candidate.iter().min().expect("block is non-empty");
            let better = match best {
                None => true,
                Some((best_weight, best_min_unit, _)) => {
                    weight > best_weight || (weight == best_weight && min_unit < best_min_unit)
                }
            };
            if better {
                best = Some((weight, min_unit, index));
            }
        }
        let (_, _, index) = best.expect("a block remains to append");
        chain.push(remaining.remove(index));
    }
    chain
}

/// Stage 3: projected global greedy insertion over the Stage-2 block chain,
/// within a `W = 8` lookahead window of the still-unplaced blocks. Returns
/// the flattened final unit order (a permutation of `0..n_units`).
fn projected_greedy(
    n_units: usize,
    chain: Vec<Block>,
    value_units: &[(usize, usize, Vec<usize>)],
) -> Vec<usize> {
    const WINDOW: usize = 8;

    // Reverse incidence (unit -> the values it touches) and each value's
    // total (never-changing) use count, off the raw `value_units` exposure.
    let mut touches_by_unit: Vec<Vec<usize>> = vec![Vec::new(); n_units];
    let mut total_uses: Vec<usize> = Vec::with_capacity(value_units.len());
    for (value_index, (_width, _dram_cells, units)) in value_units.iter().enumerate() {
        total_uses.push(units.len());
        for &unit in units {
            touches_by_unit[unit].push(value_index);
        }
    }

    // How many of each value's uses have been placed so far (the live-set
    // state threaded across the whole construction).
    let mut placed_count = vec![0usize; value_units.len()];

    // (opens, closes, touches) a candidate BLOCK would contribute if placed
    // next, replaying its units in order against a scratch copy of
    // `placed_count` (never mutates the real state — that only happens once
    // a block is actually chosen, below).
    fn evaluate(
        placed_count: &[usize],
        total_uses: &[usize],
        touches_by_unit: &[Vec<usize>],
        block: &[usize],
    ) -> (usize, usize, usize) {
        let mut scratch = placed_count.to_vec();
        let (mut opens, mut closes, mut touches) = (0usize, 0usize, 0usize);
        for &unit in block {
            for &value in &touches_by_unit[unit] {
                let before = scratch[value];
                scratch[value] += 1;
                if before == 0 {
                    opens += 1;
                } else {
                    touches += 1;
                }
                if scratch[value] == total_uses[value] {
                    closes += 1;
                }
            }
        }
        (opens, closes, touches)
    }

    // Each block keeps its fixed Stage-2 chain position as the final
    // tie-break, independent of how `remaining` shrinks.
    let mut remaining: Vec<(usize, Block)> = chain.into_iter().enumerate().collect();
    let mut order = Vec::with_capacity(n_units);

    while !remaining.is_empty() {
        let window = WINDOW.min(remaining.len());
        // Lexicographic key: minimize (opens - closes), then minimize
        // -touches (== maximize touches), then minimize chain position.
        let mut best: Option<((i64, i64, usize), usize)> = None;
        for index in 0..window {
            let (position, block) = &remaining[index];
            let (opens, closes, touches) =
                evaluate(&placed_count, &total_uses, &touches_by_unit, block);
            let key = (opens as i64 - closes as i64, -(touches as i64), *position);
            let better = match &best {
                None => true,
                Some((best_key, _)) => key < *best_key,
            };
            if better {
                best = Some((key, index));
            }
        }
        let (_, index) = best.expect("window is non-empty");
        let (_, block) = remaining.remove(index);
        for &unit in &block {
            for &value in &touches_by_unit[unit] {
                placed_count[value] += 1;
            }
            order.push(unit);
        }
    }
    order
}

/// Construct a deterministic backward unit order for `canonical`'s
/// relation-unit set (`d0.unit_order`), via matching -> NN chain -> projected
/// greedy over `ReuseStructure::build`'s reuse graph. Returns a permutation of
/// `0..d0.unit_order.len()`, suitable as `distill`'s `unit_permutation`.
pub fn construct_unit_order(
    canonical: &DagLayer,
    d0: &DistilledLayer,
    stable_domain: &BTreeMap<StableBwdSiteKey, SiteKey>,
) -> Vec<usize> {
    let n_units = d0.unit_order.len();
    if n_units == 0 {
        return Vec::new();
    }
    let structure = ReuseStructure::build(canonical, d0, stable_domain);
    let blocks = match_blocks(n_units, &structure.weighted_edges);
    let chain = chain_blocks(blocks, &structure.weighted_edges);
    projected_greedy(n_units, chain, &structure.value_units)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The Task-7 brief's self-contained 6-unit toy graph: values→units
    /// incidence `v0:{U0,U1}, v1:{U0,U1}, v2:{U2,U3}, v3:{U1,U2}, v4:{U4,U5},
    /// v5:{U3,U4}`, all widths 4 / `dram_cells` 4.
    fn toy_value_units() -> Vec<(usize, usize, Vec<usize>)> {
        vec![
            (4, 4, vec![0, 1]), // v0
            (4, 4, vec![0, 1]), // v1
            (4, 4, vec![2, 3]), // v2
            (4, 4, vec![1, 2]), // v3
            (4, 4, vec![4, 5]), // v4
            (4, 4, vec![3, 4]), // v5
        ]
    }

    /// The toy graph's weighted edges, exactly as the brief pins them:
    /// `(U0,U1,w=2), (U2,U3,w=1), (U1,U2,w=1), (U4,U5,w=1), (U3,U4,w=1)`.
    fn toy_weighted_edges() -> Vec<ReuseEdge> {
        vec![
            ReuseEdge {
                left: 0,
                right: 1,
                weight: 2,
            },
            ReuseEdge {
                left: 2,
                right: 3,
                weight: 1,
            },
            ReuseEdge {
                left: 1,
                right: 2,
                weight: 1,
            },
            ReuseEdge {
                left: 4,
                right: 5,
                weight: 1,
            },
            ReuseEdge {
                left: 3,
                right: 4,
                weight: 1,
            },
        ]
    }

    #[test]
    fn toy_graph_pins_matching_chain_and_final_order() {
        let value_units = toy_value_units();
        let edges = toy_weighted_edges();

        // Stage 1: heaviest edge (U0,U1,w=2) matches first; the two w=1 ties
        // (U2,U3) and (U4,U5) match next, smallest-unit-index tie-broken.
        let blocks = match_blocks(6, &edges);
        assert_eq!(
            blocks,
            vec![vec![0, 1], vec![2, 3], vec![4, 5]],
            "matching pairs: {{U0,U1}} then {{U2,U3}} and {{U4,U5}}"
        );

        // Stage 2: NN chain from the block containing U0, via v3's edge
        // (U1,U2) then v5's edge (U3,U4).
        let chain = chain_blocks(blocks, &edges);
        assert_eq!(
            chain,
            vec![vec![0, 1], vec![2, 3], vec![4, 5]],
            "NN block chain order"
        );

        // Stage 3: already open-set-optimal — pin exactly this output.
        let order = projected_greedy(6, chain, &value_units);
        assert_eq!(order, vec![0, 1, 2, 3, 4, 5], "pinned final order");
    }
}
