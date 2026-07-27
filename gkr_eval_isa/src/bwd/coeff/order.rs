//! Term ordering and the physical K-split for the segmented lean VM (design §3
//! "Phase 2 — segmented eval", §7 "Term ordering").
//!
//! Two independent, purely positional host passes:
//!
//!   1. [`order_terms`] — the COMMITTED semantic order. A greedy
//!      source-affinity pass that keeps terms reading the same sources close
//!      together, so that under stride-`K` execution the concurrently running
//!      warps co-touch the same lines and one warp's miss fills the line for
//!      the rest.
//!   2. [`split_round_robin`] — the PHYSICAL split of an already committed list
//!      into `K` per-warp lists, `list w` taking positions `w, w+K, w+2K, …`.
//!      It is a deterministic function of `(list, K)` computed at descriptor
//!      build time, which is what keeps committed artifacts `K`-free.
//!
//! Nothing here prices work: the per-list work model needs the round-binding
//! dependent source classes, which do not exist at the [`CoeffLayer`] layer.

use std::collections::{BTreeMap, BTreeSet};

use super::model::{CoeffLayer, CoeffTerm, SourceId, TermId};

/// How many most recently emitted terms define the affinity window.
///
/// Matched to the stride-`K` co-touch effect the order exists to create (§7):
/// the window stands for the sources the warps running "around" the next term
/// are still touching, so it is sized for the warp neighbourhood, not for a
/// resident set — there IS no resident state in this VM.
const AFFINITY_WINDOW: usize = 8;

/// The committed term order: greedy source affinity, ties on `TermId`.
///
/// Repeatedly emits the unplaced term sharing the most DISTINCT sources with
/// the union of the sources of the last `AFFINITY_WINDOW` emitted terms; ties,
/// and a window that shares nothing with any unplaced term, fall back to the
/// lowest unplaced original index. A permutation of `0..layer.terms.len()`.
pub fn order_terms(layer: &CoeffLayer) -> Vec<TermId> {
    let count = layer.terms.len();
    let sources: Vec<Vec<SourceId>> = layer.terms.iter().map(term_sources).collect();
    // Inverted index: only a term sharing a source with the window can score at
    // all, so a step scores the window's neighbourhood instead of every unplaced
    // term.
    let mut users: BTreeMap<SourceId, Vec<usize>> = BTreeMap::new();
    for (term, term_sources) in sources.iter().enumerate() {
        for &source in term_sources {
            users.entry(source).or_default().push(term);
        }
    }

    let mut emitted: Vec<usize> = Vec::with_capacity(count);
    let mut placed = vec![false; count];
    let mut lowest_unplaced = 0usize;
    let mut window: BTreeSet<SourceId> = BTreeSet::new();
    let mut shared = vec![0u32; count];
    let mut candidates: Vec<usize> = Vec::new();
    while emitted.len() < count {
        for source in &window {
            for &term in &users[source] {
                if placed[term] {
                    continue;
                }
                if shared[term] == 0 {
                    candidates.push(term);
                }
                shared[term] += 1;
            }
        }
        // `max_by_key` keeps the LAST maximum, so the reversed index makes the
        // lowest original index the unique winner of a tie.
        let next = candidates
            .iter()
            .copied()
            .max_by_key(|&term| (shared[term], std::cmp::Reverse(term)))
            .unwrap_or(lowest_unplaced);
        for &term in &candidates {
            shared[term] = 0;
        }
        candidates.clear();

        placed[next] = true;
        emitted.push(next);
        while lowest_unplaced < count && placed[lowest_unplaced] {
            lowest_unplaced += 1;
        }
        window.clear();
        for &term in emitted.iter().rev().take(AFFINITY_WINDOW) {
            window.extend(sources[term].iter().copied());
        }
    }
    emitted.into_iter().map(|term| layer.terms[term].id()).collect()
}

/// Split `items` into exactly `k` lists, `list w` taking positions
/// `w, w+k, w+2k, …` — the §3 physical per-warp split.
///
/// Purely positional, so it splits `TermId`s, decoded records or word indices
/// alike, and each list keeps the relative order of the input. Trailing lists
/// are EMPTY when `k > items.len()`, which is legal: a launch may have more
/// warps than terms.
///
/// # Panics
///
/// If `k == 0` — there is no zero-warp launch.
pub fn split_round_robin<T: Copy>(items: &[T], k: usize) -> Vec<Vec<T>> {
    assert!(k >= 1, "a round-robin split needs at least one list");
    let mut lists: Vec<Vec<T>> =
        (0..k).map(|w| Vec::with_capacity(items.len().saturating_sub(w).div_ceil(k))).collect();
    for (position, item) in items.iter().enumerate() {
        lists[position % k].push(*item);
    }
    lists
}

/// The distinct sources one term reads, ascending. A native dual factor reads
/// both projections of a source, which is ONE source here.
fn term_sources(term: &CoeffTerm) -> Vec<SourceId> {
    let mut sources = Vec::with_capacity(2);
    term.for_each_projection_use(|projection| sources.push(projection.source));
    sources.sort_unstable();
    sources.dedup();
    sources
}

#[cfg(test)]
mod tests {
    use cs::gkr_compiler::dag_ir::{BwdRegime, FieldKind, ReadPlace};

    use super::*;
    use crate::bwd::coeff::model::{CoeffSource, CoefficientRecipeId, ProjectionId};
    use crate::bwd::source::OriginLeaf;

    fn layer(sources: usize, terms: Vec<CoeffTerm>) -> CoeffLayer {
        CoeffLayer {
            regime: BwdRegime::Ext,
            c_init: None,
            coefficients: Vec::new(),
            sources: (0..sources)
                .map(|column| CoeffSource {
                    origin: OriginLeaf::Read(ReadPlace::BaseLayerWitness { column }),
                    field: FieldKind::Ext,
                })
                .collect(),
            terms,
        }
    }

    fn c0(index: u32, source: u32) -> CoeffTerm {
        CoeffTerm::C0Linear {
            id: TermId(index),
            coefficient: CoefficientRecipeId::ONE,
            value: ProjectionId::endpoint0(SourceId(source)),
            field: FieldKind::Ext,
        }
    }

    fn c2(index: u32, lhs: u32, rhs: u32) -> CoeffTerm {
        CoeffTerm::C2Product {
            id: TermId(index),
            coefficient: CoefficientRecipeId::ONE,
            lhs: ProjectionId::delta(SourceId(lhs)),
            rhs: ProjectionId::delta(SourceId(rhs)),
            lhs_field: FieldKind::Ext,
            rhs_field: FieldKind::Ext,
        }
    }

    fn dual(index: u32, lhs: u32, rhs: u32) -> CoeffTerm {
        CoeffTerm::DualProduct {
            id: TermId(index),
            coefficient: CoefficientRecipeId::ONE,
            lhs: SourceId(lhs),
            rhs: SourceId(rhs),
        }
    }

    /// Every item appears exactly once and `list w` is exactly the input's
    /// positions `w, w+k, w+2k, …`.
    #[test]
    fn round_robin_partitions_by_position() {
        let items: Vec<u32> = (0..17).collect();
        for k in 1..=6usize {
            let lists = split_round_robin(&items, k);
            assert_eq!(lists.len(), k, "one list per warp");
            for (w, list) in lists.iter().enumerate() {
                let want: Vec<u32> = items.iter().copied().skip(w).step_by(k).collect();
                assert_eq!(*list, want, "k {k}, list {w}");
            }
            let mut flat: Vec<u32> = lists.into_iter().flatten().collect();
            flat.sort_unstable();
            assert_eq!(flat, items, "k {k} partitions the input");
        }
    }

    #[test]
    fn round_robin_of_one_list_is_the_input() {
        let items: Vec<u32> = (0..5).collect();
        assert_eq!(split_round_robin(&items, 1), vec![items.clone()]);
        assert_eq!(split_round_robin::<u32>(&[], 1), vec![Vec::<u32>::new()]);
    }

    /// More warps than terms is legal: the tail lists are empty and the split
    /// still partitions.
    #[test]
    fn round_robin_leaves_empty_tail_lists() {
        let items: Vec<u32> = vec![10, 11, 12];
        let lists = split_round_robin(&items, 5);
        assert_eq!(lists, vec![vec![10], vec![11], vec![12], vec![], vec![]]);
    }

    #[test]
    #[should_panic(expected = "at least one list")]
    fn round_robin_rejects_zero_lists() {
        split_round_robin(&[1u32, 2, 3], 0);
    }

    /// A permutation of every `TermId`, and the same one on every call — later
    /// tasks encode against this order.
    #[test]
    fn order_is_a_deterministic_permutation() {
        let terms = vec![
            c0(0, 3),
            c2(1, 0, 1),
            dual(2, 2, 3),
            c0(3, 1),
            c2(4, 2, 2),
            c0(5, 0),
            dual(6, 1, 2),
        ];
        let layer = layer(4, terms);
        let order = order_terms(&layer);
        assert_eq!(order, order_terms(&layer), "ordering is a pure function of the layer");
        let mut sorted = order.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, (0..7).map(TermId).collect::<Vec<_>>(), "no term is lost or repeated");
    }

    #[test]
    fn order_of_an_empty_layer_is_empty() {
        assert!(order_terms(&layer(0, Vec::new())).is_empty());
    }

    /// The point of the pass: two interleaved source clusters come out
    /// clustered, not in original index order.
    #[test]
    fn order_clusters_terms_that_share_a_source() {
        let terms = vec![c0(0, 0), c0(1, 1), c0(2, 0), c0(3, 1), c0(4, 0), c0(5, 1)];
        let order = order_terms(&layer(2, terms));
        assert_eq!(
            order,
            [0, 2, 4, 1, 3, 5].map(TermId).to_vec(),
            "source 0's terms first, then source 1's"
        );
    }

    /// A term is placed next to the terms it SHARES a source with even when a
    /// nearer index shares nothing, and a dual factor's two sources both count.
    #[test]
    fn affinity_follows_sources_not_indices() {
        // 0: {0,1} dual, 1: {5}, 2: {1}, 3: {5,6}
        let terms = vec![dual(0, 0, 1), c0(1, 5), c0(2, 1), c2(3, 5, 6)];
        let order = order_terms(&layer(7, terms));
        assert_eq!(order, [0, 2, 1, 3].map(TermId).to_vec());
    }

    /// A source EVERY term reads puts every unplaced term in the candidate set
    /// on every step — the path where the per-step score bookkeeping has to be
    /// reset correctly, and the one that decides whether the pass stays usable
    /// on a real layer's term count.
    #[test]
    fn order_survives_a_source_every_term_reads() {
        let terms: Vec<CoeffTerm> =
            (0..2_000u32).map(|index| c2(index, 0, 1 + index % 50)).collect();
        let order = order_terms(&layer(51, terms));
        assert_eq!(order.len(), 2_000);
        let mut sorted = order.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, (0..2_000).map(TermId).collect::<Vec<_>>());
    }

    #[test]
    fn term_sources_deduplicates_and_covers_both_projections() {
        assert_eq!(term_sources(&c0(0, 4)), vec![SourceId(4)]);
        assert_eq!(term_sources(&c2(1, 2, 2)), vec![SourceId(2)], "one source used twice");
        assert_eq!(term_sources(&dual(2, 3, 1)), vec![SourceId(1), SourceId(3)]);
        assert_eq!(
            term_sources(&c2(3, 1, 0)),
            vec![SourceId(0), SourceId(1)],
            "ascending, not operand order"
        );
    }
}
