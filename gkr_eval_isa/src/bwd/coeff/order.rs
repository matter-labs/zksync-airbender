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

use super::lean::LeanAtomRef;
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
///
/// The singleton instantiation of [`order_atoms`]' generic core: one row per
/// term, keyed by `TermId`. Kept as its own function — unchanged output is the
/// pin later atom-granular work is checked against.
pub fn order_terms(layer: &CoeffLayer) -> Vec<TermId> {
    let rows: Vec<(u32, Vec<SourceId>, TermId)> =
        layer.terms.iter().map(|term| (term.id().0, term_sources(term), term.id())).collect();
    order_rows(rows)
}

/// The committed ATOM order (spec §4.5): [`order_terms`] generalized from terms
/// to atoms — a plain term or a whole [`CoeffGroup`](super::model::CoeffGroup),
/// never split across the greedy placement.
///
/// A group's row is keyed by its lowest member `TermId` (unique across atoms,
/// since atoms partition `layer.terms`) and its signature is the sorted-deduped
/// union of every member's [`term_sources`]. A plain term keeps its own
/// `TermId`/sources. [`flatten_atoms`] turns the result back into a `TermId`
/// permutation for the artifact.
pub fn order_atoms(layer: &CoeffLayer) -> Vec<LeanAtomRef> {
    let mut grouped = vec![false; layer.terms.len()];
    let mut rows: Vec<(u32, Vec<SourceId>, LeanAtomRef)> = Vec::with_capacity(layer.terms.len());
    for (index, group) in layer.groups.iter().enumerate() {
        let mut sources = Vec::new();
        for member in &group.members {
            grouped[member.term.0 as usize] = true;
            sources.extend(term_sources(&layer.terms[member.term.0 as usize]));
        }
        sources.sort_unstable();
        sources.dedup();
        let key = group.members[0].term.0;
        rows.push((key, sources, LeanAtomRef::Group(index)));
    }
    for term in &layer.terms {
        if grouped[term.id().0 as usize] {
            continue;
        }
        rows.push((term.id().0, term_sources(term), LeanAtomRef::Term(term.id())));
    }
    order_rows(rows)
}

/// Turn a committed atom order back into the `TermId` permutation the wire
/// encodes: a term atom emits itself, a group atom emits its members in the
/// group's own (ascending) order — the members of one group always land
/// contiguously, never interleaved with another atom's terms.
pub fn flatten_atoms(layer: &CoeffLayer, atoms: &[LeanAtomRef]) -> Vec<TermId> {
    let mut flat = Vec::with_capacity(layer.terms.len());
    for atom in atoms {
        match atom {
            LeanAtomRef::Term(id) => flat.push(*id),
            LeanAtomRef::Group(index) => {
                flat.extend(layer.groups[*index].members.iter().map(|member| member.term));
            }
        }
    }
    flat
}

/// The greedy source-affinity core shared by [`order_terms`] and
/// [`order_atoms`]: `rows` is `(atom_key, sources, value)` — `key` only decides
/// the pre-sort (so ties fall back to the lowest atom key) and is otherwise
/// unused, `value` is carried through untouched to the result.
///
/// Repeatedly emits the unplaced row sharing the most DISTINCT sources with the
/// union of the sources of the last `AFFINITY_WINDOW` emitted rows; ties, and a
/// window that shares nothing with any unplaced row, fall back to the lowest
/// unplaced row in the sorted table.
fn order_rows<T: Copy>(mut rows: Vec<(u32, Vec<SourceId>, T)>) -> Vec<T> {
    rows.sort_by_key(|(key, _, _)| *key);
    let count = rows.len();
    // Inverted index: only a row sharing a source with the window can score at
    // all, so a step scores the window's neighbourhood instead of every
    // unplaced row.
    let mut users: BTreeMap<SourceId, Vec<usize>> = BTreeMap::new();
    for (row, (_, row_sources, _)) in rows.iter().enumerate() {
        for &source in row_sources {
            users.entry(source).or_default().push(row);
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
            for &row in &users[source] {
                if placed[row] {
                    continue;
                }
                if shared[row] == 0 {
                    candidates.push(row);
                }
                shared[row] += 1;
            }
        }
        // `max_by_key` keeps the LAST maximum, so the reversed index makes the
        // lowest sorted-table position the unique winner of a tie.
        let next = candidates
            .iter()
            .copied()
            .max_by_key(|&row| (shared[row], std::cmp::Reverse(row)))
            .unwrap_or(lowest_unplaced);
        for &row in &candidates {
            shared[row] = 0;
        }
        candidates.clear();

        placed[next] = true;
        emitted.push(next);
        while lowest_unplaced < count && placed[lowest_unplaced] {
            lowest_unplaced += 1;
        }
        window.clear();
        for &row in emitted.iter().rev().take(AFFINITY_WINDOW) {
            window.extend(rows[row].1.iter().copied());
        }
    }
    emitted.into_iter().map(|row| rows[row].2).collect()
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
    use crate::bwd::coeff::model::{
        CoeffGroup, CoeffGroupMember, CoeffSource, CoefficientRecipeId, ImmediateId, ProjectionId,
    };
    use crate::bwd::coeff::order_covers_layer;
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
            groups: Vec::new(),
            immediates: Vec::new(),
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

    // ── Atom-granular order ─────────────────────────────────────────────────

    /// Two groups `{0,1}` and `{2,3}`, plus singleton terms `4..7` — enough
    /// atoms to exercise both group-vs-group and group-vs-singleton affinity.
    fn grouped_layer() -> CoeffLayer {
        let terms = vec![
            c0(0, 0),
            c0(1, 1),
            c0(2, 2),
            c0(3, 3),
            c0(4, 0),
            c0(5, 1),
            c0(6, 2),
            c0(7, 3),
        ];
        let mut built = layer(4, terms);
        built.groups = vec![
            CoeffGroup {
                core: CoefficientRecipeId::from_bank_index(0),
                members: vec![
                    CoeffGroupMember { term: TermId(0), immediate: ImmediateId::ONE },
                    CoeffGroupMember { term: TermId(1), immediate: ImmediateId::banked(0) },
                ],
                has_c0: true,
                has_c2: false,
            },
            CoeffGroup {
                core: CoefficientRecipeId::from_bank_index(1),
                members: vec![
                    CoeffGroupMember { term: TermId(2), immediate: ImmediateId::NEG_ONE },
                    CoeffGroupMember { term: TermId(3), immediate: ImmediateId::banked(1) },
                ],
                has_c0: true,
                has_c2: false,
            },
        ];
        built.immediates = vec![7, 9];
        built
    }

    /// `flatten_atoms(order_atoms(..))` names every term of a grouped layer
    /// exactly once — a permutation, same as [`order_terms`].
    #[test]
    fn atoms_flatten_to_a_term_permutation() {
        let grouped = grouped_layer();
        let flat = flatten_atoms(&grouped, &order_atoms(&grouped));
        assert!(order_covers_layer(&flat, grouped.terms.len()), "every term exactly once");
    }

    /// With no groups every atom is a singleton term, so the atom order,
    /// flattened, is exactly [`order_terms`]'s output.
    #[test]
    fn groupless_layer_matches_order_terms() {
        let terms = vec![
            c0(0, 3),
            c2(1, 0, 1),
            dual(2, 2, 3),
            c0(3, 1),
            c2(4, 2, 2),
            c0(5, 0),
            dual(6, 1, 2),
        ];
        let built = layer(4, terms);
        let flat = flatten_atoms(&built, &order_atoms(&built));
        assert_eq!(flat, order_terms(&built));
    }

    /// The atom order is a pure function of the layer, same as [`order_terms`].
    #[test]
    fn order_is_deterministic() {
        let grouped = grouped_layer();
        assert_eq!(
            order_atoms(&grouped),
            order_atoms(&grouped),
            "ordering is a pure function of the layer"
        );
    }

    /// A group atom never straddles the flattening: its members land as one
    /// contiguous, internally-ordered run of the flattened `TermId` list.
    #[test]
    fn group_members_stay_contiguous_in_flatten() {
        let grouped = grouped_layer();
        let flat = flatten_atoms(&grouped, &order_atoms(&grouped));
        for group in &grouped.groups {
            let member_ids: Vec<TermId> = group.members.iter().map(|member| member.term).collect();
            let start = flat
                .iter()
                .position(|id| *id == member_ids[0])
                .expect("every group member is in the flattened order");
            assert_eq!(
                &flat[start..start + member_ids.len()],
                member_ids.as_slice(),
                "group members land contiguously and in the group's own order"
            );
        }
    }
}
