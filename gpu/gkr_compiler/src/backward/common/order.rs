//! Backward term ordering and physical K-split.
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
/// Matched to the stride-`K` co-touch effect the order exists to create:
/// the window stands for the sources the warps running "around" the next term
/// are still touching, so it is sized for the warp neighbourhood, not for a
/// resident set — the evaluator has no resident state.
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
pub(crate) fn order_terms(layer: &CoeffLayer) -> Vec<TermId> {
    let rows: Vec<(u32, Vec<SourceId>, TermId)> = layer
        .terms
        .iter()
        .map(|term| (term.id().0, term_sources(term), term.id()))
        .collect();
    order_rows(rows)
}

/// The committed atom order: [`order_terms`] generalized from terms
/// to atoms — a plain term or a whole [`CoeffGroup`](super::model::CoeffGroup),
/// never split across the greedy placement.
///
/// A group's row is keyed by its lowest member `TermId` (unique across atoms,
/// since atoms partition `layer.terms`) and its signature is the sorted-deduped
/// union of every member's [`term_sources`]. A plain term keeps its own
/// `TermId`/sources. [`flatten_atoms`] turns the result back into a `TermId`
/// permutation for the artifact.
pub(crate) fn order_atoms(layer: &CoeffLayer) -> Vec<LeanAtomRef> {
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
        rows.push((
            term.id().0,
            term_sources(term),
            LeanAtomRef::Term(term.id()),
        ));
    }
    order_rows(rows)
}

/// Turn a committed atom order back into the `TermId` permutation the wire
/// encodes: a term atom emits itself, a group atom emits its members in the
/// group's own (ascending) order — the members of one group always land
/// contiguously, never interleaved with another atom's terms.
pub(crate) fn flatten_atoms(layer: &CoeffLayer, atoms: &[LeanAtomRef]) -> Vec<TermId> {
    let mut flat = Vec::with_capacity(layer.terms.len());
    for atom in atoms {
        match atom {
            LeanAtomRef::Term(id) => flat.push(*id),
            LeanAtomRef::Group(index) => {
                flat.extend(
                    layer.groups[*index]
                        .members
                        .iter()
                        .map(|member| member.term),
                );
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
/// `w, w+k, w+2k, …`.
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
    let mut lists: Vec<Vec<T>> = (0..k)
        .map(|w| Vec::with_capacity(items.len().saturating_sub(w).div_ceil(k)))
        .collect();
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
