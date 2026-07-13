//! Task 3 (CS-M0): the §4 plan ABI types + a pure, fail-closed fingerprint
//! matcher (`PlanRun`) that later tasks drive plan-based backward lowering
//! with. No fixtures, no compiler dependency — this module consumes only
//! [`BwdFingerprint`]/[`BwdServeKind`] (Task 1) and is otherwise a standalone
//! state machine over a precomputed [`BwdOccurrencePlan`].
//!
//! ## Retention interval model
//!
//! A `Retain` entry opens exactly ONE gap for its value; that value's NEXT
//! entry (Retain or Bypass) closes it — closing happens unconditionally on
//! arrival, because the arriving serve is itself the gap's endpoint. `Bypass`
//! never leaves a retention open. There is no multi-owner concept: a value
//! has at most one active retention at a time. So a `Retain, Bypass, Bypass`
//! chain on a 3-use value means: resident+hit (free) at serve 2, released
//! immediately after serve 2, and recomputed at serve 3 — `retention(v)` is
//! `Some(closes_at)` only in the window between the opening serve and the
//! next serve, never beyond it.
//!
//! ## Fail-closed
//!
//! Once the actual serve stream diverges from the plan's expected next entry,
//! every subsequent `on_serve` call returns `Bypass` — including ones whose
//! fingerprint would otherwise match again — and `diverged()` remembers the
//! first divergence index. `finish()` additionally catches EOF divergence:
//! unconsumed plan entries at the end of lowering (e.g. a suppressed
//! duplicate that silently consumed its twin's entry) are a mismatch too.

use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::ExprId;

use super::trace::BwdFingerprint;

/// What a matched plan entry tells the replaying compile to do with the
/// served value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlanAction {
    /// Serve from residency (no recompute) and, if this is the value's last
    /// planned use, keep it resident until its next serve closes the gap.
    Retain,
    /// Serve without opening (or keeping open) any retention.
    Bypass,
}

/// One planned occurrence: the fingerprint it must match against the actual
/// serve stream, plus the action to take when it matches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlanEntry {
    pub fp: BwdFingerprint,
    pub action: PlanAction,
}

/// A frozen backward occurrence plan: the ordered sequence of expected serves
/// (`entries`) for one `(epoch, stream_reductions)` regime. `epoch` and
/// `entries_fnv` are round-trip/staleness guards checked once at apply start
/// (Task 4, not here) — `PlanRun` consumes only `entries`.
#[derive(Clone, Debug)]
pub struct BwdOccurrencePlan {
    pub epoch: u64,
    pub entries_fnv: u64,
    pub stream_reductions: bool,
    pub entries: Vec<PlanEntry>,
}

/// A live replay of a [`BwdOccurrencePlan`] against an actual serve stream:
/// the fail-closed fingerprint matcher plus the retention-interval tracker.
pub(crate) struct PlanRun {
    entries: Vec<PlanEntry>,
    pos: usize,
    diverged: Option<usize>,
    /// For each value, the ascending list of entry indices (into `entries`)
    /// at which it occurs.
    by_value: BTreeMap<ExprId, Vec<usize>>,
    /// For each value, the slot (index into `by_value[v]`) of its next
    /// not-yet-consumed occurrence.
    value_cursor: BTreeMap<ExprId, usize>,
    /// The currently active retention per value: `v -> closes_at` (the entry
    /// index of `v`'s next serve). Absent iff no retention is open for `v`.
    retained: BTreeMap<ExprId, usize>,
}

impl PlanRun {
    pub fn new(plan: &BwdOccurrencePlan) -> Self {
        let entries = plan.entries.clone();

        // Precompute, per value, its ascending occurrence list, and record
        // each entry's slot within its own value's list as we go.
        let mut by_value: BTreeMap<ExprId, Vec<usize>> = BTreeMap::new();
        let mut slot_of: Vec<usize> = Vec::with_capacity(entries.len());
        for (i, e) in entries.iter().enumerate() {
            let occurrences = by_value.entry(e.fp.value).or_default();
            slot_of.push(occurrences.len());
            occurrences.push(i);
        }

        // A `Retain` entry always has a next entry for its value — a
        // `Retain` with no next serve is a plan-construction bug.
        for (i, e) in entries.iter().enumerate() {
            if e.action == PlanAction::Retain {
                let occurrences = &by_value[&e.fp.value];
                assert!(
                    slot_of[i] + 1 < occurrences.len(),
                    "plan-construction bug: Retain entry at index {i} for value {:?} has no next serve",
                    e.fp.value,
                );
            }
        }

        let value_cursor = by_value.keys().map(|&v| (v, 0usize)).collect();

        PlanRun {
            entries,
            pos: 0,
            diverged: None,
            by_value,
            value_cursor,
            retained: BTreeMap::new(),
        }
    }

    /// The entry index of `value`'s next entry after `pos` (`pos` must be the
    /// entry index of `value`'s currently-consumed occurrence). Panics if
    /// there is none — guaranteed not to happen for a `Retain` entry by the
    /// assertion in `new`.
    fn next_entry_of(&self, value: ExprId, pos: usize) -> usize {
        let occurrences = &self.by_value[&value];
        let slot = self.value_cursor[&value];
        debug_assert_eq!(
            occurrences[slot], pos,
            "value_cursor out of sync with the entry index being consumed"
        );
        occurrences[slot + 1]
    }

    /// Advance `value`'s occurrence cursor past the entry just consumed.
    fn advance_value_cursor(&mut self, value: ExprId) {
        if let Some(c) = self.value_cursor.get_mut(&value) {
            *c += 1;
        }
    }

    pub fn on_serve(&mut self, fp: &BwdFingerprint) -> PlanAction {
        if self.diverged.is_some() {
            return PlanAction::Bypass;
        }
        match self.entries.get(self.pos) {
            // Copy `e` out of the `self.entries` borrow immediately (`PlanEntry`
            // is `Copy`) so the mutations below (which need `&mut self`) don't
            // conflict with it — a syntactic requirement only, identical to the
            // brief's shape in every observable respect.
            Some(e) if e.fp == *fp => {
                let e = *e;
                self.retained.remove(&fp.value); // arriving serve closes the open gap
                if e.action == PlanAction::Retain {
                    self.retained
                        .insert(fp.value, self.next_entry_of(fp.value, self.pos));
                }
                self.pos += 1;
                self.advance_value_cursor(fp.value);
                e.action
            }
            _ => {
                self.diverged = Some(self.pos);
                PlanAction::Bypass
            }
        }
    }

    pub fn diverged(&self) -> Option<usize> {
        self.diverged
    }

    /// Called once when lowering completes: unconsumed expected entries are
    /// a mismatch too (EOF divergence), catching e.g. a suppressed duplicate
    /// that silently consumed its twin's entry.
    pub fn finish(&mut self) {
        if self.diverged.is_none() && self.pos < self.entries.len() {
            self.diverged = Some(self.pos);
        }
    }

    /// The active retention's `closes_at` entry index for `v`, if any.
    pub fn retention(&self, v: ExprId) -> Option<usize> {
        self.retained.get(&v).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bwd::trace::BwdServeKind;

    fn fp(term: u32, value: u32, consumer: Option<u32>) -> BwdFingerprint {
        BwdFingerprint {
            term,
            kind: BwdServeKind::Operand,
            value: ExprId(value),
            consumer: consumer.map(ExprId),
        }
    }

    fn plan(entries: Vec<PlanEntry>) -> BwdOccurrencePlan {
        BwdOccurrencePlan {
            epoch: 1,
            entries_fnv: 1,
            stream_reductions: false,
            entries,
        }
    }

    // (a) exact-match sequence consumes all entries and returns the planned
    // actions in order.
    #[test]
    fn exact_match_sequence_returns_planned_actions_in_order() {
        let fp_a = fp(0, 10, None);
        let fp_b1 = fp(1, 11, Some(10));
        // Value 11's second occurrence — required so entry 1's `Retain` has a
        // next serve for its value (the `PlanRun::new` invariant).
        let fp_b2 = fp(2, 11, Some(10));
        let p = plan(vec![
            PlanEntry {
                fp: fp_a,
                action: PlanAction::Bypass,
            },
            PlanEntry {
                fp: fp_b1,
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: fp_b2,
                action: PlanAction::Bypass,
            },
        ]);
        let mut run = PlanRun::new(&p);

        assert_eq!(run.on_serve(&fp_a), PlanAction::Bypass);
        assert_eq!(run.on_serve(&fp_b1), PlanAction::Retain);
        assert_eq!(run.on_serve(&fp_b2), PlanAction::Bypass);
        assert_eq!(run.diverged(), None);
    }

    // (b) first mismatch (synthetic cone suppression: an expected serve is
    // missing from the actual stream) returns Bypass for EVERY subsequent
    // serve, including ones whose fingerprints would match again, and
    // `diverged()` remembers the first divergence index.
    #[test]
    fn first_mismatch_is_fail_closed_for_all_later_serves() {
        let fp_a = fp(0, 20, None);
        let fp_b = fp(1, 21, Some(20));
        let fp_c = fp(2, 22, Some(21));
        // Value 20's second occurrence — required so entry 0's `Retain` has a
        // next serve for its value (the `PlanRun::new` invariant). It is
        // never actually served in this test — the point is that a real
        // fail-closed matcher must not reach it via `next_entry_of` either,
        // since divergence happens first.
        let fp_a2 = fp(3, 20, Some(22));
        let p = plan(vec![
            PlanEntry {
                fp: fp_a,
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: fp_b,
                action: PlanAction::Bypass,
            },
            PlanEntry {
                fp: fp_c,
                action: PlanAction::Bypass,
            },
            PlanEntry {
                fp: fp_a2,
                action: PlanAction::Bypass,
            },
        ]);
        let mut run = PlanRun::new(&p);

        // fp_a serves as expected.
        assert_eq!(run.on_serve(&fp_a), PlanAction::Retain);
        // fp_b is suppressed from the actual stream (synthetic cone
        // suppression) — the next actual serve is fp_c, which mismatches
        // the plan's expected next entry (fp_b) at pos 1.
        assert_eq!(run.on_serve(&fp_c), PlanAction::Bypass);
        assert_eq!(run.diverged(), Some(1));

        // Even a late arrival of fp_b — which WOULD match entries[1] if the
        // matcher weren't fail-closed — still returns Bypass forever after.
        assert_eq!(run.on_serve(&fp_b), PlanAction::Bypass);
        assert_eq!(run.diverged(), Some(1));
    }

    // (c) repeated identical fingerprints (same (term, kind, value,
    // consumer) twice) map to their two distinct entries in order.
    #[test]
    fn repeated_identical_fingerprints_map_to_distinct_entries_in_order() {
        let fp_x = fp(0, 30, Some(31));
        let p = plan(vec![
            PlanEntry {
                fp: fp_x,
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: fp_x,
                action: PlanAction::Bypass,
            },
        ]);
        let mut run = PlanRun::new(&p);

        assert_eq!(run.on_serve(&fp_x), PlanAction::Retain);
        assert_eq!(run.on_serve(&fp_x), PlanAction::Bypass);
        assert_eq!(run.diverged(), None);
    }

    // (d) duplicate deletion is caught: same plan as (c), but the actual
    // stream serves the duplicate only ONCE — the single serve consumes the
    // first entry, and `finish()` must record divergence for the orphaned
    // second entry.
    #[test]
    fn suppressed_duplicate_serve_is_caught_by_finish() {
        let fp_x = fp(0, 40, Some(41));
        let p = plan(vec![
            PlanEntry {
                fp: fp_x,
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: fp_x,
                action: PlanAction::Bypass,
            },
        ]);
        let mut run = PlanRun::new(&p);

        assert_eq!(run.on_serve(&fp_x), PlanAction::Retain);
        // The duplicate serve never arrives.
        assert_eq!(run.diverged(), None); // not yet — only detectable at EOF
        run.finish();
        assert_eq!(run.diverged(), Some(1));
    }

    // (e) retention interval semantics: Retain, Bypass, Bypass — retention(v)
    // is Some only between serve 1 and serve 2, None after serve 2 (never
    // re-armed through serve 3).
    #[test]
    fn retention_is_open_only_between_its_opening_serve_and_the_next() {
        let fp_v1 = fp(0, 50, None);
        let fp_v2 = fp(1, 50, Some(50));
        let fp_v3 = fp(2, 50, Some(50));
        let v = ExprId(50);
        let p = plan(vec![
            PlanEntry {
                fp: fp_v1,
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: fp_v2,
                action: PlanAction::Bypass,
            },
            PlanEntry {
                fp: fp_v3,
                action: PlanAction::Bypass,
            },
        ]);
        let mut run = PlanRun::new(&p);

        assert_eq!(run.retention(v), None);

        assert_eq!(run.on_serve(&fp_v1), PlanAction::Retain);
        assert_eq!(run.retention(v), Some(1)); // gap opened, closes at entry 1

        assert_eq!(run.on_serve(&fp_v2), PlanAction::Bypass);
        assert_eq!(run.retention(v), None); // Bypass closed it and did not reopen

        assert_eq!(run.on_serve(&fp_v3), PlanAction::Bypass);
        assert_eq!(run.retention(v), None); // still none — never through serve 3
    }

    // (f) finish() on a fully-consumed stream leaves diverged() == None.
    #[test]
    fn finish_on_fully_consumed_stream_stays_not_diverged() {
        let fp_a = fp(0, 60, None);
        let fp_b1 = fp(1, 61, Some(60));
        // Value 61's second occurrence — required so entry 1's `Retain` has
        // a next serve for its value; consumed here too so the stream ends
        // fully consumed.
        let fp_b2 = fp(2, 61, Some(60));
        let p = plan(vec![
            PlanEntry {
                fp: fp_a,
                action: PlanAction::Bypass,
            },
            PlanEntry {
                fp: fp_b1,
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: fp_b2,
                action: PlanAction::Bypass,
            },
        ]);
        let mut run = PlanRun::new(&p);

        assert_eq!(run.on_serve(&fp_a), PlanAction::Bypass);
        assert_eq!(run.on_serve(&fp_b1), PlanAction::Retain);
        assert_eq!(run.on_serve(&fp_b2), PlanAction::Bypass);
        run.finish();
        assert_eq!(run.diverged(), None);
    }
}
