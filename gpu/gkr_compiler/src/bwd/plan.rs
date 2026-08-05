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

use gkr_eval_ir::ExprId;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PlanReplayError {
    RetainWithoutNextServe { entry: usize, value: ExprId },
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
        Self::try_new(plan).unwrap_or_else(|error| match error {
            PlanReplayError::RetainWithoutNextServe { entry, value } => panic!(
                "plan-construction bug: Retain entry at index {entry} for value {value:?} has no next serve"
            ),
        })
    }

    pub fn try_new(plan: &BwdOccurrencePlan) -> Result<Self, PlanReplayError> {
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
                if slot_of[i] + 1 >= occurrences.len() {
                    return Err(PlanReplayError::RetainWithoutNextServe {
                        entry: i,
                        value: e.fp.value,
                    });
                }
            }
        }

        let value_cursor = by_value.keys().map(|&v| (v, 0usize)).collect();

        Ok(PlanRun {
            entries,
            pos: 0,
            diverged: None,
            by_value,
            value_cursor,
            retained: BTreeMap::new(),
        })
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

    /// Count of `v`'s plan entries not yet consumed by `on_serve` (its occurrence
    /// cursor lag). `0` = DEAD (no future planned use) — the primary key of the
    /// expired-victim eviction order (Task 4, spec §4 rule b: "dead first"). A value
    /// absent from the plan returns `0`.
    pub fn remaining(&self, v: ExprId) -> usize {
        match (self.by_value.get(&v), self.value_cursor.get(&v)) {
            (Some(occ), Some(&cursor)) => occ.len().saturating_sub(cursor),
            _ => 0,
        }
    }
}

// ── plan entries fingerprint (Task 4 staleness guard) ───────────────────────────

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

#[inline]
fn fnv_u64(h: &mut u64, v: u64) {
    for &b in &v.to_le_bytes() {
        *h ^= b as u64;
        *h = h.wrapping_mul(FNV_PRIME);
    }
}

/// FNV-1a fingerprint over the ordered plan entries — every field of every
/// `PlanEntry` (`term`, serve kind, value, consumer, action), in order. Paired with
/// [`plan_epoch`](super::trace::plan_epoch) as the two staleness guards
/// [`compile_distilled_planned`](super::compile::compile_distilled_planned) checks at
/// apply start: `epoch` pins the plan to a `(layer, budget, mode)` regime, this pins
/// the plan's exact entry stream so a corrupted / re-ordered / wrong-length entries
/// vector can never be replayed silently. Callers building a plan set
/// `BwdOccurrencePlan::entries_fnv` to this over their `entries`.
pub fn plan_entries_fnv(entries: &[PlanEntry]) -> u64 {
    let mut h = FNV_OFFSET;
    fnv_u64(&mut h, entries.len() as u64);
    for e in entries {
        fnv_u64(&mut h, e.fp.term as u64);
        fnv_u64(&mut h, e.fp.kind as u64);
        fnv_u64(&mut h, e.fp.value.0 as u64);
        // `None` and any real `ExprId` are distinguished by the presence flag.
        match e.fp.consumer {
            Some(c) => {
                fnv_u64(&mut h, 1);
                fnv_u64(&mut h, c.0 as u64);
            }
            None => fnv_u64(&mut h, 0),
        }
        fnv_u64(&mut h, e.action as u64);
    }
    h
}
