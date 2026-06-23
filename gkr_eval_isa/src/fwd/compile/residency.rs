//! Stage-2 Belady cell planner: pure per-layer residency planning.
//!
//! Given a `RefString` (the ordered sequence of produce/use/temp events for a
//! layer) and the `ValueGraph` facts from `analyze.rs`, `ResidencyState` tracks
//! which values currently occupy smem cells and, on eviction pressure, applies
//! the Belady optimal replacement policy with a lexicographic `MissPenalty`
//! primary key (cheapest-to-evict first) and farthest-next-use tiebreaker.
//!
//! This module is PURE: it never emits instructions. The Stage-3 emitter
//! consults `location` and `admit` to decide where each value lives and how to
//! re-obtain an evicted one.

use super::analyze::{MissPenalty, ValueId, ValueInfo};
use super::schedule::CellAllocator;
use super::super::error::CompileError;
use super::super::isa::OperandField;
use std::collections::{BTreeMap, HashMap};

// ── Reference-string event ────────────────────────────────────────────────────

/// A single event in the ordered reference stream for a layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RefEvent {
    /// A value becomes available (root materialise / first load).
    Produce(ValueId),
    /// A value is read as an operand here.
    Use(ValueId),
    /// The emitter is about to lower an expression needing `N` temp cells.
    LoweringTempNeed(usize),
    /// Zero-lane `CopyAlias` terminal use (stabilise / pin).
    AliasResolve(ValueId),
}

/// The ordered sequence of reference events for one layer.
#[derive(Clone, Debug, Default)]
pub struct RefString {
    pub events: Vec<RefEvent>,
}

// ── Value location / re-obtain descriptor ────────────────────────────────────

/// Where a value currently lives, or how to re-obtain it if not resident.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Loc {
    /// Resident in smem cell `c`.
    Smem(u16),
    /// Tier-0: carried in the accumulator.
    Acc,
    /// Not resident; re-read from a real DRAM global backing
    /// (`SourceKind::Read` / `VirtualSetup` / `Prior`).
    SourceDram,
    /// Not resident AND no DRAM home (a shared compound subexpr) — re-lower it.
    Recompute,
    /// Deliberately spilled to a scratch cell-backing column; re-read from there.
    Spill(u16),
}

// ── ResidencyState ────────────────────────────────────────────────────────────

/// Per-layer smem residency planner.
///
/// Backed by `CellAllocator` for placement/alignment. Uses Belady optimal
/// replacement with a lexicographic `MissPenalty` primary key (cheapest miss
/// evicted first) and farthest-next-use tiebreaker.
///
/// All iteration over `ValueId` uses `BTreeMap` or sorted order for
/// determinism — the output feeds instruction emission which must be
/// byte-reproducible.
pub struct ResidencyState {
    /// Cell allocator — tracks occupied/free cells and alignment.
    alloc: CellAllocator,
    /// Currently resident values: ValueId → smem base cell.
    resident: BTreeMap<ValueId, u16>,
    /// Reverse map: base cell → ValueId (for eviction debugging; cell 0 is Base
    /// or Ext base).
    cell_to_value: BTreeMap<u16, ValueId>,
    /// Active resident borrows: ValueId → outstanding borrow count. A resident
    /// value with a live borrow is an in-flight operand of a pending fold (its
    /// `Smem{cell}` is already baked into the instruction stream but the consuming
    /// ADD/MUL/FMA has not run yet), so its cell MUST NOT be evicted/reused until
    /// the borrow is released. `eviction_order` skips every value present here.
    /// This is the lease that closes the codex round-1 in-flight-borrow hole.
    borrowed: BTreeMap<ValueId, u32>,
    /// Per-value facts (field, miss penalty, has_backing).
    info: HashMap<ValueId, ValueInfo>,
    /// Precomputed: for each (ValueId, point), the index of the next `Use` event
    /// at or after `point`. Stored as a sorted list of use-event indices per
    /// value; binary search gives the next use.
    next_uses: HashMap<ValueId, Vec<usize>>,
}

impl ResidencyState {
    /// Build a new planner from the reference string and value info.
    ///
    /// Precomputes next-use distances from `refs` for every `ValueId`.
    pub fn new(refs: &RefString, info: &HashMap<ValueId, ValueInfo>, budget: usize) -> Self {
        // Precompute: for each ValueId, the sorted list of event indices at which
        // a `Use` event occurs.  Binary search gives O(log n) next-use lookup.
        let mut next_uses: HashMap<ValueId, Vec<usize>> = HashMap::new();
        for (idx, ev) in refs.events.iter().enumerate() {
            if let RefEvent::Use(v) = ev {
                next_uses.entry(*v).or_default().push(idx);
            }
        }
        // Each list is already in ascending order (we iterate events in order).

        ResidencyState {
            alloc: CellAllocator::new(budget),
            resident: BTreeMap::new(),
            cell_to_value: BTreeMap::new(),
            borrowed: BTreeMap::new(),
            info: info.clone(),
            next_uses,
        }
    }

    /// Belady-admit value `v` at event index `point`.
    ///
    /// If a fitting free block exists, places `v` without eviction.
    /// Otherwise evicts the victim set minimising lost future benefit
    /// (lexicographic `MissPenalty`, farthest-next-use tiebreak) until a
    /// fitting aligned block is free, then places `v`.
    ///
    /// Returns `Ok(Loc::Smem(cell))` on success, or
    /// `Err(CompileError::BudgetBelowFloor)` if even clearing all residents
    /// cannot yield the required aligned block.
    pub fn admit(&mut self, v: ValueId, point: usize) -> Result<Loc, CompileError> {
        if let Some(&cell) = self.resident.get(&v) {
            return Ok(Loc::Smem(cell));
        }
        let field = self.info.get(&v).map(|i| i.field).unwrap_or(OperandField::Base);

        // Try a direct alloc first (may succeed if there is a free slot).
        let initial_err = match self.alloc.alloc(field) {
            Ok(cell) => {
                self.resident.insert(v, cell);
                self.cell_to_value.insert(cell, v);
                return Ok(Loc::Smem(cell));
            }
            Err(e) => e,
        };

        // Need to evict.  Build the candidate eviction order: sorted by
        // (MissPenalty ascending, next_use descending) — cheapest-miss first,
        // farthest-use as tiebreaker.
        let eviction_order = self.eviction_order(point);

        let mut last_alloc_err = initial_err;
        for victim_id in eviction_order {
            let victim_cell = match self.resident.get(&victim_id) {
                Some(&c) => c,
                None => continue,
            };
            // Evict the victim.
            self.resident.remove(&victim_id);
            self.cell_to_value.remove(&victim_cell);
            self.alloc.free(victim_cell);

            // Try to alloc again.
            match self.alloc.alloc(field) {
                Ok(cell) => {
                    self.resident.insert(v, cell);
                    self.cell_to_value.insert(cell, v);
                    return Ok(Loc::Smem(cell));
                }
                Err(e) => { last_alloc_err = e; } // keep evicting
            }
        }

        // Even with all residents evicted, no fit.
        Err(last_alloc_err)
    }

    /// Return the current location of `v` at event index `point`.
    ///
    /// - Resident → `Smem(cell)`.
    /// - Not resident → `SourceDram` if the value has a real DRAM backing,
    ///   `Recompute` otherwise (compound subexpr, no backing).
    ///
    /// This is non-fallible: it simply reads the current resident map.
    pub fn location(&self, v: ValueId, _point: usize) -> Loc {
        if let Some(&cell) = self.resident.get(&v) {
            return Loc::Smem(cell);
        }
        // Not resident — determine re-obtain strategy.
        match self.info.get(&v) {
            Some(info) if info.has_backing => Loc::SourceDram,
            _ => Loc::Recompute,
        }
    }

    // ── On-demand transient allocation + resident borrow leases ───────────────
    //
    // These replace the static `ensure_temp_capacity` reservation model with the
    // one-shared-allocator + lazy-eviction design: the emitter asks for a transient
    // cell exactly when a compound child must materialize, and the planner evicts a
    // backed (re-readable) resident on demand to make room — emitting nothing; the
    // evicted value's future uses re-resolve via `location` (backed → `SourceDram`,
    // unbacked → `Recompute`). Borrowed residents are protected (see `borrowed`).

    /// Allocate a transient lowering cell for a value of `field`, evicting the
    /// cheapest-to-reobtain *unborrowed* resident on demand if no free block fits.
    ///
    /// The returned cell is NOT recorded as a resident — it is a transient temp the
    /// caller owns and must return via `free_temp` once the operand it backs has been
    /// consumed. Eviction emits no instructions: an evicted resident's later uses
    /// re-resolve through `location`. Returns `Err(BudgetBelowFloor)` only when no
    /// evictable (unborrowed) resident remains and the demand still won't fit — i.e.
    /// the budget is genuinely below the aligned schedule floor.
    pub fn alloc_temp(&mut self, field: OperandField, point: usize) -> Result<u16, CompileError> {
        // Direct fit first.
        let initial_err = match self.alloc.alloc(field) {
            Ok(cell) => return Ok(cell),
            Err(e) => e,
        };
        // Evict cheapest-miss / farthest-next-use unborrowed residents until it fits.
        let order = self.eviction_order(point);
        let mut last_err = initial_err;
        for victim_id in order {
            let victim_cell = match self.resident.get(&victim_id) {
                Some(&c) => c,
                None => continue,
            };
            self.resident.remove(&victim_id);
            self.cell_to_value.remove(&victim_cell);
            self.alloc.free(victim_cell);
            match self.alloc.alloc(field) {
                Ok(cell) => return Ok(cell),
                Err(e) => last_err = e,
            }
        }
        Err(last_err)
    }

    /// Return a transient cell allocated by `alloc_temp` to the free pool.
    /// Transient cells are never residents, so this only frees allocator space.
    pub fn free_temp(&mut self, cell: u16) {
        self.alloc.free(cell);
    }

    /// Borrow resident value `v` as an in-flight operand: pin its cell against
    /// eviction for the lifetime of the borrow and return the cell. Returns `None`
    /// when `v` is not resident (the caller then re-resolves via `location` —
    /// backed → DRAM `Global`, unbacked → `Recompute`). Borrowing reads the cell `v`
    /// already occupies; it allocates nothing. Balance every `Some` with
    /// `release_borrow` once the consuming fold has been emitted.
    pub fn borrow_resident(&mut self, v: ValueId) -> Option<u16> {
        if let Some(&cell) = self.resident.get(&v) {
            *self.borrowed.entry(v).or_insert(0) += 1;
            Some(cell)
        } else {
            None
        }
    }

    /// Release one borrow of `v` taken by `borrow_resident`. Once the count reaches
    /// zero the value becomes an eviction candidate again.
    pub fn release_borrow(&mut self, v: ValueId) {
        if let Some(n) = self.borrowed.get_mut(&v) {
            *n -= 1;
            if *n == 0 {
                self.borrowed.remove(&v);
            }
        }
    }

    /// Whether `v` currently has a live borrow (its cell is pinned against eviction).
    pub fn is_borrowed(&self, v: ValueId) -> bool {
        self.borrowed.contains_key(&v)
    }

    /// True iff `v` was flagged a source-residency candidate by `analyze_layer`.
    pub fn is_source_resident_candidate(&self, v: ValueId) -> bool {
        self.info.get(&v).map(|i| i.is_source_resident).unwrap_or(false)
    }

    /// The operand field a value lives in (Base default if unknown).
    pub fn field_of(&self, v: ValueId) -> OperandField {
        self.info.get(&v).map(|i| i.field).unwrap_or(OperandField::Base)
    }

    /// High-water mark of simultaneously live smem cells over this planner's life.
    ///
    /// In the one-allocator design the shared `CellAllocator` is the single source of
    /// truth for occupancy: it tracks residents (via `admit`) and transient lowering
    /// temps (via `alloc_temp`) in one space, so its high-water IS the layer's peak
    /// live-cell count (residents + temps + evict partials).
    pub fn max_live_cells(&self) -> usize {
        self.alloc.max_live()
    }

    // ── Internal helpers ──────────────────────────────────────────────────────

    /// Compute the next `Use` event index for `v` strictly after `point`.
    /// Returns `usize::MAX` if there are no future uses.
    fn next_use_after(&self, v: ValueId, point: usize) -> usize {
        match self.next_uses.get(&v) {
            None => usize::MAX,
            Some(uses) => {
                // Binary search for the first index > point.
                match uses.binary_search(&point) {
                    Ok(pos) => {
                        // Exact match at `pos`; the NEXT use is at pos+1 (if any).
                        uses.get(pos + 1).copied().unwrap_or(usize::MAX)
                    }
                    Err(pos) => {
                        // pos is the insertion point; uses[pos] is the first index > point.
                        uses.get(pos).copied().unwrap_or(usize::MAX)
                    }
                }
            }
        }
    }

    /// Return a stable, deterministic eviction order: cheapest-miss first
    /// (lexicographic MissPenalty ascending), farthest-next-use tiebreaker
    /// (descending), ValueId as the final tiebreaker for byte-reproducibility.
    ///
    /// Only currently-resident values are included.
    fn eviction_order(&self, point: usize) -> Vec<ValueId> {
        let mut candidates: Vec<(ValueId, MissPenalty, usize)> = self
            .resident
            .keys()
            // Skip values with a live borrow: their `Smem{cell}` is already baked into
            // a pending fold's operands, so evicting them would corrupt that fold (the
            // codex round-1 in-flight-borrow hole). Only unborrowed residents are victims.
            .filter(|v| !self.borrowed.contains_key(v))
            .map(|&v| {
                let miss = self.info.get(&v).map(|i| i.miss).unwrap_or_default();
                let next = self.next_use_after(v, point);
                (v, miss, next)
            })
            .collect();

        // Sort: primary = miss penalty ascending (cheapest evicted first),
        // secondary = next_use descending (farthest evicted first),
        // tertiary = ValueId ascending (stable tiebreak).
        candidates.sort_by(|a, b| {
            let miss_a = (a.1.dram_reads, a.1.instrs, a.1.cell_ops);
            let miss_b = (b.1.dram_reads, b.1.instrs, b.1.cell_ops);
            miss_a
                .cmp(&miss_b)
                .then_with(|| b.2.cmp(&a.2)) // farthest first → descending
                .then_with(|| a.0.cmp(&b.0))  // ValueId = ExprId ascending
        });

        candidates.into_iter().map(|(v, _, _)| v).collect()
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fwd::compile::analyze::{MissPenalty, ValueInfo};
    use crate::fwd::isa::OperandField;
    use cs::gkr_compiler::dag_ir::ExprId;

    // ── Test helpers ──────────────────────────────────────────────────────────

    /// Synthetic ValueId helpers — wrap raw u32 into ExprId.
    fn vid(n: u32) -> ValueId { ExprId(n) }

    fn value_a() -> ValueId { vid(0) }
    fn value_b() -> ValueId { vid(1) }
    fn value_c() -> ValueId { vid(2) }
    fn ext_value() -> ValueId { vid(10) }
    fn compound_value() -> ValueId { vid(20) }

    /// Build a `ValueInfo` for a Base value with the given miss and backing flag.
    fn base_info(miss: MissPenalty, has_backing: bool) -> ValueInfo {
        ValueInfo {
            refcount: 2,
            field: OperandField::Base,
            width: 1,
            is_candidate: true,
            miss,
            has_backing,
            is_source_resident: false,
        }
    }

    /// Build a `ValueInfo` for an Ext value.
    fn ext_info(miss: MissPenalty, has_backing: bool) -> ValueInfo {
        ValueInfo {
            refcount: 2,
            field: OperandField::Ext,
            width: 4,
            is_candidate: true,
            miss,
            has_backing,
            is_source_resident: false,
        }
    }

    fn equal_miss() -> MissPenalty {
        MissPenalty { dram_reads: 1, instrs: 1, cell_ops: 0 }
    }
    fn cheap_miss() -> MissPenalty {
        MissPenalty { dram_reads: 1, instrs: 1, cell_ops: 0 }
    }
    fn expensive_miss() -> MissPenalty {
        MissPenalty { dram_reads: 3, instrs: 5, cell_ops: 2 }
    }

    // ── Test 1: Belady evicts farthest next-use ───────────────────────────────
    //
    // RefString layout:
    //   0: Produce(A)
    //   1: Produce(B)
    //   2: Use(B)          ← B used soon (at point 2)
    //   3: Produce(C)      ← admit C at point 3; must evict A (used farthest)
    //   4: Use(A)          ← A used later
    //
    // With budget=2, after admitting A and B (both fill the budget), admitting C
    // at point 3 requires eviction.  A's next use is at point 4 (farthest);
    // B's next use was already consumed at point 2, so its next use is usize::MAX?
    // Wait — we need B's next use to be SOONER than A's for A to be evicted.
    //
    // Revised layout to ensure A is farthest:
    //   0: Produce(A)
    //   1: Produce(B)
    //   2: Produce(C)      ← admit C at point 2; budget=2, so evict one of A or B
    //   3: Use(B)          ← B used at 3 (sooner)
    //   4: Use(A)          ← A used at 4 (farther)
    //   5: Use(C)

    fn refs_for_belady() -> RefString {
        RefString {
            events: vec![
                RefEvent::Produce(value_a()),  // 0
                RefEvent::Produce(value_b()),  // 1
                RefEvent::Produce(value_c()),  // 2 — triggers eviction
                RefEvent::Use(value_b()),      // 3 — B used soon after
                RefEvent::Use(value_a()),      // 4 — A used farther ahead
                RefEvent::Use(value_c()),      // 5
            ],
        }
    }

    fn info_all_base_equal_miss() -> HashMap<ValueId, ValueInfo> {
        let mut m = HashMap::new();
        m.insert(value_a(), base_info(equal_miss(), true));
        m.insert(value_b(), base_info(equal_miss(), true));
        m.insert(value_c(), base_info(equal_miss(), true));
        m
    }

    /// The point at which C is admitted (also the point used for location checks
    /// after `drive_to_admit` returns).
    fn c_point() -> usize { 2 }

    /// Drive the state to the point of admitting `ext_value()` or `value_c()`,
    /// first producing all prior values, then admitting the target.
    fn drive_to_admit(st: &mut ResidencyState, target: ValueId) -> Loc {
        // Produce A and B first (so they are resident).
        if target == value_c() || target == ext_value() {
            let _ = st.admit(value_a(), 0);
            let _ = st.admit(value_b(), 1);
        }
        // Now admit the target at its point.
        let point = if target == ext_value() { 3 } else { c_point() };
        st.admit(target, point).expect("admit must succeed")
    }

    // ── Test 2: Ext admission frees aligned victim set ────────────────────────
    //
    // budget=4: three Base residents in cells 0,1,2; 1 free cell.
    // Admitting an Ext (needs 4 aligned cells) requires evicting all 3 Base
    // residents to free a 4-aligned 4-cell block.
    //
    // RefString: Produce A,B,C (Base), then Produce Ext, then Use Ext.
    // No further uses for A/B/C → they are evicted freely.

    fn refs_three_base_then_ext() -> RefString {
        let a = vid(0); let b = vid(1); let c = vid(2); let e = ext_value();
        RefString {
            events: vec![
                RefEvent::Produce(a),   // 0
                RefEvent::Produce(b),   // 1
                RefEvent::Produce(c),   // 2
                RefEvent::Produce(e),   // 3 — triggers eviction
                RefEvent::Use(e),       // 4
            ],
        }
    }

    fn info() -> HashMap<ValueId, ValueInfo> {
        let mut m = HashMap::new();
        m.insert(vid(0), base_info(equal_miss(), true));
        m.insert(vid(1), base_info(equal_miss(), true));
        m.insert(vid(2), base_info(equal_miss(), true));
        m.insert(ext_value(), ext_info(equal_miss(), true));
        m
    }

    // ── Test 3: Lexicographic beats pure Belady on miss cost ─────────────────
    //
    // A and B have the same next-use distance (both used at point 4).
    // A has cheap miss (1 dram read), B has expensive miss (3 dram reads + more).
    // Admitting C at point 3 must evict A (cheaper to re-obtain).

    fn refs_a_b_tie_next_use() -> RefString {
        RefString {
            events: vec![
                RefEvent::Produce(value_a()),  // 0
                RefEvent::Produce(value_b()),  // 1
                RefEvent::Produce(value_c()),  // 2 — triggers eviction
                RefEvent::Use(value_a()),      // 3 — both at same distance from point 2
                RefEvent::Use(value_b()),      // 4
                RefEvent::Use(value_c()),      // 5
            ],
        }
    }

    fn info_a_cheap_b_expensive() -> HashMap<ValueId, ValueInfo> {
        let mut m = HashMap::new();
        m.insert(value_a(), base_info(cheap_miss(), true));
        m.insert(value_b(), base_info(expensive_miss(), true));
        m.insert(value_c(), base_info(equal_miss(), true));
        m
    }

    // ── Test 4: Evicted compound reobtains by Recompute ───────────────────────
    //
    // A compound (no backing) is admitted, then evicted (budget=1 means
    // admitting another value at `drive_past_eviction` evicts it), and its
    // location after eviction must be Recompute, not SourceDram.
    //
    // RefString: Produce compound (point 0); Produce some_other (point 1,
    // forces eviction); Use compound (point 2).

    fn refs_compound_evicted() -> RefString {
        let other = vid(99);
        RefString {
            events: vec![
                RefEvent::Produce(compound_value()),  // 0
                RefEvent::Produce(other),             // 1 — forces eviction (budget=1)
                RefEvent::Use(compound_value()),      // 2
            ],
        }
    }

    fn info_compound_no_backing() -> HashMap<ValueId, ValueInfo> {
        let mut m = HashMap::new();
        m.insert(compound_value(), base_info(
            MissPenalty { dram_reads: 0, instrs: 3, cell_ops: 0 },
            false, // NO backing — compound subexpr
        ));
        m.insert(vid(99), base_info(equal_miss(), true));
        m
    }

    fn later_use_point() -> usize { 2 }

    /// Drive the state past an eviction: admit compound, then admit `vid(99)`
    /// (which forces eviction of compound because budget=1).
    fn drive_past_eviction(st: &mut ResidencyState) {
        let _ = st.admit(compound_value(), 0);
        // vid(99) has lower miss cost (equal_miss dram_reads=1 vs compound's 0
        // dram_reads but higher instrs). Actually compound has dram_reads=0
        // and vid(99) has dram_reads=1, so compound is cheaper-miss → evicted first.
        let _ = st.admit(vid(99), 1);
    }

    // ── The 4 required tests ──────────────────────────────────────────────────

    #[test]
    fn belady_evicts_farthest_next_use() {
        let mut st = ResidencyState::new(&refs_for_belady(), &info_all_base_equal_miss(), 2);
        drive_to_admit(&mut st, value_c());
        assert_eq!(
            st.location(value_a(), c_point()),
            Loc::SourceDram,
            "farthest-next-use value evicted (source read → re-read)"
        );
        assert!(
            matches!(st.location(value_b(), c_point()), Loc::Smem(_)),
            "nearer-next-use value kept"
        );
    }

    #[test]
    fn ext_admission_frees_aligned_victim_set() {
        let mut st = ResidencyState::new(&refs_three_base_then_ext(), &info(), 4);
        let loc = drive_to_admit(&mut st, ext_value());
        assert!(
            matches!(loc, Loc::Smem(c) if c % 4 == 0),
            "Ext admitted into an aligned 4-cell block via a victim set"
        );
    }

    #[test]
    fn lexicographic_beats_pure_belady_on_miss_cost() {
        let mut st = ResidencyState::new(&refs_a_b_tie_next_use(), &info_a_cheap_b_expensive(), 2);
        drive_to_admit(&mut st, value_c());
        assert_eq!(
            st.location(value_a(), c_point()),
            Loc::SourceDram,
            "evict the cheaper-miss value on a next-use tie"
        );
        assert!(
            matches!(st.location(value_b(), c_point()), Loc::Smem(_)),
            "keep the expensive-recompute value"
        );
    }

    #[test]
    fn evicted_compound_reobtains_by_recompute_not_dram() {
        let mut st = ResidencyState::new(&refs_compound_evicted(), &info_compound_no_backing(), 1);
        drive_past_eviction(&mut st);
        let loc = st.location(compound_value(), later_use_point());
        assert!(
            matches!(loc, Loc::Recompute | Loc::Spill(_)),
            "evicted compound must recompute/spill, not SourceDram: {:?}",
            loc
        );
    }

    // ── Shared fixtures for the alloc_temp / borrow-lease / max_live tests ────
    //
    // Two Base residents (cells 0,1) with no further uses (so eviction is free).
    // Reused by `alloc_temp_evicts_backed_resident_on_demand`,
    // `alloc_temp_below_floor_when_only_resident_is_borrowed`, and
    // `max_live_tracks_residents_plus_live_temps`.

    fn refs_two_residents() -> RefString {
        RefString {
            events: vec![
                RefEvent::Produce(value_a()),  // 0
                RefEvent::Produce(value_b()),  // 1
            ],
        }
    }

    fn info_two_base() -> HashMap<ValueId, ValueInfo> {
        let mut m = HashMap::new();
        m.insert(value_a(), base_info(equal_miss(), true));
        m.insert(value_b(), base_info(equal_miss(), true));
        m
    }

    // ── On-demand alloc_temp + borrow lease ──────────────────────────────────

    // Must-have #1 (the codex round-1 in-flight-borrow guard): a resident borrowed
    // as a pending operand MUST NOT be evicted by a later transient alloc in the same
    // chunk. A (cheap miss) is the natural eviction victim; borrowing it must force
    // alloc_temp to evict B (expensive miss) instead. WITHOUT the borrow lease,
    // alloc_temp evicts cheapest-miss A and the temp reuses A's cell — corrupting the
    // in-flight borrow. This test FAILS (temp == A's cell, A no longer resident)
    // without the `borrowed` skip in `eviction_order`.
    #[test]
    fn borrowed_resident_is_protected_from_eviction() {
        // budget=2: A and B both Base-resident, A cheap-miss (natural victim).
        let mut st = ResidencyState::new(&refs_a_b_tie_next_use(), &info_a_cheap_b_expensive(), 2);
        let a_cell = match st.admit(value_a(), 0).unwrap() {
            Loc::Smem(c) => c,
            other => panic!("expected Smem, got {other:?}"),
        };
        let _b = st.admit(value_b(), 1).unwrap();

        // Borrow A — it is now pinned even though it is the cheapest-miss victim.
        let borrowed = st.borrow_resident(value_a()).expect("A is resident");
        assert_eq!(borrowed, a_cell, "borrow returns A's resident cell");

        // A transient alloc forces eviction. The lease must protect A → B is evicted.
        let temp = st
            .alloc_temp(OperandField::Base, 2)
            .expect("alloc_temp evicts unborrowed B");
        assert_ne!(temp, a_cell, "temp must NOT reuse the borrowed resident's cell");
        assert_eq!(
            st.location(value_a(), 2),
            Loc::Smem(a_cell),
            "borrowed A must stay resident in its cell"
        );
        assert_eq!(
            st.location(value_b(), 2),
            Loc::SourceDram,
            "unborrowed B was the eviction victim"
        );

        st.free_temp(temp);
        st.release_borrow(value_a());
        // After release, A is an eviction candidate again.
        assert!(
            !st.is_borrowed(value_a()),
            "release_borrow clears the lease"
        );
    }

    // alloc_temp evicts a backed resident on demand and the temp reuses the freed
    // cell; the evicted value re-resolves to its DRAM backing.
    #[test]
    fn alloc_temp_evicts_backed_resident_on_demand() {
        let mut st = ResidencyState::new(&refs_two_residents(), &info_two_base(), 1);
        let a_cell = match st.admit(value_a(), 0).unwrap() {
            Loc::Smem(c) => c,
            other => panic!("expected Smem, got {other:?}"),
        };
        // budget=1, A occupies the only cell. A temp must evict A (unborrowed, backed).
        let temp = st.alloc_temp(OperandField::Base, 1).expect("evicts A");
        assert_eq!(temp, a_cell, "temp reuses the freed cell");
        assert_eq!(
            st.location(value_a(), 1),
            Loc::SourceDram,
            "evicted backed resident re-reads DRAM"
        );
        st.free_temp(temp);
    }

    // With the only resident borrowed and the budget exhausted, alloc_temp cannot
    // steal the borrowed cell → BudgetBelowFloor (NOT a silent borrow corruption).
    #[test]
    fn alloc_temp_below_floor_when_only_resident_is_borrowed() {
        let mut st = ResidencyState::new(&refs_two_residents(), &info_two_base(), 1);
        let _a = st.admit(value_a(), 0).unwrap();
        let _ = st.borrow_resident(value_a()).expect("A resident");
        match st.alloc_temp(OperandField::Base, 1) {
            Err(CompileError::BudgetBelowFloor { .. }) => {}
            other => panic!("expected BudgetBelowFloor (borrowed cell unstealable), got {other:?}"),
        }
        st.release_borrow(value_a());
    }

    // max_live_cells reflects the shared allocator's true high-water of residents +
    // transient temps held SIMULTANEOUSLY (not a stale per-reservation counter).
    #[test]
    fn max_live_tracks_residents_plus_live_temps() {
        // budget=6, 2 Base residents (cells 0,1).
        let mut st = ResidencyState::new(&refs_two_residents(), &info_two_base(), 6);
        let _ = st.admit(value_a(), 0);
        let _ = st.admit(value_b(), 1);
        assert_eq!(st.max_live_cells(), 2, "two residents = 2 live cells");

        // Hold 3 transient temps at once → peak 5.
        let t0 = st.alloc_temp(OperandField::Base, 2).unwrap();
        let t1 = st.alloc_temp(OperandField::Base, 2).unwrap();
        let t2 = st.alloc_temp(OperandField::Base, 2).unwrap();
        assert_eq!(st.max_live_cells(), 5, "2 residents + 3 live temps = peak 5");

        // Freeing temps does not lower the high-water (it is a peak, not a gauge).
        st.free_temp(t0);
        st.free_temp(t1);
        st.free_temp(t2);
        assert_eq!(st.max_live_cells(), 5, "high-water is monotone");

        // A second wave of 3 temps reuses freed cells → peak stays 5 (no drift).
        let u0 = st.alloc_temp(OperandField::Base, 2).unwrap();
        let u1 = st.alloc_temp(OperandField::Base, 2).unwrap();
        let u2 = st.alloc_temp(OperandField::Base, 2).unwrap();
        assert_eq!(st.max_live_cells(), 5, "reused cells must not inflate the peak");
        st.free_temp(u0);
        st.free_temp(u1);
        st.free_temp(u2);
    }
}
