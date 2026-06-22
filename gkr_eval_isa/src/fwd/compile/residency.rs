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

// ── Temp reservation ─────────────────────────────────────────────────────────

/// Scoped temp reservation returned by `ensure_temp_capacity`.
///
/// Holds cells that were freed for a single expression's lowering and returns
/// them to the planner on `release`. `free_cells` is how many aligned cells the
/// emitter may use without further eviction.
pub struct TempReservation {
    /// How many aligned cells are free for the lowering.
    pub free_cells: usize,
    /// Internal: cells that were evicted to satisfy the request (to be restored
    /// when `release` is called — or in practice, the emitter re-admits them).
    evicted: Vec<ValueId>,
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
    /// Per-value facts (field, miss penalty, has_backing).
    info: HashMap<ValueId, ValueInfo>,
    /// Precomputed: for each (ValueId, point), the index of the next `Use` event
    /// at or after `point`. Stored as a sorted list of use-event indices per
    /// value; binary search gives the next use.
    next_uses: HashMap<ValueId, Vec<usize>>,
    /// Number of temp cells currently held by active `TempReservation`s.
    temp_cells_held: usize,
    /// High-water mark: residents + temp cells held.
    max_live: usize,
    /// Total budget (used for max_live_cells reporting).
    budget: usize,
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
            info: info.clone(),
            next_uses,
            temp_cells_held: 0,
            max_live: 0,
            budget,
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
                self.update_max_live();
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
                    self.update_max_live();
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

    /// Evict enough residents to free at least `min_working_set` cells, then
    /// return a `TempReservation` that holds those cells until `release`.
    ///
    /// The emitter uses this before lowering a subexpression that needs scratch
    /// cells. After lowering, call `release` to return the temp cells.
    ///
    /// Returns `Err(BudgetBelowFloor)` if even evicting all residents cannot
    /// satisfy `min_working_set`.
    pub fn ensure_temp_capacity(
        &mut self,
        min_working_set: usize,
        point: usize,
    ) -> Result<TempReservation, CompileError> {
        // Count currently-free cells (budget minus occupied cells tracked by the
        // alloc's live count). We do not have a direct "free cells" method, so we
        // probe: attempt Base allocs until we have `min_working_set` free, tracking
        // how many we could grab.
        //
        // Simpler approach: compute free_cells = budget - live_from_alloc.
        // CellAllocator tracks `live` internally but doesn't expose it directly.
        // We can measure free capacity by counting how many cells we can alloc
        // then freeing them. But that would perturb state.
        //
        // Instead we track free capacity ourselves: free_cells = budget - sum of
        // widths of all resident values.
        let currently_resident_cells: usize = self.resident.keys().map(|v| {
            self.info.get(v).map(|i| i.width as usize).unwrap_or(1)
        }).sum();
        let currently_free = self.budget.saturating_sub(currently_resident_cells);

        if currently_free >= min_working_set {
            let reservation = TempReservation {
                free_cells: min_working_set,
                evicted: vec![],
            };
            self.temp_cells_held += min_working_set;
            self.update_max_live();
            return Ok(reservation);
        }

        // Need to evict.
        let mut evicted_values: Vec<ValueId> = Vec::new();
        let mut freed_cells = currently_free;
        let eviction_order = self.eviction_order(point);

        for victim_id in eviction_order {
            if freed_cells >= min_working_set {
                break;
            }
            let victim_cell = match self.resident.get(&victim_id) {
                Some(&c) => c,
                None => continue,
            };
            let width = self.info.get(&victim_id).map(|i| i.width as usize).unwrap_or(1);
            self.resident.remove(&victim_id);
            self.cell_to_value.remove(&victim_cell);
            self.alloc.free(victim_cell);
            freed_cells += width;
            evicted_values.push(victim_id);
        }

        if freed_cells < min_working_set {
            // Even evicting everything wasn't enough (budget < min_working_set).
            return Err(CompileError::BudgetBelowFloor {
                floor: min_working_set,
                budget: self.budget,
            });
        }

        self.temp_cells_held += min_working_set;
        self.update_max_live();
        Ok(TempReservation {
            free_cells: min_working_set,
            evicted: evicted_values,
        })
    }

    /// Return the temp cells reserved by `r` back to the planner.
    ///
    /// The evicted values tracked in the reservation are NOT automatically
    /// re-admitted — the emitter must re-admit them via `admit` if needed.
    pub fn release(&mut self, r: TempReservation) {
        self.temp_cells_held = self.temp_cells_held.saturating_sub(r.free_cells);
        // evicted values in `r` are not re-placed — the emitter decides.
        drop(r);
    }

    /// High-water mark of live smem cells over this planner's life.
    ///
    /// Counts both resident cells AND temp cells held by `ensure_temp_capacity`.
    pub fn max_live_cells(&self) -> usize {
        self.max_live
    }

    // ── Internal helpers ──────────────────────────────────────────────────────

    /// Update the high-water mark.
    fn update_max_live(&mut self) {
        let resident_cells: usize = self.resident.keys().map(|v| {
            self.info.get(v).map(|i| i.width as usize).unwrap_or(1)
        }).sum();
        let live = resident_cells + self.temp_cells_held;
        if live > self.max_live {
            self.max_live = live;
        }
    }

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

    // ── Test 5: temp reservation accounting is symmetric ─────────────────────
    //
    // Budget = 6, 2 Base residents (cells 0,1), leaving 4 free cells.
    // Reserve N=3: free_cells must equal N (not 4), temp_cells_held += 3.
    // max_live = 2 residents + 3 reserved = 5.
    // Release: temp_cells_held returns to 0 (symmetric subtract).
    // Reserve N=3 again: max_live must still be 5, not 8 (no leak).
    // Reserve N=5 (> budget - residents = 4): must fail with BudgetBelowFloor.
    //
    // RefString: just the two Produce events; no further uses so eviction is free.

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

    #[test]
    fn temp_reservation_accounting_is_symmetric() {
        // budget=6, 2 Base residents (2 cells used), 4 cells genuinely free.
        let mut st = ResidencyState::new(&refs_two_residents(), &info_two_base(), 6);
        let _ = st.admit(value_a(), 0);
        let _ = st.admit(value_b(), 1);

        // Baseline: residents contribute 2 cells to max_live, no temps yet.
        let baseline_max = st.max_live_cells();
        assert_eq!(baseline_max, 2, "baseline max_live should equal 2 residents");

        // ── First reservation ──────────────────────────────────────────────
        let n: usize = 3;
        let r1 = st.ensure_temp_capacity(n, 2)
            .expect("3 cells should be reservable with 4 free");

        // free_cells must equal exactly the reserved amount, not the total free.
        assert_eq!(r1.free_cells, n,
            "free_cells must equal min_working_set, not total free");

        // max_live must now be residents(2) + reserved(3) = 5.
        assert_eq!(st.max_live_cells(), 2 + n,
            "max_live must be residents + reserved");

        // ── Release ───────────────────────────────────────────────────────
        st.release(r1);

        // ── Second reservation (same N) ────────────────────────────────────
        let r2 = st.ensure_temp_capacity(n, 2)
            .expect("second identical reservation must succeed");

        assert_eq!(r2.free_cells, n,
            "second reservation free_cells must equal min_working_set");

        // max_live must NOT drift upward: still 2 + 3 = 5.
        assert_eq!(st.max_live_cells(), 2 + n,
            "max_live must not drift after release+re-reserve (no leak)");

        st.release(r2);

        // ── Budget-floor guard: N > total budget ──────────────────────────
        // budget=6; even evicting all residents (2 cells) yields at most 6
        // free cells. Asking for 7 exceeds what the budget can ever provide.
        let too_big = 7;
        let result = st.ensure_temp_capacity(too_big, 2);
        assert!(
            matches!(result, Err(CompileError::BudgetBelowFloor { floor, budget })
                if floor == too_big && budget == 6),
            "must return BudgetBelowFloor{{floor={too_big}, budget=6}}"
        );
    }
}
