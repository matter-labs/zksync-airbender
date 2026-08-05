//! Smem cell allocator + long-reduction splitter (spec §4, §11, §12).
//!
//! The forward VM keeps a tiny BF-cell-indexed smem slot file. This module owns
//! two scheduling primitives consumed by `arith.rs`:
//!
//! - [`CellAllocator`] — hands out smem cell indices honoring the §4 layout rules:
//!   an Ext value occupies **4 consecutive, 4-cell-aligned** cells (`cell % 4 == 0`)
//!   for vectorized `.v4` LDS/STS, a Base value occupies **1** cell, and a Base
//!   range is **never packed inside an Ext allocation's 4-cell span**. Allocation
//!   beyond `budget` is `CompileError::BudgetBelowFloor` (§11/§12: below the
//!   irreducible floor the budget is an unsupported config, not a circuit
//!   infeasibility).
//!
//! - [`split_reduction`] — splits an over-long additive/multiplicative reduction
//!   into chunks each `<= MAX_ARITY` (the 7-bit arity cap the encoder enforces),
//!   bounded by the budget, summing exactly to `arity` (§11 "split long reductions
//!   into multiple instructions with eviction/caching between").

use super::super::error::CompileError;
use super::super::isa::{MAX_ARITY, OperandField};

/// A first-fit smem cell allocator over a fixed `budget` of BF cells (spec §4).
///
/// Cells are the unit of allocation (distinct from a backing **slot**). An Ext
/// allocation reserves a 4-cell-aligned block of 4 cells; a Base allocation
/// reserves a single cell. A Base allocation never lands inside an Ext block's
/// 4-cell span: a freed Ext block is reused only as a whole Ext block, so its
/// interior cells stay reserved-as-a-unit until the whole block frees.
#[derive(Clone, Debug)]
pub struct CellAllocator {
    budget: usize,
    /// Per-cell occupancy. `true` = the cell is part of a live allocation.
    occupied: Vec<bool>,
    /// Cells that are the *interior* of a live Ext block (not its base cell).
    /// A Base allocation must never reuse these even if `occupied[c]` flips —
    /// they belong to the Ext block as an indivisible 4-cell unit.
    ext_interior: Vec<bool>,
    /// High-water mark: the most cells live at once over this allocator's life.
    max_live: usize,
    /// Currently live cell count (sum of widths of outstanding allocations).
    live: usize,
}

impl CellAllocator {
    /// A fresh allocator over `budget` BF cells.
    pub fn new(budget: usize) -> Self {
        CellAllocator {
            budget,
            occupied: vec![false; budget],
            ext_interior: vec![false; budget],
            max_live: 0,
            live: 0,
        }
    }

    /// Allocate a cell for a value of `field`, returning its base cell index.
    ///
    /// Base → 1 cell (first free cell that is not Ext interior). Ext → a 4-cell,
    /// 4-cell-aligned block (4 contiguous free cells starting at `cell % 4 == 0`).
    /// No room within `budget` → `Err(BudgetBelowFloor)`.
    pub fn alloc(&mut self, field: OperandField) -> Result<u16, CompileError> {
        match field {
            OperandField::Base => self.alloc_base(),
            OperandField::Ext => self.alloc_ext(),
        }
    }

    fn alloc_base(&mut self) -> Result<u16, CompileError> {
        // First-fit: the lowest free cell that is not the interior of an Ext block.
        for c in 0..self.budget {
            if !self.occupied[c] && !self.ext_interior[c] {
                self.occupied[c] = true;
                self.bump_live(1);
                return Ok(c as u16);
            }
        }
        Err(self.below_floor(1))
    }

    fn alloc_ext(&mut self) -> Result<u16, CompileError> {
        // First-fit over 4-cell-aligned blocks fully inside the budget and free.
        let mut base = 0usize;
        while base + 4 <= self.budget {
            let free = (base..base + 4).all(|c| !self.occupied[c]);
            if free {
                for c in base..base + 4 {
                    self.occupied[c] = true;
                    // Interior cells (base+1..base+4) are reserved as part of the
                    // Ext unit so a later Base alloc never packs into the span.
                    self.ext_interior[c] = c != base;
                }
                self.bump_live(4);
                return Ok(base as u16);
            }
            base += 4;
        }
        Err(self.below_floor(4))
    }

    /// Free a previously allocated cell by its base index. A Base cell frees 1
    /// cell; an Ext block frees its whole 4-cell span (recognized by interior
    /// markers on the following cells).
    pub fn free(&mut self, cell: u16) {
        let base = cell as usize;
        if base >= self.budget || !self.occupied[base] {
            return;
        }
        // An Ext block: base cell occupied + the next cell flagged interior.
        let is_ext = base + 1 < self.budget && self.ext_interior[base + 1];
        let width = if is_ext { 4 } else { 1 };
        for c in base..(base + width).min(self.budget) {
            self.occupied[c] = false;
            self.ext_interior[c] = false;
        }
        self.live = self.live.saturating_sub(width);
    }

    /// The high-water mark of live cells over this allocator's life (§11
    /// "max live cells" instrumentation; tracked into `trace.max_live_cells`).
    pub fn max_live(&self) -> usize {
        self.max_live
    }

    fn bump_live(&mut self, width: usize) {
        self.live += width;
        if self.live > self.max_live {
            self.max_live = self.live;
        }
    }

    /// The budget is below the irreducible floor for the requested live set:
    /// floor is at least the currently-live cells plus the width that did not fit.
    fn below_floor(&self, want: usize) -> CompileError {
        CompileError::BudgetBelowFloor {
            floor: self.live + want,
            budget: self.budget,
        }
    }
}

/// Split a reduction of `arity` terms into chunk sizes, each `<= MAX_ARITY`,
/// summing **exactly** to `arity` (spec §11).
///
/// `arity <= MAX_ARITY` returns `vec![arity]` (no split). For larger arity the
/// terms are sliced into chunks of at most `MAX_ARITY`; each emitted chunk is a
/// single ADD/MUL instruction over the accumulator with the running partial held
/// in an evict cell between chunks (§11 eviction). This enforces ONLY the encoder
/// arity cap. The smem working-set bound is a separate concern, handled by the
/// schedule-driven lowerer (`lower.rs`): each split partial is evicted to a fresh
/// internal value and re-folded, with cell placement bounded by `plan_placement`
/// rather than a static pre-split.
pub fn split_reduction(arity: usize) -> Vec<usize> {
    if arity == 0 {
        return vec![];
    }
    if arity <= MAX_ARITY {
        return vec![arity];
    }
    let chunk_cap = MAX_ARITY;

    let mut chunks = Vec::new();
    let mut remaining = arity;
    while remaining > 0 {
        let take = remaining.min(chunk_cap);
        chunks.push(take);
        remaining -= take;
    }
    chunks
}
