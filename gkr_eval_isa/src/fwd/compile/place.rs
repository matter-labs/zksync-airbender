//! Lifetime-overlap cell allocator for the Stage-3 forward-program generator (spec
//! OP-2, OP-4, OP-5-packing).
//!
//! Pure over synthetic inputs — no `arith.rs`/`compile_layer` dependency. Consumes a
//! flat, already-scheduled instruction stream (`VirtualInstr`) plus the per-step
//! `resident_before`/`resident_after` membership ([`ResidencyStep`], a local,
//! schedule-schema-agnostic type — post-schema-v2 (Task 4) the caller always hands
//! this module residency-FREE steps; see `mod.rs::compile_layer_with_policy`'s
//! `free_steps`) and produces a concrete cell assignment (`Placement`).
//!
//! `CellAllocator` (`schedule.rs`) is strictly first-fit and hands back whatever cell
//! it picks — it cannot place a value at a *chosen* cell. Two things this module needs
//! chosen-cell placement for:
//!   - lifetime-aware Base placement must land a Base in a *specific* quad (one no
//!     overlapping-lifetime Ext will need), not just the lowest free cell;
//!   - compaction (`clear_quad_for_ext`) needs a *specific* free target per relocated
//!     Base, then the incoming Ext placed at the quad it just cleared.
//! So this module owns its own cell-occupancy model (`CellOccupancy`) rather than
//! driving a `CellAllocator`. `schedule.rs` is untouched.
//!
//! Cell widths: Base = 1 cell; Ext = 4 cells, 4-aligned. Compaction only ever relocates
//! 1-cell Base values to currently-FREE 1-cells outside the quad being cleared — an Ext
//! is never moved and a relocation target is always free, so there are no
//! occupied-target cycles, no scratch cell, and no accumulator.

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::ExprId;

use crate::fwd::compile::CompileError;
use crate::fwd::isa::{LdcSub, OperandField, Sign};

/// Per-step resident-set membership this allocator's lifetime analysis reads
/// (`resident_before`/`resident_after`). Local to this module — NOT the persisted
/// schedule schema (`cs::dag_ir::LayerSchedule`, schema v2, has no per-step residency
/// anymore; see module doc). `mod.rs::compile_layer_with_policy` always passes
/// residency-free steps (both sets empty) since the emitter now realizes residency
/// lazily rather than from a persisted plan.
#[derive(Clone, Debug, Default)]
pub struct ResidencyStep {
    pub resident_before: Vec<ExprId>,
    pub resident_after: Vec<ExprId>,
}

pub type ValueId = ExprId;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VInstrKind {
    Mov,
    Add,
    Mul,
    Fma,
}

/// A single Base relocation performed by compaction (`clear_quad_for_ext`). `to` is
/// always a cell that is free at the moment the step is applied — see the module doc.
#[derive(Clone, Copy, Debug)]
pub struct RelocStep {
    pub value: ValueId,
    pub from: u16,
    pub to: u16,
}

#[derive(Clone, Debug)]
pub enum VirtualOp {
    Value(ValueId),
    Global { slot: u8, col: u16 },
    Ldc { sub: LdcSub, idx: u16 },
    Special { desc: u16 },
    Acc,
}

#[derive(Clone, Debug)]
pub struct VirtualInstr {
    pub op: VInstrKind,
    pub field: OperandField,
    pub defines: Option<ValueId>,
    pub reads: Vec<VirtualOp>,
    pub sign: Sign,
    pub is_dram_read: bool,
}

pub struct PlacementInput<'a> {
    pub instrs: &'a [VirtualInstr],
    pub steps: &'a [ResidencyStep],
    pub step_of_instr: &'a [usize],
    pub widths: &'a HashMap<ValueId, OperandField>,
    pub budget: usize,
}

pub struct Placement {
    pub cell_of: HashMap<(usize, ValueId), u16>,
    pub moves: Vec<(usize, RelocStep)>,
    pub max_live_cells: usize,
}

// ─────────────────────────────────────────────────────────────────────────────────
// Cell occupancy (this module's private replacement for `CellAllocator` — see the
// module doc for why the strictly-first-fit allocator is insufficient here).
// ─────────────────────────────────────────────────────────────────────────────────

/// Direct per-cell occupancy: `owner[c] == Some(v)` iff cell `c` currently belongs to
/// live value `v`. An Ext value owns all 4 cells of its quad; a Base owns exactly 1.
/// Because an Ext always claims its whole quad atomically (never partially), a quad
/// with ANY free cell can only be a Base-hosting quad or a fully clean one — there is
/// no such thing as a "partially free Ext quad" to special-case.
struct CellOccupancy {
    budget: usize,
    owner: Vec<Option<ValueId>>,
    live: usize,
    max_live: usize,
}

impl CellOccupancy {
    fn new(budget: usize) -> Self {
        CellOccupancy { budget, owner: vec![None; budget], live: 0, max_live: 0 }
    }

    fn is_free(&self, cell: usize) -> bool {
        self.owner[cell].is_none()
    }

    fn occupy(&mut self, start: usize, width: usize, value: ValueId) {
        for c in start..start + width {
            self.owner[c] = Some(value);
        }
        self.live += width;
        self.max_live = self.max_live.max(self.live);
    }

    fn vacate(&mut self, start: usize, width: usize) {
        for c in start..start + width {
            self.owner[c] = None;
        }
        self.live -= width;
    }

    /// The lowest 4-aligned, fully-free quad start, if any.
    fn free_quad(&self) -> Option<usize> {
        let mut q = 0;
        while q + 4 <= self.budget {
            if (q..q + 4).all(|c| self.is_free(c)) {
                return Some(q);
            }
            q += 4;
        }
        None
    }
}

/// Lifetime-aware Base placement (spec Step 3 item 2, the primary lever): prefer a
/// free cell whose quad already has an occupant over opening a fresh clean quad. A
/// quad's only possible occupant kinds are (a) Bases packed 1-per-cell, or (b) a
/// single live Ext reserving the whole 4-cell span — case (b) leaves ZERO free cells
/// in that quad, so any free cell found in an "already occupied" quad is necessarily
/// in a Base-hosting quad. Preferring those keeps clean quads available for Exts
/// whose lifetime overlaps this Base's, deferring/avoiding the compaction fallback.
fn place_base(occ: &CellOccupancy) -> u16 {
    let quad_has_occupant = |cell: usize| -> bool {
        let start = (cell / 4) * 4;
        let end = (start + 4).min(occ.budget);
        (start..end).any(|c| !occ.is_free(c))
    };
    (0..occ.budget)
        .find(|&c| occ.is_free(c) && quad_has_occupant(c))
        .or_else(|| (0..occ.budget).find(|&c| occ.is_free(c)))
        .expect("caller guarantees a free cell exists for a Base placement") as u16
}

/// Ext placement: a clean 4-aligned quad, or `None` if none is free — fragmented
/// (caller falls back to `clear_quad_for_ext`) or genuinely oversized.
fn place_ext(occ: &CellOccupancy) -> Option<usize> {
    occ.free_quad()
}

// ─────────────────────────────────────────────────────────────────────────────────
// Live ranges.
// ─────────────────────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug)]
struct LiveRange {
    def: usize,
    last_use: usize,
}

/// Build the per-value `[def, last_use]` live range over the flat `instrs` index
/// space (Step 3 item 1). See the module doc / task brief for the rules; briefly:
///
/// - `def` = the first instr with `defines == Some(v)`, OR — only for a value with NO
///   defining instr that enters via `steps[0].resident_before` (a cross-step resident
///   carried in from outside this instr slice) — the first instr whose `reads`
///   mentions `Value(v)`.
/// - `last_use` = max of (a) the last instr reading `Value(v)`, and (b) the last instr
///   of the last step `s` with `v ∈ resident_after[s]`, clamped so that an implicit
///   cone-fit drop (`v` in `resident_after[p-1]`, absent from `resident_before[p]`)
///   caps component (b) at the end of step `p-1` — later `resident_after` entries (an
///   inconsistent-data possibility, never true in a sound schedule) must not resurrect
///   a value past the boundary where it was actually dropped.
/// - L6 edge case: a value never read as `Value(v)` and never present in any
///   `resident_after` (e.g. a materialized-then-immediately-consumed internal temp)
///   lives only at its own defining instr: `last_use = def`.
fn compute_live_ranges(input: &PlacementInput) -> HashMap<ValueId, LiveRange> {
    // Every value referenced anywhere: defined, read as a Value operand, or named in
    // any step's resident_before/resident_after.
    let mut ids: std::collections::HashSet<ValueId> = std::collections::HashSet::new();
    for instr in input.instrs {
        if let Some(v) = instr.defines {
            ids.insert(v);
        }
        for r in &instr.reads {
            if let VirtualOp::Value(v) = r {
                ids.insert(*v);
            }
        }
    }
    for step in input.steps {
        ids.extend(step.resident_before.iter().copied());
        ids.extend(step.resident_after.iter().copied());
    }

    // def: first defining instr, else (only for a steps[0].resident_before entrant
    // with no defining instr) the first instr reading it as a Value.
    let mut def: HashMap<ValueId, usize> = HashMap::new();
    for (i, instr) in input.instrs.iter().enumerate() {
        if let Some(v) = instr.defines {
            def.entry(v).or_insert(i);
        }
    }
    if let Some(first_step) = input.steps.first() {
        for &v in &first_step.resident_before {
            if !def.contains_key(&v) {
                if let Some(i) = input.instrs.iter().position(|instr| {
                    instr.reads.iter().any(|r| matches!(r, VirtualOp::Value(x) if *x == v))
                }) {
                    def.insert(v, i);
                }
            }
        }
    }
    // Defensive fallback: a value with no evidence of a def at all (not exercised by
    // the Task-1 corpus). Rather than panic on an unanticipated input shape, treat it
    // as resident from the very start of this instr slice.
    for &v in &ids {
        def.entry(v).or_insert(0);
    }

    // The last instr belonging to each step.
    let mut last_instr_of_step: Vec<usize> = vec![0; input.steps.len()];
    for (i, &s) in input.step_of_instr.iter().enumerate() {
        if s < last_instr_of_step.len() {
            last_instr_of_step[s] = last_instr_of_step[s].max(i);
        }
    }

    let mut ranges: HashMap<ValueId, LiveRange> = HashMap::new();
    for &v in &ids {
        let d = def[&v];

        // (a) the last instr reading `v` as a Value operand.
        let a = input
            .instrs
            .iter()
            .enumerate()
            .filter(|(_, instr)| instr.reads.iter().any(|r| matches!(r, VirtualOp::Value(x) if *x == v)))
            .map(|(i, _)| i)
            .max();

        // (b) cross-step residency, clamped at the first implicit cone-fit drop.
        let drop_boundary = (1..input.steps.len()).find(|&p| {
            input.steps[p - 1].resident_after.contains(&v) && !input.steps[p].resident_before.contains(&v)
        });
        let b = if let Some(p) = drop_boundary {
            Some(last_instr_of_step[p - 1])
        } else {
            (0..input.steps.len())
                .filter(|&s| input.steps[s].resident_after.contains(&v))
                .map(|s| last_instr_of_step[s])
                .max()
        };

        // L6: never read as a Value and never resident_after anywhere.
        let last_use = match (a, b) {
            (Some(x), Some(y)) => x.max(y),
            (Some(x), None) => x,
            (None, Some(y)) => y,
            (None, None) => d,
        };
        assert!(last_use >= d, "last_use ({last_use}) < def ({d}) for value {v:?}");
        ranges.insert(v, LiveRange { def: d, last_use });
    }
    ranges
}

fn width_of(widths: &HashMap<ValueId, OperandField>, v: ValueId) -> usize {
    match widths.get(&v) {
        Some(OperandField::Ext) => 4,
        Some(OperandField::Base) => 1,
        None => panic!("no width recorded for value {v:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────────
// Base-relocation compaction (Step 3 item 4, spec OP-4).
// ─────────────────────────────────────────────────────────────────────────────────

/// Open ONE clean 4-aligned quad for an incoming Ext by relocating the fewest-Base
/// quad's Bases to free 1-cells outside it. Returns `(cleared_quad_start, base moves)`.
///
/// Picks the quad with the fewest live Base occupants (`k`, `0 < k <= 3`; a quad
/// hosting a live Ext is not a candidate — see `CellOccupancy`'s doc for why such a
/// quad has zero free cells and thus can never be the *target*, and is skipped here
/// as a *source* too since it holds no movable Bases). Each relocated Base prefers a
/// free cell in a quad that already hosts a Base (packing — doesn't fragment a clean
/// quad); falls back to any other free cell outside the cleared quad.
///
/// Only Bases move, and every target is a cell that is free at the moment it is
/// chosen — no cycles, no scratch cell, no accumulator. `None` only if no quad has an
/// all-Base (movable), non-empty occupancy, which cannot happen when the caller has
/// already checked `current_live_width + 4 <= budget` (see `plan_placement`): with no
/// clean quad free (a precondition for calling this at all) and >= 4 free cells
/// overall, some quad must hold 1..=3 Bases (an Ext quad always contributes 0 free
/// cells, and 4 free cells can't all come from quads with 0 free cells each).
pub(crate) fn clear_quad_for_ext(
    live: &[(ValueId, u16, OperandField)],
    widths: &HashMap<ValueId, OperandField>,
    budget: usize,
) -> Option<(u16, Vec<RelocStep>)> {
    let n_quads = budget / 4;
    if n_quads == 0 {
        return None;
    }

    let mut free = vec![true; budget];
    let mut quad_base_count = vec![0usize; n_quads];
    let mut quad_has_ext = vec![false; n_quads];
    for &(value, cell, field) in live {
        debug_assert_eq!(
            widths.get(&value),
            Some(&field),
            "live entry's field must match `widths` for {value:?}"
        );
        let width = if field == OperandField::Ext { 4 } else { 1 };
        for c in cell as usize..(cell as usize + width).min(budget) {
            free[c] = false;
        }
        let q = cell as usize / 4;
        if q < n_quads {
            if field == OperandField::Ext {
                quad_has_ext[q] = true;
            } else {
                quad_base_count[q] += 1;
            }
        }
    }

    // The fewest-Base, no-Ext, non-empty quad (0 < k <= 3); lowest address on ties.
    let target = (0..n_quads)
        .filter(|&q| !quad_has_ext[q] && quad_base_count[q] > 0 && quad_base_count[q] <= 3)
        .min_by_key(|&q| quad_base_count[q])?;
    let quad_start = target * 4;

    // Sort movers by their `from` cell so the emitted `moves` sequence — and thus the
    // target assignment below (targets are scanned free-cell-ascending) — is a pure
    // function of the occupancy, NOT of the caller's `live`-slice order. The caller
    // (`plan_placement`) builds `live` from a `HashMap`, whose iteration order is
    // nondeterministic; without this sort the from→to pairing would vary run-to-run and
    // break byte-exact program parity once Task 3 consumes `moves`.
    let mut movers: Vec<(ValueId, u16)> = live
        .iter()
        .filter(|&&(_, cell, field)| field == OperandField::Base && (cell as usize) / 4 == target)
        .map(|&(value, cell, _)| (value, cell))
        .collect();
    movers.sort_by_key(|&(_, cell)| cell);

    let mut relocs = Vec::with_capacity(movers.len());
    for (value, from) in movers {
        free[from as usize] = true; // vacate first: never its own cell as a target
        quad_base_count[target] -= 1;

        // Prefer a free cell in a quad that already hosts a Base; else any free cell
        // outside the cleared quad (necessarily a clean quad by this point).
        let to = (0..n_quads)
            .filter(|&q| q != target && !quad_has_ext[q] && quad_base_count[q] > 0)
            .find_map(|q| (q * 4..(q * 4 + 4).min(budget)).find(|&c| free[c]))
            .or_else(|| (0..budget).filter(|&c| c / 4 != target).find(|&c| free[c]))
            .expect(
                "a free cell must exist outside the cleared quad: caller guarantees \
                 current_live_width + 4 <= budget",
            ) as u16;

        free[to as usize] = false;
        quad_base_count[to as usize / 4] += 1;
        relocs.push(RelocStep { value, from, to });
    }

    Some((quad_start as u16, relocs))
}

// ─────────────────────────────────────────────────────────────────────────────────
// Placement scan (Step 3 items 2-3).
// ─────────────────────────────────────────────────────────────────────────────────

pub fn plan_placement(input: &PlacementInput) -> Result<Placement, CompileError> {
    let n = input.instrs.len();
    let ranges = compute_live_ranges(input);

    // Group values by their def-instr so the scan looks up "what becomes live here" in
    // O(1) per instr rather than re-scanning the whole range map every time.
    let mut live_at_def: Vec<Vec<ValueId>> = vec![Vec::new(); n];
    for (&v, r) in &ranges {
        if r.def < n {
            live_at_def[r.def].push(v);
        }
    }
    for bucket in &mut live_at_def {
        bucket.sort_by_key(|v| v.0); // deterministic placement order
    }

    let mut occ = CellOccupancy::new(input.budget);
    let mut cell_of_value: HashMap<ValueId, u16> = HashMap::new();
    let mut cell_of: HashMap<(usize, ValueId), u16> = HashMap::new();
    let mut moves: Vec<(usize, RelocStep)> = Vec::new();

    for i in 0..n {
        // 1. Free the cells of values whose last use was strictly before this instr.
        let dead: Vec<ValueId> =
            cell_of_value.keys().copied().filter(|v| ranges[v].last_use < i).collect();
        for v in dead {
            let cell = cell_of_value.remove(&v).expect("dead value must be currently placed");
            occ.vacate(cell as usize, width_of(input.widths, v));
        }

        // 2. Place values that become live at this instr.
        for &v in &live_at_def[i] {
            let field = *input.widths.get(&v).expect("every placed value needs a recorded width");
            match field {
                OperandField::Base => {
                    let cell = place_base(&occ);
                    occ.occupy(cell as usize, 1, v);
                    cell_of_value.insert(v, cell);
                }
                OperandField::Ext => {
                    let quad = match place_ext(&occ) {
                        Some(q) => q,
                        None => {
                            // No clean quad free. Genuinely oversized, or just fragmented?
                            let current_live_width = occ.live;
                            if current_live_width + 4 > input.budget {
                                return Err(CompileError::BudgetBelowFloor {
                                    floor: current_live_width + 4,
                                    budget: input.budget,
                                });
                            }
                            // `cell_of_value` is a HashMap: sort the snapshot by cell so
                            // `clear_quad_for_ext` receives stable input regardless of
                            // iteration order (belt-and-suspenders — the helper also sorts
                            // its movers, but a stable input keeps the whole path
                            // order-independent end to end).
                            let mut live: Vec<(ValueId, u16, OperandField)> = cell_of_value
                                .iter()
                                .map(|(&val, &cell)| (val, cell, input.widths[&val]))
                                .collect();
                            live.sort_by_key(|&(_, cell, _)| cell);
                            let (cleared_quad, relocs) =
                                clear_quad_for_ext(&live, input.widths, input.budget).expect(
                                    "clear_quad_for_ext must succeed: current_live_width + 4 <= budget",
                                );
                            for r in relocs {
                                occ.vacate(r.from as usize, 1);
                                occ.occupy(r.to as usize, 1, r.value);
                                cell_of_value.insert(r.value, r.to);
                                moves.push((i, r));
                            }
                            cleared_quad as usize
                        }
                    };
                    occ.occupy(quad, 4, v);
                    cell_of_value.insert(v, quad as u16);
                }
            }
        }

        // 3. Record every currently-live value's cell at this instr, post any
        // compaction that happened above.
        for (&v, &c) in &cell_of_value {
            cell_of.insert((i, v), c);
        }
    }

    Ok(Placement { cell_of, moves, max_live_cells: occ.max_live })
}

#[cfg(test)]
mod tests {
    use super::*; // brings VInstrKind, VirtualOp, VirtualInstr, RelocStep, PlacementInput, plan_placement, clear_quad_for_ext
    use crate::fwd::isa::{OperandField as F, Sign};
    use cs::gkr_compiler::dag_ir::ExprId;
    use std::collections::HashMap;

    fn v(n: u32) -> ExprId {
        ExprId(n)
    }

    // Helper: one step whose resident sets are the given ExprId lists.
    fn step(before: &[u32], after: &[u32]) -> ResidencyStep {
        ResidencyStep {
            resident_before: before.iter().map(|&x| v(x)).collect(),
            resident_after: after.iter().map(|&x| v(x)).collect(),
        }
    }

    // A: two Ext residents that never overlap in time get non-overlapping 4-aligned cells,
    //    and total live never exceeds budget.
    #[test]
    fn ext_values_get_4_aligned_nonoverlapping_cells() {
        let widths: HashMap<ExprId, F> = [(v(1), F::Ext), (v(2), F::Ext)].into();
        let instrs = vec![
            VirtualInstr { op: VInstrKind::Mov, field: F::Ext, defines: Some(v(1)),
                reads: vec![VirtualOp::Global { slot: 0, col: 0 }], sign: Sign::Plus, is_dram_read: true },
            VirtualInstr { op: VInstrKind::Mov, field: F::Ext, defines: Some(v(2)),
                reads: vec![VirtualOp::Value(v(1))], sign: Sign::Plus, is_dram_read: false },
        ];
        let steps = vec![step(&[], &[1, 2])];
        let step_of = vec![0, 0];
        let input = PlacementInput { instrs: &instrs, steps: &steps, step_of_instr: &step_of, widths: &widths, budget: 16 };
        let p = plan_placement(&input).unwrap();
        let c1 = p.cell_of[&(1, v(1))]; // v1 live at instr 1
        let c2 = p.cell_of[&(1, v(2))]; // v2 defined at instr 1
        assert_eq!(c1 % 4, 0, "Ext must be 4-aligned");
        assert_eq!(c2 % 4, 0, "Ext must be 4-aligned");
        assert!((c1 as i32 - c2 as i32).abs() >= 4, "overlapping Ext lifetimes must not share a 4-cell span");
        assert!(p.max_live_cells <= 16);
    }

    // ── Move simulator: applies a RelocStep sequence to a cell→value occupancy map and
    //    PROVES clobber-safety — every step's target must be free (or the value's own cells)
    //    before it writes; at the end every value sits at its expected target with no overlap.
    //    A step that would overwrite a still-live value panics. This is what makes Test B/E bind.
    //    Compaction only ever moves 1-cell Bases to FREE cells (never Exts), so there are no cycles
    //    and no accumulator — a `RelocStep` is a single Base relocation whose target must be free.
    fn simulate(steps: &[RelocStep], init: &[(ExprId, u16, F)]) -> HashMap<ExprId, u16> {
        let span = |cell: u16, f: F| -> std::ops::Range<u16> { cell..cell + if f == F::Ext { 4 } else { 1 } };
        let mut occ: HashMap<u16, ExprId> = HashMap::new();       // cell -> occupying value
        let mut at: HashMap<ExprId, u16> = HashMap::new();        // value -> base cell
        let mut fld: HashMap<ExprId, F> = HashMap::new();
        for &(val, cell, f) in init { fld.insert(val, f); at.insert(val, cell); for c in span(cell, f) { assert!(occ.insert(c, val).is_none(), "init overlap @ {c}"); } }
        for s in steps {
            assert_eq!(fld[&s.value], F::Base, "compaction relocates only Base values");
            assert_eq!(at.get(&s.value), Some(&s.from));
            occ.remove(&s.from);
            assert!(occ.get(&s.to).is_none(), "Base move clobbers a live cell @ {} (target not free)", s.to);
            occ.insert(s.to, s.value);
            at.insert(s.value, s.to);
        }
        at
    }

    // B: DIRECT test of the Base-relocation compaction helper (spec OP-4). A fragmented occupancy where
    //    every 4-aligned quad holds >=1 live Base (so no clean quad for an incoming Ext) but total width
    //    + the Ext fits in budget MUST be resolvable by relocating the fewest-Base quad's Bases to free
    //    1-cells outside it. Asserts a clean quad results, only Bases move, targets are free (simulate).
    #[test]
    fn compaction_clears_a_quad_by_relocating_fewest_bases() {
        // budget 12 = quads {0..3, 4..7, 8..11}. Live: Base@0 (quad0), Base@4 (quad1), Base@8, Base@9 (quad2).
        // No clean quad; free cells = {1,2,3,5,6,7,10,11}. Incoming Ext (4) => total 4+4 = 8 <= 12 (feasible).
        let widths: HashMap<ExprId, F> = [(v(1), F::Base), (v(2), F::Base), (v(3), F::Base), (v(4), F::Base)].into();
        let live = [(v(1), 0u16, F::Base), (v(2), 4u16, F::Base), (v(3), 8u16, F::Base), (v(4), 9u16, F::Base)];
        // clear_quad_for_ext returns (cleared_quad_start, base moves) to open a clean quad for one Ext.
        let (quad, moves) = clear_quad_for_ext(&live, &widths, 12).expect("a clean quad must be openable");
        assert!(!moves.is_empty(), "a fragmented layout must relocate at least one Base");
        assert!(moves.iter().all(|m| widths[&m.value] == F::Base), "compaction moves ONLY Base values");
        assert_eq!(quad % 4, 0, "cleared quad is 4-aligned");
        // Simulate: every move is to a free cell (clobber-safe), and the cleared quad ends empty.
        let final_at = simulate(&moves, &live);
        for c in quad..quad + 4 {
            assert!(!final_at.values().any(|&base| base == c), "quad cell {c} must be free after compaction");
        }
    }

    // B2 (primary lever): lifetime-aware placement AVOIDS compaction when possible. Two Bases whose
    //    lifetimes overlap an Ext must be packed into ONE quad, leaving the other clean for the Ext —
    //    so plan_placement emits NO moves.
    #[test]
    fn lifetime_aware_placement_avoids_compaction() {
        // budget 8 = quads {0..3, 4..7}. b1,b2 (Base) live across e3 (Ext); a-priori packs b1,b2 into one
        // quad so the other stays clean for e3 -> no compaction.
        let widths: HashMap<ExprId, F> = [(v(1), F::Base), (v(2), F::Base), (v(3), F::Ext)].into();
        let instrs = vec![
            VirtualInstr { op: VInstrKind::Mov, field: F::Base, defines: Some(v(1)), reads: vec![VirtualOp::Global{slot:0,col:0}], sign: Sign::Plus, is_dram_read: true },
            VirtualInstr { op: VInstrKind::Mov, field: F::Base, defines: Some(v(2)), reads: vec![VirtualOp::Global{slot:0,col:1}], sign: Sign::Plus, is_dram_read: true },
            // e3 defined while b1,b2 still live (both in resident_after) -> needs a clean quad concurrently.
            VirtualInstr { op: VInstrKind::Mov, field: F::Ext, defines: Some(v(3)), reads: vec![VirtualOp::Value(v(1))], sign: Sign::Plus, is_dram_read: false },
        ];
        let steps = vec![step(&[], &[1, 2, 3])];
        let step_of = vec![0, 0, 0];
        let input = PlacementInput { instrs: &instrs, steps: &steps, step_of_instr: &step_of, widths: &widths, budget: 8 };
        let p = plan_placement(&input).unwrap();
        assert!(p.moves.is_empty(), "lifetime-aware placement should keep a quad clean for e3, no compaction");
        // e3 got a 4-aligned quad; b1,b2 share the other.
        let e = p.cell_of[&(2, v(3))];
        assert_eq!(e % 4, 0, "Ext is 4-aligned");
    }

    // C: a resident set whose total width exceeds budget is rejected (feasibility guard).
    #[test]
    fn oversized_resident_set_is_rejected() {
        let widths: HashMap<ExprId, F> = [(v(1), F::Ext), (v(2), F::Ext), (v(3), F::Ext)].into();
        let instrs = vec![
            VirtualInstr { op: VInstrKind::Mov, field: F::Ext, defines: Some(v(1)), reads: vec![VirtualOp::Global{slot:0,col:0}], sign: Sign::Plus, is_dram_read: true },
            VirtualInstr { op: VInstrKind::Mov, field: F::Ext, defines: Some(v(2)), reads: vec![VirtualOp::Global{slot:0,col:1}], sign: Sign::Plus, is_dram_read: true },
            VirtualInstr { op: VInstrKind::Mov, field: F::Ext, defines: Some(v(3)), reads: vec![VirtualOp::Global{slot:0,col:2}], sign: Sign::Plus, is_dram_read: true },
        ];
        let steps = vec![step(&[], &[1, 2, 3])]; // 3 Ext = 12 cells > budget 8
        let step_of = vec![0, 0, 0];
        let input = PlacementInput { instrs: &instrs, steps: &steps, step_of_instr: &step_of, widths: &widths, budget: 8 };
        assert!(plan_placement(&input).is_err(), "resident width 12 > budget 8 must be rejected");
    }

    // D: no-extra-residency — the set of values holding a cell at a step boundary equals
    //    exactly resident_after (reconstructed from the placement, not from the input sets),
    //    and an implicit cross-step drop frees its cell with no move/traffic.
    #[test]
    fn realized_live_set_matches_resident_after() {
        let widths: HashMap<ExprId, F> = [(v(1), F::Base), (v(2), F::Base)].into();
        let instrs = vec![
            VirtualInstr { op: VInstrKind::Mov, field: F::Base, defines: Some(v(1)), reads: vec![VirtualOp::Global{slot:0,col:0}], sign: Sign::Plus, is_dram_read: true },
            VirtualInstr { op: VInstrKind::Mov, field: F::Base, defines: Some(v(2)), reads: vec![VirtualOp::Global{slot:0,col:1}], sign: Sign::Plus, is_dram_read: true },
        ];
        // step0 ends with only {2} resident: v1 was produced but is an implicit drop (not in resident_after).
        let steps = vec![step(&[], &[2])];
        let step_of = vec![0, 0];
        let input = PlacementInput { instrs: &instrs, steps: &steps, step_of_instr: &step_of, widths: &widths, budget: 16 };
        let p = plan_placement(&input).unwrap();
        // At the last instr of step 0, exactly v2 holds a cell; v1's cell was freed (implicit drop, no move).
        let last = instrs.len() - 1;
        assert!(p.cell_of.contains_key(&(last, v(2))), "resident_after value 2 must hold a cell");
        assert!(!p.cell_of.contains_key(&(last, v(1))), "dropped value 1 must NOT hold a cell at step end");
        assert!(p.moves.is_empty(), "an implicit drop frees a cell with no defrag move");
    }

    // E: FORCED compaction through plan_placement is DETERMINISTIC (the review finding).
    //    Twelve Bases fill all three quads of a budget-12 space (pack-first), then six of
    //    them free, leaving exactly TWO live Bases per quad — cells {0,1},{4,5},{8,9} —
    //    a fully fragmented layout with NO clean quad. An Ext demand then arrives while
    //    those six Bases are live (current_live_width 6 + 4 = 10 <= 12), forcing
    //    `clear_quad_for_ext` on quad0's TWO Bases. With two movers there is a real
    //    from->to PAIRING choice, and `plan_placement` builds the compaction's input from
    //    a `HashMap` (nondeterministic iteration order) — so WITHOUT the sort-by-`from`
    //    fix the pairing (and thus the emitted `moves`) would vary run-to-run and break
    //    byte-exact program parity once Task 3 consumes `moves`. Asserts the EXACT moves
    //    (pins the target-selection policy) + clobber-safety via `simulate` + the Ext
    //    landing in the cleared quad, then proves order-independence directly by calling
    //    `clear_quad_for_ext` on the SAME occupancy in two different slice orders.
    #[test]
    fn forced_compaction_moves_are_deterministic() {
        let budget = 12;
        // v(1)..v(12) Base, v(13) Ext.
        let mut widths: HashMap<ExprId, F> = HashMap::new();
        for i in 1..=12u32 {
            widths.insert(v(i), F::Base);
        }
        widths.insert(v(13), F::Ext);

        // instrs 0..=10 define v1..v11 (each a plain Global read — no Value reads, so
        // placement is pure pack-first). instr 11 defines v12 AND reads the six Bases
        // that must drop (last_use = 11): v3,v4,v7,v8,v11 as Value operands (v12 itself
        // is never read -> L6 last_use = def = 11). instr 12 defines the Ext v13 and
        // reads the six survivors v1,v2,v5,v6,v9,v10 (last_use = 12, still live).
        let mut instrs: Vec<VirtualInstr> = Vec::new();
        for n in 1..=11u32 {
            instrs.push(VirtualInstr {
                op: VInstrKind::Mov, field: F::Base, defines: Some(v(n)),
                reads: vec![VirtualOp::Global { slot: 0, col: (n - 1) as u16 }],
                sign: Sign::Plus, is_dram_read: true,
            });
        }
        instrs.push(VirtualInstr {
            op: VInstrKind::Mov, field: F::Base, defines: Some(v(12)),
            reads: [3u32, 4, 7, 8, 11].iter().map(|&x| VirtualOp::Value(v(x))).collect(),
            sign: Sign::Plus, is_dram_read: false,
        });
        instrs.push(VirtualInstr {
            op: VInstrKind::Add, field: F::Ext, defines: Some(v(13)),
            reads: [1u32, 2, 5, 6, 9, 10].iter().map(|&x| VirtualOp::Value(v(x))).collect(),
            sign: Sign::Plus, is_dram_read: false,
        });

        let steps = vec![step(&[], &[])]; // no cross-step residency; last_use is read-driven
        let step_of = vec![0usize; instrs.len()];
        let input = PlacementInput { instrs: &instrs, steps: &steps, step_of_instr: &step_of, widths: &widths, budget };
        let p = plan_placement(&input).unwrap();

        // (b) EXACT expected moves: quad0's two Bases (v1@0, v2@1) relocate to the first
        // two free cells of an already-occupied quad (6, 7 in quad1), sorted by `from`.
        let as_tuple = |m: &RelocStep| (m.value, m.from, m.to);
        assert_eq!(p.moves.len(), 2, "quad0 has two Bases -> two relocations, got {:?}", p.moves);
        assert!(p.moves.iter().all(|&(idx, _)| idx == 12), "compaction happens at the Ext-demand instr");
        assert!(p.moves.iter().all(|&(_, m)| widths[&m.value] == F::Base), "compaction moves ONLY Base values");
        assert_eq!(as_tuple(&p.moves[0].1), (v(1), 0u16, 6u16), "v1 (cell 0) -> first free occupied-quad cell (6)");
        assert_eq!(as_tuple(&p.moves[1].1), (v(2), 1u16, 7u16), "v2 (cell 1) -> next free occupied-quad cell (7)");

        // Ext landed in the cleared quad (cell 0, 4-aligned).
        let e = p.cell_of[&(12, v(13))];
        assert_eq!(e, 0, "Ext takes the cleared quad");
        assert_eq!(e % 4, 0, "Ext is 4-aligned");

        // (a) clobber-safety: replay the emitted moves against the pre-compaction live set
        // and confirm the cleared quad ends empty (simulate panics on any clobber).
        let pre = [
            (v(1), 0u16, F::Base), (v(2), 1u16, F::Base),
            (v(5), 4u16, F::Base), (v(6), 5u16, F::Base),
            (v(9), 8u16, F::Base), (v(10), 9u16, F::Base),
        ];
        let relocs: Vec<RelocStep> = p.moves.iter().map(|&(_, m)| m).collect();
        let final_at = simulate(&relocs, &pre);
        for c in 0u16..4 {
            assert!(!final_at.values().any(|&base| base == c), "quad0 cell {c} must be free after compaction");
        }

        // Order-independence, directly at the helper: the SAME occupancy in ascending vs
        // reversed slice order must yield IDENTICAL (quad, moves). This is what the
        // sort-by-`from` fix guarantees; without it the reversed input pairs v2->6, v1->7.
        let ascending = pre.to_vec();
        let mut reversed = pre.to_vec();
        reversed.reverse();
        let (qa, ma) = clear_quad_for_ext(&ascending, &widths, budget).expect("compaction feasible");
        let (qb, mb) = clear_quad_for_ext(&reversed, &widths, budget).expect("compaction feasible");
        assert_eq!(qa, qb, "cleared quad must not depend on input-slice order");
        let tuples = |ms: &[RelocStep]| ms.iter().map(|m| (m.value, m.from, m.to)).collect::<Vec<_>>();
        assert_eq!(tuples(&ma), tuples(&mb), "emitted moves must be independent of input-slice order");
        assert_eq!(tuples(&ma), vec![(v(1), 0, 6), (v(2), 1, 7)], "moves pin the from->to pairing");
    }
}
