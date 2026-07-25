//! Lifetime-overlap cell allocator for the Stage-3 forward-program generator (spec
//! OP-2, OP-4, OP-5-packing).
//!
//! Pure over synthetic inputs — no `arith.rs`/`compile_layer` dependency. Consumes a
//! flat, already-scheduled instruction stream (`VirtualInstr`) plus the per-step
//! `resident_before`/`resident_after` membership ([`ResidencyStep`], a local,
//! schedule-schema-agnostic type — post-schema-v2 (Task 4) the caller always hands
//! this module residency-FREE steps; see `mod.rs::compile_layer`'s
//! `free_steps`) and produces a concrete cell assignment (`Placement`).
//!
//! Placement is a two-phase interval packing, **Ext-first** (widths: Base = 1 cell;
//! Ext = 4 cells, 4-aligned). The instruction stream is frozen and every value's
//! `[def, last_use]` live range is known up front, so this is a pure offline packing
//! problem — no forward eviction, no relocation, no cyclical recompute dependency.
//!
//! The packing itself lives in [`crate::interval_pack`], generic over a stable value
//! id, because the backward coefficient-term scheduler packs the same two widths over
//! the same four-lane-aligned cell file. This module is the FORWARD adapter: it owns
//! the `VirtualInstr`/`ResidencyStep` input shape, the forward live-range derivation
//! ([`compute_live_ranges`]), the `Base`/`Ext` ↔ [`PackWidth`] mapping, and the
//! translation of a [`PackFailure`] into `CompileError::BudgetBelowFloor`. The
//! algorithm, its `(def, id)` packing order, its greedy fast path and its
//! backtracking fallback are unchanged — see [`crate::interval_pack`]'s module doc
//! for the two phases.
//!
//! Because a Base is never assigned a cell an Ext will occupy, **an Ext never has to
//! evict a Base**: the placement is relocation-free by construction (`Placement::moves`
//! is always empty). This supersedes the earlier forward-scan allocator whose greedy,
//! lifetime-blind Base placement could strand a long-lived Base in a quad a later Ext
//! then reclaimed, forcing a compaction relocation (one extra cell→cell `MOV` per row).
//!
//! Feasibility: if some value finds no legal cell, the layer does not fit at this
//! `budget` and we return `BudgetBelowFloor` — the caller's fill-then-trim wrapper
//! then admits fewer cached values and retries, exactly as before.
//!
//! One naming note: this module's `budget` counts the same quantity
//! [`crate::interval_pack`] calls `lanes` (Base = 1, Ext = 4), so the forward `b16`
//! budget is 16 of them. It is passed through unchanged.

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::ExprId;

use crate::fwd::compile::CompileError;
use crate::fwd::isa::{LdcSub, OperandField, Sign};
use crate::interval_pack::{self, Interval, PackFailure, PackWidth};

/// Per-step resident-set membership this allocator's lifetime analysis reads
/// (`resident_before`/`resident_after`). Local to this module — NOT the persisted
/// schedule schema (`cs::dag_ir::LayerSchedule`, schema v2, has no per-step residency
/// anymore; see module doc). `mod.rs::compile_layer` always passes
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

/// Instrumentation record for one compaction relocation: the surviving Base that was
/// moved to clear a quad for an incoming Ext, annotated with both values' live ranges.
/// Emitted once per `RelocStep`; entries sharing an `at_instr`/`cleared_quad`/`ext_value`
/// belong to the same compaction event. Lets a diagnostic distinguish "the doomed quad
/// held a long-surviving Base" (a placement-ordering wart — a lifetime-aware base
/// placement could have kept the quad clean) from genuinely unavoidable fragmentation.
#[derive(Clone, Copy, Debug)]
pub struct MoveCtx {
    pub at_instr: usize,     // the Ext def instr whose placement forced this compaction
    pub cleared_quad: u16,   // quad start the Ext will occupy
    pub ext_value: ValueId,  // the incoming Ext
    pub ext_last_use: usize, // ext's last_use (how long the reclaimed quad stays busy)
    pub moved_value: ValueId,
    pub moved_def: usize,      // where the relocated Base was defined
    pub moved_last_use: usize, // how long it survives past `at_instr` (why it had to move)
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
    /// Per-relocation instrumentation (parallel to the relocations in `moves`);
    /// empty when no compaction fired. See [`MoveCtx`].
    pub move_ctx: Vec<MoveCtx>,
}

// ─────────────────────────────────────────────────────────────────────────────────
// Live ranges.
// ─────────────────────────────────────────────────────────────────────────────────

/// The forward spelling of [`crate::interval_pack::Interval`]. Same inclusive
/// `[def, last_use]` semantics; the alias keeps this module's own vocabulary while
/// the packer owns the type.
type LiveRange = Interval;

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

/// The packer's width for a forward value: `Ext` is one four-cell aligned quad,
/// `Base` one cell. Panics on a value with no recorded width, exactly as before —
/// `mod.rs`'s `defines` scan is exhaustive, so a miss is a compiler bug, not input
/// data.
fn pack_width_of(widths: &HashMap<ValueId, OperandField>, v: ValueId) -> PackWidth {
    match widths.get(&v) {
        Some(OperandField::Ext) => PackWidth::Quad,
        Some(OperandField::Base) => PackWidth::Single,
        None => panic!("no width recorded for value {v:?}"),
    }
}

fn width_of(widths: &HashMap<ValueId, OperandField>, v: ValueId) -> usize {
    pack_width_of(widths, v).lanes()
}

// ─────────────────────────────────────────────────────────────────────────────────
// Two-phase interval packing (Ext-first) — the adapter onto `crate::interval_pack`.
// ─────────────────────────────────────────────────────────────────────────────────

/// Assign a fixed cell to every value: a 4-aligned quad per Ext, a single cell per Base,
/// such that no two time-overlapping values share a cell and no Base ever lands in a
/// live Ext's quad (⇒ relocation-free).
///
/// Delegates to [`interval_pack::assign_lanes`], which is the same greedy-lowest-fit
/// fast path plus backtracking fallback this function always ran; only the
/// `Base`/`Ext` ↔ [`PackWidth`] mapping and the `BudgetBelowFloor` floor spelling are
/// forward-specific and stay here. The three floors are exactly the ones this function
/// reported before the extraction: the width-weighted peak, `(n_quads + 1) * 4` when the
/// Ext demand alone overflows, and `budget + 1` when no coloring seats the Bases.
fn assign_cells(
    ranges: &HashMap<ValueId, LiveRange>,
    widths: &HashMap<ValueId, OperandField>,
    budget: usize,
) -> Result<HashMap<ValueId, u16>, CompileError> {
    interval_pack::assign_lanes(ranges, |v| pack_width_of(widths, v), budget)
        .map_err(|e: PackFailure| CompileError::BudgetBelowFloor { floor: e.floor(budget), budget })
}

pub fn plan_placement(input: &PlacementInput) -> Result<Placement, CompileError> {
    let n = input.instrs.len();
    let ranges = compute_live_ranges(input);
    let cell_of_value = assign_cells(&ranges, input.widths, input.budget)?;

    // ── Materialize: each value holds its fixed cell(s) for every instr in [def, last_use]
    //    (no relocation, so the cell is constant over the range). `max_live_cells` is the
    //    peak width-weighted occupancy over the instruction stream.
    let mut cell_of: HashMap<(usize, ValueId), u16> = HashMap::new();
    let mut width_at: Vec<usize> = vec![0; n.max(1)];
    for (&v, &c) in &cell_of_value {
        let r = ranges[&v];
        let w = width_of(input.widths, v);
        for i in r.def..=r.last_use {
            if i < n {
                cell_of.insert((i, v), c);
                width_at[i] += w;
            }
        }
    }
    let max_live_cells = width_at.iter().copied().max().unwrap_or(0);

    Ok(Placement { cell_of, moves: Vec::new(), max_live_cells, move_ctx: Vec::new() })
}

/// Diagnostic sibling of [`plan_placement`] (Task 6 LIGHT peak-composition readout).
/// Produces a BYTE-IDENTICAL [`Placement`] (same `compute_live_ranges` / `assign_cells`
/// / width-weighted fill), and additionally returns the PEAK instruction index (the
/// lowest-index argmax of the per-instr live occupancy `width_at`) and the values live
/// there, each paired with its cell width (Ext = 4, Base = 1). Additive — `plan_placement`
/// is untouched. Invariant (asserted by the Task-6 attribution test): `sum(width for
/// (_, width) in live) == placement.max_live_cells`, since `peak` is exactly the argmax of
/// `width_at` and `live` enumerates the same values that contribute to `width_at[peak]`.
pub fn plan_placement_with_peak(
    input: &PlacementInput,
) -> Result<(Placement, usize, Vec<(ValueId, usize)>), CompileError> {
    let n = input.instrs.len();
    let ranges = compute_live_ranges(input);
    let cell_of_value = assign_cells(&ranges, input.widths, input.budget)?;

    // Same materialize/fill as `plan_placement` (kept in lockstep so the returned
    // `Placement` matches it exactly).
    let mut cell_of: HashMap<(usize, ValueId), u16> = HashMap::new();
    let mut width_at: Vec<usize> = vec![0; n.max(1)];
    for (&v, &c) in &cell_of_value {
        let r = ranges[&v];
        let w = width_of(input.widths, v);
        for i in r.def..=r.last_use {
            if i < n {
                cell_of.insert((i, v), c);
                width_at[i] += w;
            }
        }
    }
    let max_live_cells = width_at.iter().copied().max().unwrap_or(0);

    // Peak = lowest-index argmax of `width_at`. Keying on `(w, Reverse(i))` with distinct
    // indices makes the unique maximum the highest width and — among ties — the lowest index.
    let peak = width_at
        .iter()
        .copied()
        .enumerate()
        .max_by_key(|&(i, w)| (w, std::cmp::Reverse(i)))
        .map(|(i, _)| i)
        .unwrap_or(0);

    // Values live at `peak`, each with its cell width. `def <= peak <= last_use` selects
    // exactly the values that summed into `width_at[peak] == max_live_cells`.
    let mut live: Vec<(ValueId, usize)> = ranges
        .iter()
        .filter(|(_, r)| r.def <= peak && peak <= r.last_use)
        .map(|(&v, _)| (v, width_of(input.widths, v)))
        .collect();
    live.sort_by_key(|(v, _)| v.0);

    Ok((Placement { cell_of, moves: Vec::new(), max_live_cells, move_ctx: Vec::new() }, peak, live))
}

#[cfg(test)]
mod tests {
    use super::*; // VInstrKind, VirtualOp, VirtualInstr, PlacementInput, Placement, plan_placement
    use crate::fwd::isa::{OperandField as F, Sign};
    use cs::gkr_compiler::dag_ir::ExprId;
    use std::collections::HashMap;

    fn v(n: u32) -> ExprId {
        ExprId(n)
    }

    /// The free-function spelling of [`Interval::overlaps`] these tests were written
    /// against, kept so the oracle and the validity checks read as before.
    fn overlaps(a: &LiveRange, b: &LiveRange) -> bool {
        a.overlaps(b)
    }

    // Helper: one step whose resident sets are the given ExprId lists.
    fn step(before: &[u32], after: &[u32]) -> ResidencyStep {
        ResidencyStep {
            resident_before: before.iter().map(|&x| v(x)).collect(),
            resident_after: after.iter().map(|&x| v(x)).collect(),
        }
    }

    fn load(n: u32, field: F, col: u16) -> VirtualInstr {
        VirtualInstr {
            op: VInstrKind::Mov, field, defines: Some(v(n)),
            reads: vec![VirtualOp::Global { slot: 0, col }], sign: Sign::Plus, is_dram_read: true,
        }
    }

    // THE core invariant of two-phase placement: at every instr, no Base occupies a cell
    // inside a live Ext's quad. This is exactly what makes the placement relocation-free —
    // an Ext never has to evict a Base — so it must hold for every accepted placement.
    fn assert_ext_base_disjoint(p: &Placement, widths: &HashMap<ExprId, F>) {
        let mut by_instr: HashMap<usize, Vec<(ExprId, u16)>> = HashMap::new();
        for (&(i, val), &c) in &p.cell_of {
            by_instr.entry(i).or_default().push((val, c));
        }
        for (&i, vals) in &by_instr {
            let ext_quads: Vec<u16> =
                vals.iter().filter(|(val, _)| widths[val] == F::Ext).map(|&(_, c)| c / 4).collect();
            for &(val, c) in vals {
                if widths[&val] == F::Base {
                    assert!(
                        !ext_quads.contains(&(c / 4)),
                        "Base {val:?}@cell{c} sits in a live Ext's quad at instr {i}"
                    );
                }
            }
        }
        assert!(p.moves.is_empty(), "two-phase placement is relocation-free by construction");
    }

    // Two time-overlapping Exts get non-overlapping 4-aligned quads; live width <= budget.
    #[test]
    fn ext_values_get_4_aligned_nonoverlapping_cells() {
        let widths: HashMap<ExprId, F> = [(v(1), F::Ext), (v(2), F::Ext)].into();
        let instrs = vec![
            load(1, F::Ext, 0),
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
        assert_ext_base_disjoint(&p, &widths);
    }

    // Ext-first: two Exts DISJOINT in time reuse the SAME quad (interval partitioning uses
    // the peak concurrent Ext count, not the total Ext count).
    #[test]
    fn disjoint_exts_reuse_a_quad() {
        let widths: HashMap<ExprId, F> = [(v(1), F::Ext), (v(2), F::Ext)].into();
        // e1 defined+last-used at instr0 (never read again); e2 defined at instr1. Disjoint.
        let instrs = vec![load(1, F::Ext, 0), load(2, F::Ext, 1)];
        let steps = vec![step(&[], &[]), step(&[], &[])];
        let step_of = vec![0, 1];
        let input = PlacementInput { instrs: &instrs, steps: &steps, step_of_instr: &step_of, widths: &widths, budget: 8 };
        let p = plan_placement(&input).unwrap();
        assert_eq!(p.cell_of[&(0, v(1))], 0, "e1 takes quad 0");
        assert_eq!(p.cell_of[&(1, v(2))], 0, "disjoint e2 reuses quad 0");
        assert_ext_base_disjoint(&p, &widths);
    }

    // Base phase: an Ext gets its clean quad and time-overlapping Bases pack into the
    // residual — never inside the Ext's quad, and with NO relocation.
    #[test]
    fn overlapping_bases_pack_around_the_ext() {
        // budget 8 = quads {0..3, 4..7}. b1,b2 (Base) live across e3 (Ext).
        let widths: HashMap<ExprId, F> = [(v(1), F::Base), (v(2), F::Base), (v(3), F::Ext)].into();
        let instrs = vec![
            load(1, F::Base, 0),
            load(2, F::Base, 1),
            // e3 defined while b1,b2 still live (all in resident_after).
            VirtualInstr { op: VInstrKind::Mov, field: F::Ext, defines: Some(v(3)), reads: vec![VirtualOp::Value(v(1))], sign: Sign::Plus, is_dram_read: false },
        ];
        let steps = vec![step(&[], &[1, 2, 3])];
        let step_of = vec![0, 0, 0];
        let input = PlacementInput { instrs: &instrs, steps: &steps, step_of_instr: &step_of, widths: &widths, budget: 8 };
        let p = plan_placement(&input).unwrap();
        let e = p.cell_of[&(2, v(3))];
        assert_eq!(e % 4, 0, "Ext is 4-aligned");
        // b1,b2 live at instr 2 (they're read/resident there); neither shares the Ext quad.
        let eq = e / 4;
        assert_ne!(p.cell_of[&(2, v(1))] / 4, eq, "b1 not in the Ext quad");
        assert_ne!(p.cell_of[&(2, v(2))] / 4, eq, "b2 not in the Ext quad");
        assert_ext_base_disjoint(&p, &widths);
    }

    // Base phase: two Bases DISJOINT in time share ONE cell (each cell is packed with
    // non-overlapping intervals — "pack a single cell as tightly as possible").
    #[test]
    fn disjoint_bases_share_a_cell() {
        let widths: HashMap<ExprId, F> = [(v(1), F::Base), (v(2), F::Base)].into();
        // b1 def+last-used at instr0; b2 at instr1. Disjoint -> same cell.
        let instrs = vec![load(1, F::Base, 0), load(2, F::Base, 1)];
        let steps = vec![step(&[], &[]), step(&[], &[])];
        let step_of = vec![0, 1];
        let input = PlacementInput { instrs: &instrs, steps: &steps, step_of_instr: &step_of, widths: &widths, budget: 8 };
        let p = plan_placement(&input).unwrap();
        assert_eq!(p.cell_of[&(0, v(1))], 0, "b1 -> cell 0");
        assert_eq!(p.cell_of[&(1, v(2))], 0, "disjoint b2 reuses cell 0");
        assert_eq!(p.max_live_cells, 1, "never more than one Base live at once");
    }

    // A resident set whose Ext demand exceeds the quad budget is rejected (feasibility).
    #[test]
    fn oversized_ext_set_is_rejected() {
        let widths: HashMap<ExprId, F> = [(v(1), F::Ext), (v(2), F::Ext), (v(3), F::Ext)].into();
        let instrs = vec![load(1, F::Ext, 0), load(2, F::Ext, 1), load(3, F::Ext, 2)];
        let steps = vec![step(&[], &[1, 2, 3])]; // 3 concurrent Ext = 12 cells > budget 8 (2 quads)
        let step_of = vec![0, 0, 0];
        let input = PlacementInput { instrs: &instrs, steps: &steps, step_of_instr: &step_of, widths: &widths, budget: 8 };
        assert!(plan_placement(&input).is_err(), "3 concurrent Ext do not fit in 2 quads");
    }

    // No-extra-residency: exactly resident_after holds a cell at a step boundary, and an
    // implicit cross-step drop frees its cell with no move.
    #[test]
    fn realized_live_set_matches_resident_after() {
        let widths: HashMap<ExprId, F> = [(v(1), F::Base), (v(2), F::Base)].into();
        let instrs = vec![load(1, F::Base, 0), load(2, F::Base, 1)];
        // step0 ends with only {2} resident: v1 was produced but is an implicit drop.
        let steps = vec![step(&[], &[2])];
        let step_of = vec![0, 0];
        let input = PlacementInput { instrs: &instrs, steps: &steps, step_of_instr: &step_of, widths: &widths, budget: 16 };
        let p = plan_placement(&input).unwrap();
        let last = instrs.len() - 1;
        assert!(p.cell_of.contains_key(&(last, v(2))), "resident_after value 2 must hold a cell");
        assert!(!p.cell_of.contains_key(&(last, v(1))), "dropped value 1 must NOT hold a cell at step end");
        assert!(p.moves.is_empty(), "an implicit drop frees a cell with no move");
    }

    // Regression: the exact layout that the OLD forward-scan allocator resolved with a
    // compaction relocation. Twelve Bases fill budget-12; six drop at instr 11; an Ext
    // then arrives at instr 12 while six Bases survive. The old allocator, having parked
    // survivors across all three quads, had no clean quad and relocated one. Two-phase
    // reserves the Ext's quad in phase 1 and packs every Base around it in phase 2 — so
    // the layer is feasible with ZERO relocations.
    #[test]
    fn former_compaction_case_needs_zero_relocations() {
        let budget = 12;
        let mut widths: HashMap<ExprId, F> = HashMap::new();
        for i in 1..=12u32 {
            widths.insert(v(i), F::Base);
        }
        widths.insert(v(13), F::Ext);

        // instrs 0..=10 define v1..v11 (plain Global reads). instr 11 defines v12 and reads
        // v3,v4,v7,v8,v11 (their last use). instr 12 defines Ext v13 and reads the six
        // survivors v1,v2,v5,v6,v9,v10.
        let mut instrs: Vec<VirtualInstr> = (1..=11u32).map(|n| load(n, F::Base, (n - 1) as u16)).collect();
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

        let steps = vec![step(&[], &[])];
        let step_of = vec![0usize; instrs.len()];
        let input = PlacementInput { instrs: &instrs, steps: &steps, step_of_instr: &step_of, widths: &widths, budget };
        let p = plan_placement(&input).unwrap();

        assert!(p.moves.is_empty(), "two-phase resolves this with zero relocations");
        assert!(p.move_ctx.is_empty(), "no compaction context recorded");
        let e = p.cell_of[&(12, v(13))];
        assert_eq!(e % 4, 0, "Ext is 4-aligned");
        assert!(p.max_live_cells <= budget, "fits the budget");
        assert_ext_base_disjoint(&p, &widths);
    }

    // ── Direct assign_cells packing tests (interval level, no instr stream) ──────────

    fn ranges_of(specs: &[(u32, usize, usize, F)]) -> (HashMap<ExprId, LiveRange>, HashMap<ExprId, F>) {
        let mut ranges = HashMap::new();
        let mut widths = HashMap::new();
        for &(id, def, last, f) in specs {
            ranges.insert(v(id), LiveRange { def, last_use: last });
            widths.insert(v(id), f);
        }
        (ranges, widths)
    }

    /// Validate a `cell_of_value`: Exts 4-aligned and in-bounds; no two time-overlapping
    /// values share any cell.
    fn assert_valid_assignment(
        cells: &HashMap<ExprId, u16>,
        ranges: &HashMap<ExprId, LiveRange>,
        widths: &HashMap<ExprId, F>,
        budget: usize,
    ) {
        let span = |id: &ExprId| -> std::ops::Range<usize> {
            let c = cells[id] as usize;
            c..c + if widths[id] == F::Ext { 4 } else { 1 }
        };
        let ids: Vec<ExprId> = cells.keys().copied().collect();
        for id in &ids {
            let s = span(id);
            assert!(s.end <= budget, "{id:?} span {s:?} exceeds budget {budget}");
            if widths[id] == F::Ext {
                assert_eq!(s.start % 4, 0, "{id:?} Ext not 4-aligned");
            }
        }
        for (i, a) in ids.iter().enumerate() {
            for b in &ids[i + 1..] {
                if overlaps(&ranges[a], &ranges[b]) {
                    let (sa, sb) = (span(a), span(b));
                    assert!(
                        sa.end <= sb.start || sb.end <= sa.start,
                        "time-overlapping {a:?}{sa:?} and {b:?}{sb:?} share a cell"
                    );
                }
            }
        }
    }

    // Exhaustive feasibility oracle for the two-phase model (Ext->quad, Base->cell, no
    // relocation): backtracks over BOTH Ext colorings and Base cell choices. Ground truth
    // that `assign_cells` must match — it must never report infeasible when this says
    // feasible. Small instances only.
    fn oracle_feasible(
        ranges: &HashMap<ExprId, LiveRange>,
        widths: &HashMap<ExprId, F>,
        budget: usize,
    ) -> bool {
        let n_quads = budget / 4;
        let mut exts: Vec<ExprId> = ranges.keys().copied().filter(|v| widths[v] == F::Ext).collect();
        let mut bases: Vec<ExprId> = ranges.keys().copied().filter(|v| widths[v] == F::Base).collect();
        exts.sort_by_key(|x| (ranges[x].def, x.0));
        bases.sort_by_key(|x| (ranges[x].def, x.0));

        fn bases_fit(
            i: usize,
            bases: &[ExprId],
            ranges: &HashMap<ExprId, LiveRange>,
            n_quads: usize,
            budget: usize,
            quads: &[Vec<LiveRange>],
            cell_bases: &mut Vec<Vec<LiveRange>>,
        ) -> bool {
            if i == bases.len() {
                return true;
            }
            let r = ranges[&bases[i]];
            for c in 0..budget {
                let q = c / 4;
                let ext_ok = q >= n_quads || quads[q].iter().all(|o| !overlaps(&r, o));
                if ext_ok && cell_bases[c].iter().all(|o| !overlaps(&r, o)) {
                    cell_bases[c].push(r);
                    if bases_fit(i + 1, bases, ranges, n_quads, budget, quads, cell_bases) {
                        return true;
                    }
                    cell_bases[c].pop();
                }
            }
            false
        }
        fn exts_fit(
            i: usize,
            exts: &[ExprId],
            bases: &[ExprId],
            ranges: &HashMap<ExprId, LiveRange>,
            n_quads: usize,
            budget: usize,
            quads: &mut Vec<Vec<LiveRange>>,
        ) -> bool {
            if i == exts.len() {
                return bases_fit(0, bases, ranges, n_quads, budget, quads, &mut vec![Vec::new(); budget]);
            }
            let r = ranges[&exts[i]];
            for q in 0..n_quads {
                if quads[q].iter().all(|o| !overlaps(&r, o)) {
                    quads[q].push(r);
                    if exts_fit(i + 1, exts, bases, ranges, n_quads, budget, quads) {
                        return true;
                    }
                    quads[q].pop();
                }
            }
            false
        }
        let mut quads = vec![Vec::new(); n_quads];
        exts_fit(0, &exts, &bases, ranges, n_quads, budget, &mut quads)
    }

    // The reviewer's confirmed counterexample: greedy lowest-fit Ext coloring strands the
    // Base, but an alternate coloring seats it. The backtracking fallback must find it.
    #[test]
    fn base_blind_greedy_stranding_is_recovered_by_search() {
        // budget 8 (2 quads). v1 Ext[0,2], v2 Ext[2,4], v3 Base[4,6], v4 Ext[5,5].
        // Greedy: v1->q0, v2->q1, v4[5,5] disjoint from v1 -> reuses q0; then v3[4,6]
        // overlaps v4(q0) and v2(q1) -> no cell. Valid coloring: v4->q1 (with v2), v3->q0.
        let (ranges, widths) =
            ranges_of(&[(1, 0, 2, F::Ext), (2, 2, 4, F::Ext), (4, 5, 5, F::Ext), (3, 4, 6, F::Base)]);
        assert!(oracle_feasible(&ranges, &widths, 8), "the instance IS feasible");
        let cells = assign_cells(&ranges, &widths, 8)
            .expect("backtracking must recover the feasible coloring greedy missed");
        assert_valid_assignment(&cells, &ranges, &widths, 8);
    }

    // Fuzz: across many random small instances at production budgets, `assign_cells`
    // must agree with the exhaustive oracle on feasibility, and every placement it emits
    // must be valid. This is the completeness guard for the two-phase packer.
    #[test]
    fn assign_cells_matches_exhaustive_oracle() {
        // Deterministic LCG (Date/rand are unavailable and would break reproducibility).
        let mut state: u64 = 0x9e3779b97f4a7c15;
        let mut next = |bound: u64| -> u64 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (state >> 33) % bound
        };
        let mut checked = 0usize;
        for _ in 0..4000 {
            let budget = if next(2) == 0 { 8 } else { 12 };
            let n_ext = next(4) as u32; // 0..=3
            let n_base = next(6) as u32; // 0..=5
            let horizon = 8usize;
            let mut specs: Vec<(u32, usize, usize, F)> = Vec::new();
            let mut id = 1u32;
            for _ in 0..n_ext {
                let def = next(horizon as u64) as usize;
                let last = def + next((horizon - def) as u64) as usize;
                specs.push((id, def, last, F::Ext));
                id += 1;
            }
            for _ in 0..n_base {
                let def = next(horizon as u64) as usize;
                let last = def + next((horizon - def) as u64) as usize;
                specs.push((id, def, last, F::Base));
                id += 1;
            }
            let (ranges, widths) = ranges_of(&specs);
            let got = assign_cells(&ranges, &widths, budget);
            let oracle = oracle_feasible(&ranges, &widths, budget);
            assert_eq!(
                got.is_ok(),
                oracle,
                "feasibility mismatch vs oracle: budget={budget} specs={specs:?}"
            );
            if let Ok(cells) = got {
                assert_valid_assignment(&cells, &ranges, &widths, budget);
            }
            checked += 1;
        }
        assert_eq!(checked, 4000);
    }
}
