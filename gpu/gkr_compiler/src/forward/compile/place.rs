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

use gkr_eval_ir::ExprId;

use crate::forward::compile::CompileError;
use crate::forward::isa::{LdcSub, OperandField};
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

#[derive(Clone, Debug)]
pub enum VirtualOp {
    Value(ValueId),
    Global { slot: u8, col: u16 },
    Ldc { sub: LdcSub, idx: u16 },
    Special { desc: u16 },
}

#[derive(Clone, Debug)]
pub struct VirtualInstr {
    pub defines: Option<ValueId>,
    pub reads: Vec<VirtualOp>,
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
    pub max_live_cells: usize,
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
                    instr
                        .reads
                        .iter()
                        .any(|r| matches!(r, VirtualOp::Value(x) if *x == v))
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
            .filter(|(_, instr)| {
                instr
                    .reads
                    .iter()
                    .any(|r| matches!(r, VirtualOp::Value(x) if *x == v))
            })
            .map(|(i, _)| i)
            .max();

        // (b) cross-step residency, clamped at the first implicit cone-fit drop.
        let drop_boundary = (1..input.steps.len()).find(|&p| {
            input.steps[p - 1].resident_after.contains(&v)
                && !input.steps[p].resident_before.contains(&v)
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
        assert!(
            last_use >= d,
            "last_use ({last_use}) < def ({d}) for value {v:?}"
        );
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
    interval_pack::assign_lanes(ranges, |v| pack_width_of(widths, v), budget).map_err(
        |e: PackFailure| CompileError::BudgetBelowFloor {
            floor: e.floor(budget),
            budget,
        },
    )
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

    Ok(Placement {
        cell_of,
        max_live_cells,
    })
}
