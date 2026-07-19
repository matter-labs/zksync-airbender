//! Task 1 (CS-M0): the backward compile EVENT TRACE — a passive, observation-only
//! record of what the bwd lowering did (serve / traffic-read / capacity events),
//! plus the deterministic plan-epoch fingerprint and the per-instruction live
//! profile later tasks consume.
//!
//! Nothing here changes what any program does. The trace is carried by a NEW
//! bwd-only field on `VirtualLower` (`bwd_trace: Option<BwdCompileTrace>`, default
//! `None`) that forward paths never set — so the forward program is byte-identical
//! by construction, and an untraced backward compile is byte-identical to a traced
//! one (only the recorded `events`/`free` differ).

use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};

use cs::gkr_compiler::dag_ir::{Expr, ExprId, SourceKind};

use crate::fwd::binding::BackingTable;
use crate::fwd::isa::{DstLine, Instr, OperandField, OperandLine, Program};

use super::compile::{spine_terms, BwdCompiledLayer};
use super::distill::{distilled_site_domain, DistilledLayer};
use super::source::{BwdSpecial, BwdSpecialTable};

/// Plan ABI version — bumped whenever the plan/trace stream encoding changes so a
/// stale-round plan compiled against an older layout can never be replayed silently
/// (folded into [`plan_epoch`]).
pub const BWD_PLAN_ABI_VERSION: u32 = 1;

// ── serve fingerprints ─────────────────────────────────────────────────────────

/// Which demand a serve satisfies: the backward root's own output (once, at the
/// top of the driver, before any term lowering) or an operand demanded during a
/// term's cone walk.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BwdServeKind {
    RootOutput,
    Operand,
}

/// A serve occurrence, fingerprinted by the spine `term` it fired under, its
/// `kind`, the served `value`, and the `consumer` (the parent expr whose operand
/// walk is serving `value`; `None` for `RootOutput`).
///
/// `consumer` is read from a `consumer_stack: Vec<ExprId>` on `VirtualLower`,
/// pushed/popped around `compile_expr_virtual` (behavior-neutral bookkeeping — the
/// forward path emits nothing from it). Because plans are always built FROM a trace
/// (never re-derived by a demand-walk mirror), any deterministic consumer notion is
/// self-consistent across plan and replay — FMA reparenting is a non-issue by
/// construction. Residual duplicate risk: identical `(term, kind, value, consumer)`
/// pairs only arise for same-consumer double use (`x*x`); cone suppression removes
/// both occurrences together (same cone), and the EOF count check (Task 3) catches
/// any drift.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BwdFingerprint {
    pub term: u32,
    pub kind: BwdServeKind,
    pub value: ExprId,
    pub consumer: Option<ExprId>,
}

/// Where a served value came from at serve time: recomputed from its cone, or read
/// from a resident cell (`self.defined.contains(&value)` when the serve fired).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BwdServedFrom {
    Recomputed,
    Resident,
}

// ── events ───────────────────────────────────────────────────────────────────

/// One observed backward-compile event. Task 1 emits only `Serve` and
/// `TrafficRead`; the capacity events (`Admit`/`Evict`/`Refuse`) and `Diverge` are
/// part of the frozen event vocabulary later CS-M0 tasks fill in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BwdEvent {
    /// A demand was served (root-output or operand).
    Serve { fp: BwdFingerprint, from: BwdServedFrom },
    /// A real DRAM read the objective counts: a `Global` operand (`cells` = its
    /// field width, 1 Base / 4 Ext) or a READ-origin `FoldSource` operand
    /// (`cells` = 4). VS-origin folds emit NO `TrafficRead` — they use the O(k)
    /// closed form (zero DRAM), mirroring the `BwdTrafficStats` invariant.
    TrafficRead { value: ExprId, cells: u32 },
    /// A value was admitted into residency, occupying `width` cells.
    Admit { value: ExprId, width: u8 },
    /// A value left residency; `expired` iff it had no remaining occurrence.
    Evict { value: ExprId, expired: bool },
    /// An admission was refused for want of `need` free cells.
    Refuse { value: ExprId, need: u32 },
    /// The replay diverged from the trace at entry index `at_entry`.
    Diverge { at_entry: usize },
}

// ── trace ────────────────────────────────────────────────────────────────────

/// The full observation record of one backward compile at a fixed `(budget,
/// stream_reductions)`. `epoch` is the [`plan_epoch`] fingerprint of the distilled
/// layer + budget + mode; `free[t] = budget - live_profile[t]` (saturating) is the
/// per-instruction spare-lane envelope.
#[derive(Clone, Debug)]
pub struct BwdCompileTrace {
    pub epoch: u64,
    pub budget: usize,
    pub stream_reductions: bool,
    pub events: Vec<BwdEvent>,
    pub free: Vec<usize>,
}

// ── plan epoch ─────────────────────────────────────────────────────────────────

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

#[inline]
fn fnv_bytes(h: &mut u64, bytes: &[u8]) {
    for &b in bytes {
        *h ^= b as u64;
        *h = h.wrapping_mul(FNV_PRIME);
    }
}

#[inline]
fn fnv_u32(h: &mut u64, v: u32) {
    fnv_bytes(h, &v.to_le_bytes());
}

/// The backward compile DRIVER a plan/trace was produced by (CS-M5a Task 6). Folded
/// into [`plan_epoch`] as a discriminant tag so a plan built by one driver can never
/// satisfy the other driver's planned-compile epoch guard: the term (spine-accumulation)
/// and fragment (full-decomposition) drivers produce STRUCTURALLY DIFFERENT programs from
/// the same distilled layer, so their occurrence streams / serve fingerprints are not
/// interchangeable. Closes the verified hole where a term-built plan passed the fragment
/// planned entry's epoch/`entries_fnv` guards.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DriverMode {
    Term,
    Fragment,
}

fn driver_mode_disc(mode: DriverMode) -> u8 {
    match mode {
        DriverMode::Term => 0,
        DriverMode::Fragment => 1,
    }
}

/// Source-kind discriminant for the plan-epoch content walk (a stable ordinal, not
/// the payload — the payload cannot change under a unit permutation).
fn source_kind_disc(k: &SourceKind) -> u8 {
    match k {
        SourceKind::Read { .. } => 0,
        SourceKind::Constant { .. } => 1,
        SourceKind::Challenge { .. } => 2,
        SourceKind::VirtualSetup { .. } => 3,
        SourceKind::LookupValue { .. } => 4,
    }
}

/// FNV-1a fingerprint over `(BWD_PLAN_ABI_VERSION, regime, budget, stream_reductions,
/// root, + a full content walk of `d.layer.exprs`)`. The content walk feeds, per
/// expr, its discriminant + child `ExprId`s + (for a `Source`) its `SourceId` and
/// source-kind discriminant.
///
/// The walk captures BOTH expression contents and the unit permutation: `distill`
/// re-interns cones in unit execution order, so a different permutation yields a
/// different rebuilt arena. `DistilledLayer.unit_order` itself stays canonical under
/// permutation and is therefore NOT a hash input.
///
/// The TERM entry (spine-accumulation driver). Its VALUE moved with CS-M5a Task 6 (the
/// driver-mode tag is now folded in) — the epoch is an internal staleness guard, never
/// persisted across runs and never pinned, so the value is free to change.
pub fn plan_epoch(d: &DistilledLayer, budget: usize, stream_reductions: bool) -> u64 {
    plan_epoch_mode(d, budget, stream_reductions, DriverMode::Term)
}

/// FRAGMENT entry (full-decomposition driver) of [`plan_epoch`]: same content walk plus
/// the [`DriverMode::Fragment`] tag AND an FNV over the layer's STABLE fragment keys in
/// schedule (fragment-index) order — so a fragment plan is additionally bound to the exact
/// fragment decomposition it was priced against. Deterministic per distilled layer.
pub fn plan_epoch_fragment(d: &DistilledLayer, budget: usize, stream_reductions: bool) -> u64 {
    plan_epoch_mode(d, budget, stream_reductions, DriverMode::Fragment)
}

fn plan_epoch_mode(
    d: &DistilledLayer,
    budget: usize,
    stream_reductions: bool,
    mode: DriverMode,
) -> u64 {
    let mut h = FNV_OFFSET;
    fnv_u32(&mut h, BWD_PLAN_ABI_VERSION);
    fnv_bytes(&mut h, &[driver_mode_disc(mode)]); // CS-M5a T6 driver-mode tag
    fnv_bytes(&mut h, &[d.regime as u8]);
    fnv_bytes(&mut h, &(budget as u64).to_le_bytes());
    fnv_bytes(&mut h, &[stream_reductions as u8]);
    fnv_u32(&mut h, d.root.0);
    for expr in &d.layer.exprs {
        match expr {
            Expr::Source(sid) => {
                fnv_bytes(&mut h, &[0]); // Expr::Source discriminant
                fnv_u32(&mut h, sid.0);
                let kind = &d.layer.sources[sid.0 as usize].kind;
                fnv_bytes(&mut h, &[source_kind_disc(kind)]);
            }
            Expr::Add(children) => {
                fnv_bytes(&mut h, &[1]); // Expr::Add discriminant
                for c in children {
                    fnv_u32(&mut h, c.0);
                }
            }
            Expr::Mul(children) => {
                fnv_bytes(&mut h, &[2]); // Expr::Mul discriminant
                for c in children {
                    fnv_u32(&mut h, c.0);
                }
            }
        }
    }
    if let DriverMode::Fragment = mode {
        // The full-decomposition binding: hash the order-INDEPENDENT stable fragment
        // keys (atoms + coefficient/`c_init` factor-key lists, canonicalized by
        // `FragmentTable::stable_view`/`stable_c_init`) in schedule order. Reduced via a
        // fixed-seed `DefaultHasher` (deterministic within a build; the epoch is a
        // non-persisted internal guard) and folded into the FNV stream.
        let mut fh = DefaultHasher::new();
        d.fragments.stable_view(d).hash(&mut fh);
        d.fragments.stable_c_init(d).hash(&mut fh);
        fnv_bytes(&mut h, &fh.finish().to_le_bytes());
    }
    h
}

// ── live profile ─────────────────────────────────────────────────────────────

/// Per-instruction occupied smem lanes of a placed program: a lane is occupied from
/// the instruction that writes it (`Mov` with `dst = Smem`) through its last read
/// before the lane's next write (write-segmented lifetimes, lane granularity). A
/// read of a never-written lane counts as occupied from t=0 (pre-initialized).
pub fn live_profile(p: &Program) -> Vec<usize> {
    #[derive(Clone, Copy)]
    enum Ev {
        Write,
        Read,
    }
    let n = p.instrs.len();
    // WIRE DECODE (v2, `smem_lane` src/fwd/interp.rs:132-142): a Base `Smem` index is
    // a LANE; an Ext `Smem` index is a BUCKET whose lanes are cell*4 .. cell*4+4.
    // (codex H5a: revision 1 treated Ext cells as lane-addressed and corrupted the
    // profile.)
    let span = |cell: u16, f: OperandField| match f {
        OperandField::Base => (cell as u32, 1u32),
        OperandField::Ext => (cell as u32 * 4, 4u32),
    };
    let mut lanes: BTreeMap<u32, Vec<(usize, Ev)>> = BTreeMap::new();
    let mut push = |lanes: &mut BTreeMap<u32, Vec<(usize, Ev)>>, cell: u16, f: OperandField, t, ev| {
        let (base, width) = span(cell, f);
        for l in base..base + width {
            lanes.entry(l).or_default().push((t, ev));
        }
    };
    for (t, i) in p.instrs.iter().enumerate() {
        match i {
            Instr::Add { field, operands, .. } | Instr::Mul { field, operands, .. } => {
                for op in operands {
                    if let OperandLine::Smem { cell } = op {
                        push(&mut lanes, *cell, *field, t, Ev::Read);
                    }
                }
            }
            Instr::Fma { field_lhs, field_rhs, pairs, .. } => {
                for (l, r) in pairs {
                    if let OperandLine::Smem { cell } = l {
                        push(&mut lanes, *cell, *field_lhs, t, Ev::Read);
                    }
                    if let OperandLine::Smem { cell } = r {
                        push(&mut lanes, *cell, *field_rhs, t, Ev::Read);
                    }
                }
            }
            Instr::Mov { field, dst, src, .. } => {
                if let Some(OperandLine::Smem { cell }) = src {
                    push(&mut lanes, *cell, *field, t, Ev::Read);
                }
                if let Some(DstLine::Smem { cell }) = dst {
                    push(&mut lanes, *cell, *field, t, Ev::Write);
                }
            }
        }
    }
    let mut occ = vec![0usize; n];
    for (_, evs) in lanes {
        let mut i = 0;
        while i < evs.len() {
            let seg_start = match evs[i].1 {
                Ev::Write => evs[i].0,
                Ev::Read => 0,
            };
            let mut seg_end = evs[i].0;
            let mut j = i + 1;
            while j < evs.len() && matches!(evs[j].1, Ev::Read) {
                seg_end = evs[j].0;
                j += 1;
            }
            for t in seg_start..=seg_end {
                occ[t] += 1;
            }
            i = j;
        }
    }
    occ
}

/// Reconstruct the concrete compiler's real DRAM reads and instruction positions
/// from the realized instruction stream. This is the single post-peephole operand
/// scan used by both frozen demand construction and replay certification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PositionedPhysicalTrafficEvent {
    pub instruction: usize,
    pub physical_ordinal: usize,
    pub event: BwdEvent,
}

pub(crate) fn positioned_physical_traffic_events(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    program: &Program,
    specials: &BwdSpecialTable,
    leaf_descs: &BTreeMap<ExprId, u16>,
    backings: &BackingTable,
) -> Option<Vec<PositionedPhysicalTrafficEvent>> {
    let desc_to_leaf: BTreeMap<u16, ExprId> =
        leaf_descs.iter().map(|(&leaf, &desc)| (desc, leaf)).collect();
    let mut events = Vec::new();
    let mut record =
        |instruction: usize, operand: OperandLine, field: OperandField| -> Option<()> {
        let (value, cells) = match operand {
            OperandLine::Global { slot, col } => {
                let place = backings.slot_col_to_read_place(slot, col)?;
                let value = layer.exprs.iter().enumerate().find_map(|(index, expr)| {
                    let Expr::Source(source) = expr else {
                        return None;
                    };
                    match &layer.sources[source.0 as usize].kind {
                        SourceKind::Read { place: candidate } if *candidate == place => {
                            Some(ExprId(index as u32))
                        }
                        _ => None,
                    }
                })?;
                let cells = match field {
                    OperandField::Base => 1,
                    OperandField::Ext => 4,
                };
                (value, cells)
            }
            OperandLine::Special { desc } => match specials.get(desc) {
                Some(BwdSpecial::FoldSource { origin }) if !origin.is_vs() => {
                    (*desc_to_leaf.get(&desc)?, 4)
                }
                _ => return Some(()),
            },
            OperandLine::Smem { .. } | OperandLine::Ldc { .. } => return Some(()),
        };
        let physical_ordinal = events.len();
        events.push(PositionedPhysicalTrafficEvent {
            instruction,
            physical_ordinal,
            event: BwdEvent::TrafficRead { value, cells },
        });
        Some(())
    };

    for (instruction, instr) in program.instrs.iter().enumerate() {
        match instr {
            Instr::Add { field, operands, .. } | Instr::Mul { field, operands, .. } => {
                for &operand in operands {
                    record(instruction, operand, *field)?;
                }
            }
            Instr::Fma { field_lhs, field_rhs, pairs, .. } => {
                for &(lhs, rhs) in pairs {
                    record(instruction, lhs, *field_lhs)?;
                    record(instruction, rhs, *field_rhs)?;
                }
            }
            Instr::Mov { field, src: Some(operand), .. } => {
                record(instruction, *operand, *field)?
            }
            Instr::Mov { src: None, .. } => {}
        }
    }
    Some(events)
}

pub(crate) fn physical_traffic_events(
    layer: &cs::gkr_compiler::dag_ir::DagLayer,
    program: &Program,
    specials: &BwdSpecialTable,
    leaf_descs: &BTreeMap<ExprId, u16>,
    backings: &BackingTable,
) -> Option<Vec<BwdEvent>> {
    positioned_physical_traffic_events(layer, program, specials, leaf_descs, backings).map(
        |events| {
            events
                .into_iter()
                .map(|positioned| positioned.event)
                .collect()
        },
    )
}

/// Preserve the source-resolution traffic anchors only when their complete
/// `(value, width)` multiset exactly matches the final post-peephole program.
/// Partial retention would make duplicate occurrences ambiguous, so any
/// missing or extra physical read fails closed.
pub(crate) fn retain_physical_traffic_events(
    ordered_events: Vec<BwdEvent>,
    physical_events: &[BwdEvent],
) -> Option<Vec<BwdEvent>> {
    let mut anchored = BTreeMap::<(ExprId, u32), usize>::new();
    for event in &ordered_events {
        if let BwdEvent::TrafficRead { value, cells } = event {
            *anchored.entry((*value, *cells)).or_default() += 1;
        }
    }
    let mut physical = BTreeMap::<(ExprId, u32), usize>::new();
    for event in physical_events {
        let BwdEvent::TrafficRead { value, cells } = event else {
            return None;
        };
        *physical.entry((*value, *cells)).or_default() += 1;
    }
    (anchored == physical).then_some(ordered_events)
}

// ── frozen demand (Task 2) ──────────────────────────────────────────────────

/// The frozen all-recompute demand stream D0. Built once from a traced
/// all-recompute compile (`decisions: None`, so no residency ever fires and every
/// `Serve` records the raw demand walk), this is what every later CS-M0 planner
/// (the FiF leaf solver, priced rounds) consumes — plans are always built FROM a
/// frozen snapshot, never re-derived by a fresh demand walk (see module docs).
///
/// `domain_serves` is `trace`'s `Serve` events filtered to values in
/// [`distilled_site_domain`] — the matcher and every planner act ONLY on this
/// filtered stream; non-domain serves carry no actions. `leaf_instants[v]` gives
/// each DOMAIN leaf `v`'s final-program instruction indices at which a real
/// `Global` or READ-origin `FoldSource` operand uses `v` — the FiF gap model's
/// demand instants. `free` is `trace.free`, the per-instruction spare-lane envelope.
///
/// Fan-out-1 leaves and direct top-level read terms are real DRAM traffic with
/// program gathers but NO domain serve (`distilled_site_domain` excludes them) —
/// they must not enter the gap model. Their cells are folded into
/// `nondomain_gather_cells` instead: the constant term of the modeled-traffic
/// baseline Task 8's replay pricing reconciles against
/// (`dram_traffic = stats_ext.global + stats_ext.fold_traffic`).
#[derive(Clone, Debug)]
pub struct FrozenDemand {
    pub epoch: u64,
    pub stream_reductions: bool,
    pub budget: usize,
    pub domain_serves: Vec<(BwdFingerprint, BwdServedFrom)>,
    pub free: Vec<usize>,
    pub leaf_instants: BTreeMap<ExprId, Vec<usize>>,
    pub leaf_accesses: BTreeMap<ExprId, Vec<(usize, usize)>>,
    pub nondomain_gather_cells: usize,
}

/// Whether [`freeze_demand_with`] applies the DIRECT-TOP-LEVEL-READ correction (CS-M5a
/// Task 6): re-crediting a spine's bare-`Source` first term from `leaf_instants` to
/// `nondomain_gather_cells`.
///
/// `Term` — the TERM driver's spine-term loop gathers that first bare-source term via
/// `source_to_vop` with NO accompanying `Serve` (see the block below), so the correction
/// is REQUIRED to restore the leaf-instants↔program alignment; term traces are frozen
/// byte-identically to before this task.
///
/// `None` — the FRAGMENT driver (Task 5.2) gives every top atom a real `Serve`, so no
/// unserved direct-top gather exists and the correction must be SKIPPED (applying it would
/// wrongly evict a genuine served instant).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DirectTopCorrection {
    Term,
    None,
}

fn checked_add_gather_cells(total: &mut usize, cells: u32) -> Option<()> {
    *total = total.checked_add(cells as usize)?;
    Some(())
}

/// Task 2 (CS-M0): freeze the all-recompute demand stream D0 from a traced bwd
/// compile — `d`'s site domain filters `trace`'s `Serve` events into
/// `domain_serves` and gates `leaf_instants` through the authoritative physical
/// traffic scan, with everything outside the domain folded into
/// `nondomain_gather_cells`. The TERM-driver entry applies the direct-top correction
/// (see [`freeze_demand_with`]).
pub fn freeze_demand(
    d: &DistilledLayer,
    trace: &BwdCompileTrace,
    program: &Program,
    specials: &BwdSpecialTable,
    backings: &BackingTable,
) -> Option<FrozenDemand> {
    freeze_demand_with(
        d,
        trace,
        program,
        specials,
        backings,
        DirectTopCorrection::Term,
    )
}

/// CS-M5a Task 6: [`freeze_demand`] parameterized over the [`DirectTopCorrection`] the
/// compile driver requires. `Term` runs the direct-top block (byte-identical to the
/// pre-Task-6 `freeze_demand`); `None` skips it (valid for fragment traces). Everything
/// else is identical across both variants.
pub fn freeze_demand_with(
    d: &DistilledLayer,
    trace: &BwdCompileTrace,
    program: &Program,
    specials: &BwdSpecialTable,
    backings: &BackingTable,
    correction: DirectTopCorrection,
) -> Option<FrozenDemand> {
    let domain_values: BTreeSet<ExprId> =
        distilled_site_domain(d).into_iter().map(|site| site.value).collect();

    let domain_serves: Vec<(BwdFingerprint, BwdServedFrom)> = trace
        .events
        .iter()
        .filter_map(|e| match e {
            BwdEvent::Serve { fp, from } if domain_values.contains(&fp.value) => {
                Some((*fp, *from))
            }
            _ => None,
        })
        .collect();

    // Every `TrafficRead` is exactly a real DRAM read the objective counts (a
    // READ-origin `FoldSource` gather or a bare `Global` read — VS-origin folds
    // emit none, see `BwdEvent::TrafficRead`'s doc), so summing the non-domain
    // ones here is precisely "non-domain READ-origin gathers + Global reads of
    // non-domain values".
    let physical = positioned_physical_traffic_events(
        &d.layer,
        program,
        specials,
        &d.leaf_descs,
        backings,
    )
    ?;
    let mut nondomain_gather_cells = 0usize;
    let mut leaf_traffic = BTreeMap::<ExprId, Vec<(usize, usize, u32)>>::new();
    for positioned in physical {
        let BwdEvent::TrafficRead { value, cells } = positioned.event else {
            unreachable!("the physical traffic scan emits only TrafficRead events");
        };
        if domain_values.contains(&value) {
            leaf_traffic
                .entry(value)
                .or_default()
                .push((positioned.instruction, positioned.physical_ordinal, cells));
        } else {
            checked_add_gather_cells(&mut nondomain_gather_cells, cells)?;
        }
    }

    if let DirectTopCorrection::Term = correction {
        // DOCUMENTED OFFSET RULE: the driver's per-spine-term loop
        // (`lower_bwd_root_virtual`, `fwd/compile/lower.rs` ~2156-2168) compiles EVERY
        // spine term via a direct `compile_expr_virtual` call, bypassing
        // `lower_operand_virtual`'s `serve_occurrence` wrapper entirely. A term that is
        // itself a bare `Source` expr — a "direct top-level read term"; structurally
        // this can only ever be `spine_terms(d)[0]` (the alpha spine's UNSCALED root_0
        // child — every i>=1 term is `beta^i * expr(root_i)`, always a `Mul`, per
        // `distill`'s alpha-spine doc) — therefore gathers via `source_to_vop` (a real
        // `TrafficRead`) with NO accompanying `Serve` event.
        //
        // That term is also the very first thing the driver ever compiles (`cur_step`
        // starts at 0 and nothing upstream of the term loop touches an individual leaf
        // source — the one call before it, `serve_occurrence(root_expr, RootOutput)`,
        // emits no instruction), so this untracked gather is provably the MINIMUM-index
        // program occurrence of that leaf's desc: nothing else in the program can
        // reference it before its own term starts. When such a leaf is ALSO a genuine
        // (fan-out >= 2) domain leaf, this one occurrence is credited to
        // `nondomain_gather_cells` instead of `leaf_instants`, restoring the alignment
        // invariant. A leaf that is ONLY its own bare spine term has fan-out 1 and is
        // already excluded from the site domain (`distilled_site_domain`), so this
        // correction is a no-op for it — its lone gather is already counted above via
        // the plain non-domain `TrafficRead` filter.
        for term in spine_terms(d) {
            if !domain_values.contains(&term) {
                continue;
            }
            if !matches!(d.layer.exprs[term.0 as usize], Expr::Source(_)) {
                continue;
            }
            if let Some(traffic) = leaf_traffic.get_mut(&term) {
                if let Some((min_at, _)) = traffic
                    .iter()
                    .enumerate()
                    .min_by_key(|&(_, &(position, ordinal, _))| (position, ordinal))
                {
                    let (_, _, cells) = traffic.remove(min_at);
                    checked_add_gather_cells(&mut nondomain_gather_cells, cells)?;
                }
            }
        }
    }

    let leaf_instants = leaf_traffic
        .iter()
        .filter_map(|(&value, traffic)| {
            (!traffic.is_empty())
                .then(|| (value, traffic.iter().map(|&(position, _, _)| position).collect()))
        })
        .collect();
    let leaf_accesses = leaf_traffic
        .into_iter()
        .filter_map(|(value, traffic)| {
            (!traffic.is_empty()).then(|| {
                (
                    value,
                    traffic
                        .into_iter()
                        .map(|(instruction, ordinal, _)| (instruction, ordinal))
                        .collect(),
                )
            })
        })
        .collect();

    Some(FrozenDemand {
        epoch: trace.epoch,
        stream_reductions: trace.stream_reductions,
        budget: trace.budget,
        domain_serves,
        free: trace.free.clone(),
        leaf_instants,
        leaf_accesses,
        nondomain_gather_cells,
    })
}

// ── certificate (Task 6) ────────────────────────────────────────────────────

/// Task 6 (CS-M0): the bwd schedule certificate. An exact, tolerance-free
/// re-scoring of a trace's realized `TrafficRead` traffic against the compile's
/// own tally (`dram_traffic = stats_ext.global + stats_ext.fold_traffic`).
///
/// `diverged` / `refusals` / `evictions` are plan-compliance DIAGNOSTICS only
/// (spec §5) — they ride the report for triage but never affect the `Ok`/`Err`
/// decision, which is purely `counted_traffic == reported_traffic`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CertificateReport {
    /// `Σ` over `trace.events` of `TrafficRead.cells` — the traffic the replay
    /// actually realized.
    pub counted_traffic: usize,
    /// `c.stats_ext.global + c.stats_ext.fold_traffic` — the compile's own tally.
    pub reported_traffic: usize,
    /// The `Diverge` event's `at_entry`, if the replay ever diverged from a plan.
    pub diverged: Option<usize>,
    /// Count of `Refuse` events (admissions refused for want of free cells).
    pub refusals: usize,
    /// Count of `Evict` events (includes rule-a releases, a Task-4 design call —
    /// diagnostic only, never gates the certificate).
    pub evictions: usize,
}

/// Certify `trace` against `c`: `Ok(report)` iff the realized `TrafficRead` traffic
/// EXACTLY equals the compile's reported traffic tally (no tolerance); `Err(report)`
/// otherwise, carrying the same fields for diagnosis. Plan-compliance fields
/// (`diverged`, `refusals`, `evictions`) never affect which variant is returned.
pub fn certify(c: &BwdCompiledLayer, trace: &BwdCompileTrace) -> Result<CertificateReport, CertificateReport> {
    let counted_traffic: usize = trace
        .events
        .iter()
        .filter_map(|e| match e {
            BwdEvent::TrafficRead { cells, .. } => Some(*cells as usize),
            _ => None,
        })
        .sum();
    let reported_traffic = c.stats_ext.global + c.stats_ext.fold_traffic;
    let diverged = trace.events.iter().find_map(|e| match e {
        BwdEvent::Diverge { at_entry } => Some(*at_entry),
        _ => None,
    });
    let refusals = trace.events.iter().filter(|e| matches!(e, BwdEvent::Refuse { .. })).count();
    let evictions = trace.events.iter().filter(|e| matches!(e, BwdEvent::Evict { .. })).count();

    let report = CertificateReport { counted_traffic, reported_traffic, diverged, refusals, evictions };
    if counted_traffic == reported_traffic {
        Ok(report)
    } else {
        Err(report)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        BwdEvent, BwdFingerprint, BwdServeKind, BwdServedFrom,
        checked_add_gather_cells, retain_physical_traffic_events,
    };
    use cs::gkr_compiler::dag_ir::ExprId;

    #[test]
    fn nondomain_gather_accumulation_reports_overflow() {
        let mut total = usize::MAX;
        assert_eq!(checked_add_gather_cells(&mut total, 1), None);
        assert_eq!(total, usize::MAX);
    }

    #[test]
    fn physical_traffic_reconciliation_requires_every_duplicate_anchor() {
        let value = ExprId(7);
        let read = BwdEvent::TrafficRead { value, cells: 4 };
        let ordered = vec![
            BwdEvent::Serve {
                fp: BwdFingerprint {
                    term: 0,
                    kind: BwdServeKind::Operand,
                    value,
                    consumer: Some(ExprId(11)),
                },
                from: BwdServedFrom::Recomputed,
            },
            read,
            BwdEvent::Serve {
                fp: BwdFingerprint {
                    term: 1,
                    kind: BwdServeKind::Operand,
                    value,
                    consumer: Some(ExprId(12)),
                },
                from: BwdServedFrom::Recomputed,
            },
            read,
        ];
        let physical = vec![read, read];

        assert_eq!(
            retain_physical_traffic_events(ordered.clone(), &physical),
            Some(ordered.clone()),
            "both duplicate anchors must survive in their original Serve order"
        );
        for removed in 0..physical.len() {
            let mut missing = physical.clone();
            missing.remove(removed);
            assert!(
                retain_physical_traffic_events(ordered.clone(), &missing).is_none(),
                "removing physical duplicate occurrence {removed} must fail closed"
            );
        }
        let mut extra = physical;
        extra.push(read);
        assert!(
            retain_physical_traffic_events(ordered, &extra).is_none(),
            "an extra physical duplicate occurrence must fail closed"
        );
    }
}
