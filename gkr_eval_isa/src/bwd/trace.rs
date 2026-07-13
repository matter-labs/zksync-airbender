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

use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::{Expr, ExprId, SourceKind};

use crate::fwd::isa::{DstLine, Instr, OperandField, OperandLine, Program};

use super::distill::DistilledLayer;

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
pub fn plan_epoch(d: &DistilledLayer, budget: usize, stream_reductions: bool) -> u64 {
    let mut h = FNV_OFFSET;
    fnv_u32(&mut h, BWD_PLAN_ABI_VERSION);
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
