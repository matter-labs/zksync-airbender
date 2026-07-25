//! Physical cell placement for a fixed coefficient paging plan (design §7.3),
//! the §8 value-use contract it emits, and the §12.2 cell-liveness certificate.
//!
//! Paging ([`super::schedule`]) already fixed admission, bypass, retention and
//! eviction. §7.3: "Placement may not change those decisions." This module
//! therefore only turns a [`PagingPlan`] into physical BF-lane numbers plus the
//! instruction stream that reads and writes them, and it is gated by byte equality
//! of [`PagingPlan::canonical_bytes`] across the call.
//!
//! # The cell file
//!
//! `4 * cell_budget` BF lanes. A BF projection occupies one lane; an E4 projection
//! occupies four consecutive four-lane-aligned lanes. Placement is Ext-first:
//!
//!   1. colour E4 lifetimes into four-lane-aligned quads;
//!   2. pack BF lifetimes into the remaining lane-time holes; and
//!   3. return a move-free placement when that succeeds.
//!
//! Both passes are [`crate::interval_pack::assign_lanes`] — the same offline
//! packer the forward Stage-3 allocator uses, which is why it was made generic
//! over the value id. Only when the offline packing fails *while the peak
//! weighted occupancy still fits* does a deterministic event-scan repair run and
//! emit [`ScheduledInstr::MoveBF`]. §7.3: "The two-pass strategy remains primary
//! so moves stay pathological."
//!
//! # The read/write coordinate space
//!
//! A paging step is one physical source resolution: it may READ a resident cell
//! and then WRITE a fill. Those two halves must not be modelled as one instant,
//! or a fill could never reuse the lanes of the very endpoint it just consumed
//! into a register — which §8's delta resolution ("obtain `s0` from source or
//! resident `Endpoint0`; `ds = s1 - s0`") does all the time.
//!
//! So every plan step `s` occupies TWO interval positions:
//!
//! ```text
//! 2*s      read phase   — a resident cell this step reads is still live here
//! 2*s + 1  write phase  — a fill this step retains starts living here
//! ```
//!
//! A residence therefore spans `[2 * fill_step + 1, end]` where `end` is the
//! largest of `2 * s` over the steps that read its cell and `2 * s + 1` over the
//! steps it survives. A value read and dropped at step `s` ends at `2*s` and a
//! fill at step `s` starts at `2*s + 1`, so they do not overlap — exactly the
//! read-before-write the resolution performs. A value that survives step `s` ends
//! at `2*s + 1` or later and so does conflict with that step's fill, which is also
//! exactly right.
//!
//! A useful consequence: at an odd position the live set is exactly
//! `resident_after[s]` and at an even position it is a subset of
//! `resident_after[s-1]`, both of which the pager already held to `4 *
//! cell_budget`. Peak weighted occupancy therefore never exceeds the budget for a
//! plan the pager produced — [`PlacementFloor::PeakOccupancy`] is reachable only
//! from a hand-built plan that violates the capacity rule.
//!
//! # What is deliberately NOT here
//!
//! Source-window binding, column numbers and the `first_access` bit (Task 6), and
//! the u16 encoding (Task 7). A [`ValueUse`] names a [`SourceId`] /
//! [`ProjectionId`], never a window/column pair.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use cs::gkr_compiler::dag_ir::BwdRegime;

use super::model::{
    CoeffLayer, CoefficientRecipeId, Projection, ProjectionId, SourceId, TermId,
};
use super::schedule::{
    LANES_PER_CELL, PagingAction, PagingPlan, PagingRequest, ProjectionOutcome, ResolutionGroup,
    ScheduleError, SlotKind, SourcePrice, ValueWidth, term_slots, validate_prices,
};
use crate::interval_pack::{self, Interval, PackFailure, PackWidth};

// ── The value-use contract (§8, §9.4, §9.5) ──────────────────────────────────

/// One `PlannedSource` half-action (§9.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PlanAction {
    /// Resolve this projection from source and retain nothing.
    Direct,
    /// Read this projection from its resident lane.
    UseResident { lane: u16 },
    /// Resolve this projection and retain it at `lane`.
    Fill { lane: u16 },
    /// The wire format's fourth action, for a field the plan does not use. A
    /// coefficient plan always names BOTH halves of the pair — the endpoint is
    /// either read, resolved, or resolved-and-retained — so this variant exists
    /// for encoding fidelity only: placement never emits it and
    /// [`certify_cell_liveness`] rejects it.
    Invalid,
}

impl PlanAction {
    /// The lane this action touches, if any.
    pub fn lane(self) -> Option<u16> {
        match self {
            PlanAction::UseResident { lane } | PlanAction::Fill { lane } => Some(lane),
            PlanAction::Direct | PlanAction::Invalid => None,
        }
    }
}

/// A resident-cell read (§9.4's `Cell` mode).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CellRead {
    /// One projection's physical BF lane.
    Single { projection: ProjectionId, lane: u16 },
    /// The opcode-scoped native-dual packed form (§9.5): `Endpoint0` lane first,
    /// `Delta` lane second, both of `source`.
    Pair { source: SourceId, endpoint0_lane: u16, delta_lane: u16 },
}

/// How one operand slot obtains its value (§8).
///
/// The canonical spelling is mandatory (§9.5): `{Direct, Direct}` is
/// [`ValueUse::Direct`] and never a plan; a single requested-projection fill is
/// [`ValueUse::Fill`] and never a plan; a fully resident dual pair is the packed
/// [`CellRead::Pair`] and never a plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ValueUse {
    /// `DirectSource`: resolve this slot's projections from source and retain
    /// none of them.
    Direct { source: SourceId },
    /// `FillSource`: resolve the slot's single requested projection and retain it
    /// at `dst_lane`. §8: the fill CONSUMES the just-resolved register value; it
    /// never reloads the lane it just wrote.
    Fill { projection: ProjectionId, dst_lane: u16 },
    /// `Cell`: read resident lanes and resolve nothing.
    Cell(CellRead),
    /// `PlannedSource` (§9.5): the `Endpoint0`/`Delta` plan of one source-pair
    /// resolution. Legal only on a `Delta` use or a native dual factor.
    PlannedDelta { source: SourceId, endpoint0: PlanAction, delta: PlanAction },
}

/// One scheduled instruction. §8: "A local move is the only standalone cell-file
/// action."
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScheduledInstr {
    /// One coefficient term. `uses[i]` is the value use of
    /// `term_slots(layer, term)[i]` — i.e. of the DEDUPLICATED operand slot, the
    /// same indexing [`PagingAction::slot`] uses, so a term whose two operands
    /// share one source carries one use.
    Term { term: TermId, coefficient: CoefficientRecipeId, uses: Vec<ValueUse> },
    /// Relocate one BF projection between single lanes.
    MoveBF { projection: ProjectionId, from_lane: u16, to_lane: u16 },
    /// Relocate one E4 projection between four-lane-aligned quads.
    MoveE4 { projection: ProjectionId, from_lane: u16, to_lane: u16 },
}

// ── Output ───────────────────────────────────────────────────────────────────

/// One contiguous residency of one projection: the `Fill` that created it through
/// the last step at which its lanes are read or it stays resident.
///
/// A projection evicted and later re-filled has two residences, which is what lets
/// placement give it two different lanes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Residence {
    pub projection: ProjectionId,
    pub width: ValueWidth,
    /// The plan step whose `Fill` created it.
    pub fill_step: u32,
    /// Live interval in the doubled read/write coordinate space (module doc).
    pub span: Interval,
}

/// Static shape of one placed program.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PlacementStats {
    pub terms: usize,
    pub residences: usize,
    pub cell_reads: usize,
    pub fills: usize,
    pub bf_moves: usize,
    pub e4_moves: usize,
    /// Peak weighted occupancy, in BF-lane-equivalents.
    pub peak_lanes: u32,
    /// Highest occupied lane plus one.
    pub lanes_used: u32,
    /// `true` when the offline two-pass failed and the event-scan repair ran.
    pub repaired: bool,
}

/// A complete physical placement of one paging plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoeffPlacement {
    pub regime: BwdRegime,
    pub request: PagingRequest,
    /// Instruction stream in execution order: the moves a term needs precede that
    /// term's [`ScheduledInstr::Term`].
    pub instrs: Vec<ScheduledInstr>,
    /// Every residence placement derived from the plan, in `fill_step` order, each
    /// with the lane it was FIRST placed at. A repaired residence's later lanes are
    /// in the move stream.
    pub residences: Vec<(Residence, u16)>,
    pub stats: PlacementStats,
}

// ── Errors ───────────────────────────────────────────────────────────────────

/// Why a plan could not be seated at its budget.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlacementFloor {
    /// Peak weighted occupancy exceeds the budget, so no placement of any kind —
    /// with or without moves — can fit. Unreachable for a plan
    /// [`super::schedule::page_projections`] produced (module doc).
    PeakOccupancy { peak: u32 },
    /// Offline packing failed and no legal relocation exists at this step.
    NoLegalRelocation { step: u32, projection: ProjectionId },
}

/// Everything placement can reject. Every variant is derivable from its inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlacementError {
    /// §7.3 cannot seat this plan at this budget.
    BudgetBelowFloor { floor: u32, capacity: u32, reason: PlacementFloor },
    /// The plan declares a `Hit` on, or reads the resident `Endpoint0` of, a
    /// projection that holds no lane.
    ReadOfNonResident { step: u32, projection: ProjectionId },
    /// The plan declares a `Fill` of a projection that is already resident, or
    /// `resident_after` names a projection no `Fill` created.
    ResidencyContradiction { step: u32, projection: ProjectionId },
    /// The plan was built for a different regime than the layer it is placed
    /// against — the two describe different programs.
    RegimeMismatch { declared: BwdRegime, found: BwdRegime },
    /// The plan's action stream is not the structural expansion of its order.
    Structure(ScheduleError),
}

impl From<ScheduleError> for PlacementError {
    fn from(e: ScheduleError) -> Self {
        PlacementError::Structure(e)
    }
}

// ── Derivation: the plan's residences and per-step cell traffic ──────────────

/// Everything placement reads out of a [`PagingPlan`], and nothing it decides.
struct Derived {
    residences: Vec<Residence>,
    /// Per step: `(projection, residence index)` read from a cell, in canonical
    /// order (`Endpoint0` before `Delta`).
    reads: Vec<Vec<(ProjectionId, usize)>>,
    /// Per step: `(projection, residence index)` filled.
    fills: Vec<Vec<(ProjectionId, usize)>>,
    /// Per step, the term position the step belongs to.
    position: Vec<u32>,
    /// Per term position, every projection any of its steps reads from a cell.
    reads_by_position: Vec<BTreeSet<ProjectionId>>,
    /// Per term position, the half-open step range it owns.
    steps_of_position: Vec<(usize, usize)>,
}

fn width_of(prices: &[SourcePrice], p: ProjectionId) -> ValueWidth {
    prices[p.source.0 as usize].width
}

fn pack_width(width: ValueWidth) -> PackWidth {
    match width {
        ValueWidth::Bf => PackWidth::Single,
        ValueWidth::E4 => PackWidth::Quad,
    }
}

/// The projections whose CELLS one step reads, in canonical order.
///
/// Two sources, both read straight off the declared plan:
///
///   * every projection the step declares a `Hit` on; and
///   * the resident `Endpoint0` a `Single(Delta)` MISS consumes as `s0` — §8's
///     "obtain `s0` from source or resident `Endpoint0`". The pager charges one
///     endpoint read instead of two for exactly this case, so the read is a
///     decision already taken; placement only has to notice it.
fn step_cell_reads(
    action: &PagingAction,
    resident_before: &BTreeSet<ProjectionId>,
) -> BTreeSet<ProjectionId> {
    let mut out: BTreeSet<ProjectionId> = BTreeSet::new();
    for pa in &action.projections {
        if pa.outcome == ProjectionOutcome::Hit {
            out.insert(pa.projection);
        }
    }
    if let ResolutionGroup::Single(p) = action.group {
        let e0 = ProjectionId::endpoint0(p.source);
        if p.projection == Projection::Delta
            && !resident_before.contains(&p)
            && resident_before.contains(&e0)
        {
            out.insert(e0);
        }
    }
    out
}

fn derive(layer: &CoeffLayer, prices: &[SourcePrice], plan: &PagingPlan) -> Result<Derived, PlacementError> {
    let n = plan.actions.len();
    let mut d = Derived {
        residences: Vec::new(),
        reads: Vec::with_capacity(n),
        fills: Vec::with_capacity(n),
        position: Vec::with_capacity(n),
        reads_by_position: vec![BTreeSet::new(); plan.order.len()],
        steps_of_position: vec![(0, 0); plan.order.len()],
    };
    // Reject an action stream that is not the layer's structural expansion before
    // reading anything else out of it.
    for &id in &plan.order {
        let term = layer
            .terms
            .get(id.0 as usize)
            .ok_or(ScheduleError::UnknownTerm { term: id })?;
        term_slots(layer, term)?;
    }

    let mut open: HashMap<ProjectionId, usize> = HashMap::new();
    let mut resident_before: BTreeSet<ProjectionId> = BTreeSet::new();

    for (step, action) in plan.actions.iter().enumerate() {
        let s = step as u32;
        let position = action.position as usize;
        if position >= d.reads_by_position.len() {
            return Err(ScheduleError::UnknownTerm { term: action.term }.into());
        }
        d.position.push(action.position);

        let read_set = step_cell_reads(action, &resident_before);
        let mut step_reads = Vec::with_capacity(read_set.len());
        for p in read_set {
            let index = *open
                .get(&p)
                .ok_or(PlacementError::ReadOfNonResident { step: s, projection: p })?;
            let end = 2 * step;
            d.residences[index].span.last_use = d.residences[index].span.last_use.max(end);
            d.reads_by_position[position].insert(p);
            step_reads.push((p, index));
        }

        let mut step_fills = Vec::new();
        for pa in &action.projections {
            if pa.outcome != ProjectionOutcome::Fill {
                continue;
            }
            if open.contains_key(&pa.projection) {
                return Err(PlacementError::ResidencyContradiction {
                    step: s,
                    projection: pa.projection,
                });
            }
            let index = d.residences.len();
            let start = 2 * step + 1;
            d.residences.push(Residence {
                projection: pa.projection,
                width: width_of(prices, pa.projection),
                fill_step: s,
                span: Interval { def: start, last_use: start },
            });
            open.insert(pa.projection, index);
            step_fills.push((pa.projection, index));
        }

        // Everything the plan says is resident after this step holds its lanes
        // through the write phase.
        for p in &action.resident_after {
            let index = *open
                .get(p)
                .ok_or(PlacementError::ResidencyContradiction { step: s, projection: *p })?;
            let end = 2 * step + 1;
            d.residences[index].span.last_use = d.residences[index].span.last_use.max(end);
        }

        let after: BTreeSet<ProjectionId> = action.resident_after.iter().copied().collect();
        open.retain(|p, _| after.contains(p));
        resident_before = after;
        d.reads.push(step_reads);
        d.fills.push(step_fills);
    }

    // Term positions own contiguous step ranges (the pager expands term by term).
    let mut cursor = 0usize;
    for position in 0..d.steps_of_position.len() {
        let start = cursor;
        while cursor < d.position.len() && d.position[cursor] as usize == position {
            cursor += 1;
        }
        d.steps_of_position[position] = (start, cursor);
    }
    if cursor != d.position.len() {
        return Err(ScheduleError::OrderNotAPermutation {
            terms: layer.terms.len(),
            order: plan.order.len(),
        }
        .into());
    }
    Ok(d)
}

// ── Lane assignment ──────────────────────────────────────────────────────────

/// One emitted relocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MoveRecord {
    /// The step whose fill forced it. Emitted before that step's term.
    step: u32,
    projection: ProjectionId,
    width: ValueWidth,
    from_lane: u16,
    to_lane: u16,
}

/// The physical answer: a lane for every read and every fill, plus the moves.
struct LanePlan {
    /// Parallel to [`Derived::reads`].
    read_lanes: Vec<Vec<u16>>,
    /// Parallel to [`Derived::fills`].
    fill_lanes: Vec<Vec<u16>>,
    moves: Vec<MoveRecord>,
    /// Lane each residence was FIRST placed at, by residence index.
    first_lane: Vec<u16>,
    repaired: bool,
}

/// Offline two-pass: colour E4 lifetimes into quads, pack BF lifetimes into the
/// remaining lane-time holes. Every residence keeps one lane for its whole span,
/// so the placement is move-free by construction.
fn two_pass(d: &Derived, capacity: usize) -> Result<LanePlan, PackFailure> {
    let ranges: HashMap<usize, Interval> =
        d.residences.iter().enumerate().map(|(i, r)| (i, r.span)).collect();
    let lane_of =
        interval_pack::assign_lanes(&ranges, |i| pack_width(d.residences[i].width), capacity)?;

    let first_lane: Vec<u16> = (0..d.residences.len()).map(|i| lane_of[&i]).collect();
    let read_lanes = d
        .reads
        .iter()
        .map(|step| step.iter().map(|(_, i)| first_lane[*i]).collect())
        .collect();
    let fill_lanes = d
        .fills
        .iter()
        .map(|step| step.iter().map(|(_, i)| first_lane[*i]).collect())
        .collect();
    Ok(LanePlan { read_lanes, fill_lanes, moves: Vec::new(), first_lane, repaired: false })
}

/// One candidate quad clearance, ranked lexicographically by the brief's exact
/// key: fewest moves, then lowest destination lanes, then lowest source lanes,
/// then `ProjectionId`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct RepairCandidate {
    moves: usize,
    destinations: Vec<u16>,
    sources: Vec<u16>,
    projections: Vec<ProjectionId>,
    /// Not part of the ranking — the quad this key belongs to. Placed last so it
    /// cannot influence the derived `Ord` before the four ranked keys have decided,
    /// and a quad is uniquely determined by its occupant source lanes anyway.
    quad: usize,
}

/// Deterministic event-scan repair (design §7.3's "insert `MoveBF` or vectorized
/// `MoveE4` only for real lifetime fragmentation").
///
/// Runs ONLY when [`two_pass`] failed while the peak weighted occupancy still
/// fits. Processes steps in plan order, expiring dead occupants before every fill,
/// and for an incoming E4 with no free quad chooses the lexically first candidate
/// quad whose live BF occupants can be relocated into currently free singleton
/// lanes.
///
/// Two hard rules, both checked BEFORE candidate selection rather than as an
/// after-the-fact exclusion:
///
///   * a value that is an input of the CURRENT term is never moved; and
///   * a move destination is never a lane the current term reads, because the
///     moves are emitted before that term's instruction and would clobber the
///     read.
fn event_scan_repair(
    d: &Derived,
    capacity: usize,
) -> Result<LanePlan, PlacementError> {
    let n_quads = capacity / LANES_PER_CELL as usize;
    // Lane -> residence index currently holding it.
    let mut owner: Vec<Option<usize>> = vec![None; capacity];
    // Residence index -> its current base lane.
    let mut lane_of: Vec<Option<u16>> = vec![None; d.residences.len()];
    let mut first_lane: Vec<u16> = vec![0; d.residences.len()];
    let mut moves: Vec<MoveRecord> = Vec::new();
    let mut read_lanes: Vec<Vec<u16>> = Vec::with_capacity(d.reads.len());
    let mut fill_lanes: Vec<Vec<u16>> = Vec::with_capacity(d.fills.len());

    let occupies = |owner: &[Option<usize>], lane: u16, width: ValueWidth| -> Vec<usize> {
        let base = lane as usize;
        (base..base + width.lanes() as usize).filter_map(|l| owner[l]).collect()
    };
    let claim = |owner: &mut Vec<Option<usize>>, lane: u16, width: ValueWidth, index: usize| {
        let base = lane as usize;
        for l in base..base + width.lanes() as usize {
            owner[l] = Some(index);
        }
    };
    let release = |owner: &mut Vec<Option<usize>>, lane: u16, width: ValueWidth| {
        let base = lane as usize;
        for l in base..base + width.lanes() as usize {
            owner[l] = None;
        }
    };

    // Lanes the CURRENT term has already read. A move is emitted before its term's
    // instruction, so it must not write one of these even after the value died —
    // the term's `Cell` read happens after the move on the device.
    let mut term_read_lanes: BTreeSet<u16> = BTreeSet::new();
    // Lanes an EARLIER operand slot of the current term has already filled. A move
    // is emitted before its term, so writing one of these would be undone the
    // instant that fill executes.
    let mut term_filled_lanes: BTreeSet<u16> = BTreeSet::new();
    let mut current_position: Option<usize> = None;
    let mut term_first_step = 0u32;

    for step in 0..d.reads.len() {
        let position = d.position[step] as usize;
        if current_position != Some(position) {
            term_read_lanes.clear();
            term_filled_lanes.clear();
            current_position = Some(position);
            term_first_step = step as u32;
        }
        let term_reads = &d.reads_by_position[position];

        // Reads first: their lanes were fixed when the residence was placed, and a
        // relocated residence reads its CURRENT lane.
        let step_read_lanes: Vec<u16> =
            d.reads[step].iter().map(|(_, i)| lane_of[*i].expect("placed")).collect();
        for (slot, &(_, index)) in d.reads[step].iter().enumerate() {
            let base = step_read_lanes[slot];
            for l in base..base + d.residences[index].width.lanes() as u16 {
                term_read_lanes.insert(l);
            }
        }
        read_lanes.push(step_read_lanes);

        // Expire before every fill: a residence whose span ends at or before this
        // step's read phase has already been consumed into a register, so its lanes
        // are available to this step's own fill (module doc).
        for index in 0..d.residences.len() {
            if let Some(lane) = lane_of[index] {
                if d.residences[index].span.last_use <= 2 * step {
                    release(&mut owner, lane, d.residences[index].width);
                    lane_of[index] = None;
                }
            }
        }

        let mut step_fill_lanes = Vec::new();
        for &(projection, index) in &d.fills[step] {
            let width = d.residences[index].width;
            let lane = match width {
                ValueWidth::Bf => (0..capacity)
                    .find(|&l| owner[l].is_none())
                    .map(|l| l as u16)
                    .ok_or(PlacementError::BudgetBelowFloor {
                        floor: capacity as u32 + 1,
                        capacity: capacity as u32,
                        reason: PlacementFloor::NoLegalRelocation {
                            step: step as u32,
                            projection,
                        },
                    })?,
                ValueWidth::E4 => {
                    match (0..n_quads).find(|&q| {
                        (q * 4..q * 4 + 4).all(|l| owner[l].is_none())
                    }) {
                        Some(q) => (q * 4) as u16,
                        None => {
                            // No free quad: relocate the live BF occupants of one.
                            let candidate = best_repair_candidate(
                                d,
                                &owner,
                                &lane_of,
                                term_reads,
                                &term_read_lanes,
                                &term_filled_lanes,
                                term_first_step,
                                n_quads,
                                capacity,
                            )
                            .ok_or(PlacementError::BudgetBelowFloor {
                                floor: capacity as u32 + 1,
                                capacity: capacity as u32,
                                reason: PlacementFloor::NoLegalRelocation {
                                    step: step as u32,
                                    projection,
                                },
                            })?;
                            for (slot, &occupant) in candidate.occupants.iter().enumerate() {
                                let from = lane_of[occupant].expect("live occupant");
                                let to = candidate.destinations[slot];
                                release(&mut owner, from, ValueWidth::Bf);
                                claim(&mut owner, to, ValueWidth::Bf, occupant);
                                lane_of[occupant] = Some(to);
                                moves.push(MoveRecord {
                                    step: step as u32,
                                    projection: d.residences[occupant].projection,
                                    width: ValueWidth::Bf,
                                    from_lane: from,
                                    to_lane: to,
                                });
                            }
                            // Every LIVE occupant was just relocated and every
                            // dead one was already released by this step's expiry,
                            // so the quad is now empty with no extra clearing.
                            let base = candidate.key.quad * 4;
                            debug_assert!(
                                (base..base + 4).all(|l| owner[l].is_none()),
                                "a cleared quad must hold no live occupant"
                            );
                            base as u16
                        }
                    }
                }
            };
            debug_assert!(occupies(&owner, lane, width).is_empty(), "fill into a live range");
            claim(&mut owner, lane, width, index);
            lane_of[index] = Some(lane);
            first_lane[index] = lane;
            for l in lane..lane + width.lanes() as u16 {
                term_filled_lanes.insert(l);
            }
            step_fill_lanes.push(lane);
        }
        fill_lanes.push(step_fill_lanes);
    }

    Ok(LanePlan { read_lanes, fill_lanes, moves, first_lane, repaired: true })
}

/// The chosen clearance: which residences move, and where.
struct Clearance {
    key: RepairCandidate,
    occupants: Vec<usize>,
    destinations: Vec<u16>,
}

/// Enumerate every legal quad clearance and return the lexically first by
/// `(fewest moves, lowest destination lanes, lowest source lanes, ProjectionId)`.
///
/// A quad is a candidate only when EVERY live occupant is a BF projection that
/// the current term neither reads nor produced, and enough free destination lanes
/// exist outside the quad that the current term does not read.
///
/// "nor produced" is not a refinement of "never move a current-term input" — it is
/// a second, independent rule with the same cause. A move is a STANDALONE
/// instruction emitted before its term, so at the moment it executes a value an
/// earlier operand slot of that same term will fill does not exist yet. Relocating
/// it would read an undefined range and leave the later fill writing the vacated
/// lane. `fill_step >= term_first_step` is exactly that set.
#[allow(clippy::too_many_arguments)]
fn best_repair_candidate(
    d: &Derived,
    owner: &[Option<usize>],
    lane_of: &[Option<u16>],
    term_reads: &BTreeSet<ProjectionId>,
    term_read_lanes: &BTreeSet<u16>,
    term_filled_lanes: &BTreeSet<u16>,
    term_first_step: u32,
    n_quads: usize,
    capacity: usize,
) -> Option<Clearance> {
    // A lane a move may write: unowned now, not read by this term, and not already
    // filled by an earlier operand slot of this term. All three are checked HERE,
    // before candidate selection, rather than as an after-the-fact exclusion —
    // the move executes before the term, so anything the term reads or has already
    // written is off limits.
    let writable: Vec<u16> = (0..capacity)
        .map(|l| l as u16)
        .filter(|&l| {
            owner[l as usize].is_none()
                && !term_read_lanes.contains(&l)
                && !term_filled_lanes.contains(&l)
        })
        .collect();

    let mut best: Option<Clearance> = None;
    for quad in 0..n_quads {
        let base = quad * 4;
        let mut occupants: Vec<usize> = Vec::new();
        for l in base..base + 4 {
            if let Some(index) = owner[l] {
                if !occupants.contains(&index) {
                    occupants.push(index);
                }
            }
        }
        // Never move a value that is an input of the current term; an E4 occupant
        // would need `MoveE4`, which no case has demanded.
        if occupants.iter().any(|&i| {
            d.residences[i].width != ValueWidth::Bf
                || term_reads.contains(&d.residences[i].projection)
                || d.residences[i].fill_step >= term_first_step
        }) {
            continue;
        }
        // Occupants ascending by source lane, so the key is deterministic.
        occupants.sort_by_key(|&i| lane_of[i].expect("live occupant"));
        let destinations: Vec<u16> =
            writable.iter().copied().filter(|&l| (l as usize) < base || (l as usize) >= base + 4).take(occupants.len()).collect();
        if destinations.len() < occupants.len() {
            continue;
        }
        let key = RepairCandidate {
            moves: occupants.len(),
            destinations: destinations.clone(),
            sources: occupants.iter().map(|&i| lane_of[i].expect("live occupant")).collect(),
            projections: occupants.iter().map(|&i| d.residences[i].projection).collect(),
            quad,
        };
        let better = best.as_ref().is_none_or(|current| key < current.key);
        if better {
            best = Some(Clearance { key, occupants, destinations });
        }
    }
    best
}

// ── Emission ─────────────────────────────────────────────────────────────────

/// The `ValueUse` of one operand slot, from the slot's kind, the plan's declared
/// outcomes, and the lanes placement assigned.
fn value_use(
    kind: SlotKind,
    action: &PagingAction,
    read_lane: &BTreeMap<ProjectionId, u16>,
    fill_lane: &BTreeMap<ProjectionId, u16>,
) -> ValueUse {
    let source = kind.source();
    let e0 = ProjectionId::endpoint0(source);
    let ds = ProjectionId::delta(source);
    let outcome = |p: ProjectionId| {
        action.projections.iter().find(|a| a.projection == p).map(|a| a.outcome)
    };
    let plan_action = |p: ProjectionId| -> PlanAction {
        if let Some(&lane) = read_lane.get(&p) {
            return PlanAction::UseResident { lane };
        }
        if let Some(&lane) = fill_lane.get(&p) {
            return PlanAction::Fill { lane };
        }
        PlanAction::Direct
    };

    match kind {
        SlotKind::Endpoint0Only(p) => {
            if let Some(&lane) = read_lane.get(&p) {
                return ValueUse::Cell(CellRead::Single { projection: p, lane });
            }
            if let Some(&dst_lane) = fill_lane.get(&p) {
                return ValueUse::Fill { projection: p, dst_lane };
            }
            ValueUse::Direct { source }
        }
        SlotKind::DeltaOnly(p) => {
            if let Some(&lane) = read_lane.get(&p) {
                return ValueUse::Cell(CellRead::Single { projection: p, lane });
            }
            let endpoint0 = plan_action(e0);
            let delta = plan_action(p);
            match (endpoint0, delta) {
                // §9.5: `{Direct, Direct}` uses `DirectSource`, not a plan.
                (PlanAction::Direct, PlanAction::Direct) => ValueUse::Direct { source },
                // §9.5: a single requested-projection fill uses `FillSource`.
                (PlanAction::Direct, PlanAction::Fill { lane }) => {
                    ValueUse::Fill { projection: p, dst_lane: lane }
                }
                _ => ValueUse::PlannedDelta { source, endpoint0, delta },
            }
        }
        SlotKind::DualFactor(_) => {
            let e0_hit = outcome(e0) == Some(ProjectionOutcome::Hit);
            let ds_hit = outcome(ds) == Some(ProjectionOutcome::Hit);
            if e0_hit && ds_hit {
                // §9.5: a fully resident dual pair uses the packed `Cell` form.
                return ValueUse::Cell(CellRead::Pair {
                    source,
                    endpoint0_lane: read_lane[&e0],
                    delta_lane: read_lane[&ds],
                });
            }
            let endpoint0 = plan_action(e0);
            let delta = plan_action(ds);
            if endpoint0 == PlanAction::Direct && delta == PlanAction::Direct {
                return ValueUse::Direct { source };
            }
            ValueUse::PlannedDelta { source, endpoint0, delta }
        }
    }
}

fn emit(
    layer: &CoeffLayer,
    plan: &PagingPlan,
    d: &Derived,
    lanes: &LanePlan,
) -> Result<Vec<ScheduledInstr>, PlacementError> {
    let mut out: Vec<ScheduledInstr> = Vec::with_capacity(plan.order.len() + lanes.moves.len());
    let mut move_cursor = 0usize;
    for (position, &id) in plan.order.iter().enumerate() {
        let (first, last) = d.steps_of_position[position];
        let term = layer
            .terms
            .get(id.0 as usize)
            .ok_or(ScheduleError::UnknownTerm { term: id })?;
        let slots = term_slots(layer, term)?;

        // Every move any step of this term forced is emitted BEFORE the term, so it
        // cannot clobber a lane the term reads.
        while move_cursor < lanes.moves.len() && (lanes.moves[move_cursor].step as usize) < last {
            let m = lanes.moves[move_cursor];
            out.push(match m.width {
                ValueWidth::Bf => ScheduledInstr::MoveBF {
                    projection: m.projection,
                    from_lane: m.from_lane,
                    to_lane: m.to_lane,
                },
                ValueWidth::E4 => ScheduledInstr::MoveE4 {
                    projection: m.projection,
                    from_lane: m.from_lane,
                    to_lane: m.to_lane,
                },
            });
            move_cursor += 1;
        }

        let mut uses = Vec::with_capacity(slots.len());
        for step in first..last {
            let action = &plan.actions[step];
            let kind = *slots
                .get(action.slot as usize)
                .ok_or(ScheduleError::UnknownTerm { term: id })?;
            let read_lane: BTreeMap<ProjectionId, u16> = d.reads[step]
                .iter()
                .map(|(p, _)| *p)
                .zip(lanes.read_lanes[step].iter().copied())
                .collect();
            let fill_lane: BTreeMap<ProjectionId, u16> = d.fills[step]
                .iter()
                .map(|(p, _)| *p)
                .zip(lanes.fill_lanes[step].iter().copied())
                .collect();
            uses.push(value_use(kind, action, &read_lane, &fill_lane));
        }
        if uses.len() != slots.len() {
            return Err(ScheduleError::OrderNotAPermutation {
                terms: layer.terms.len(),
                order: plan.order.len(),
            }
            .into());
        }
        out.push(ScheduledInstr::Term { term: id, coefficient: term.coefficient(), uses });
    }
    Ok(out)
}

// ── Entry point ──────────────────────────────────────────────────────────────

/// Place one fixed paging plan into physical BF lanes and emit its instruction
/// stream (§7.3, §8).
///
/// The plan is READ ONLY. Callers gate that with byte equality of
/// [`PagingPlan::canonical_bytes`] across this call, which is the only mechanism
/// that actually proves a decision was not changed — re-certifying the plan would
/// accept a consistently-rewritten but DIFFERENT legal plan and so proves nothing
/// here.
pub fn place_paging_plan(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    plan: &PagingPlan,
) -> Result<CoeffPlacement, PlacementError> {
    validate_prices(layer, prices)?;
    if plan.regime != layer.regime {
        return Err(PlacementError::RegimeMismatch {
            declared: plan.regime,
            found: layer.regime,
        });
    }
    let capacity = plan.request.budget.lanes() as usize;
    let d = derive(layer, prices, plan)?;

    let lanes = match two_pass(&d, capacity) {
        Ok(lanes) => lanes,
        Err(PackFailure::PeakExceedsBudget { peak }) => {
            return Err(PlacementError::BudgetBelowFloor {
                floor: peak as u32,
                capacity: capacity as u32,
                reason: PlacementFloor::PeakOccupancy { peak: peak as u32 },
            });
        }
        // Offline packing failed while the peak still fits: this is the
        // pathological fragmentation §7.3 keeps moves for.
        //
        // One arm, not two: `QuadDemandExceedsBudget` cannot fire here. It means
        // the concurrent E4 count exceeds the quad budget, but the peak check
        // above already established `4 * concurrent_e4 <= peak <= 4 * n_quads`.
        // It is handled identically rather than split out so a future change to
        // the peak check cannot turn it into a silent panic.
        Err(_) => event_scan_repair(&d, capacity)?,
    };

    let instrs = emit(layer, plan, &d, &lanes)?;
    let ranges: HashMap<usize, Interval> =
        d.residences.iter().enumerate().map(|(i, r)| (i, r.span)).collect();
    let peak_lanes =
        interval_pack::peak_weighted_demand(&ranges, |i| pack_width(d.residences[i].width)) as u32;
    let mut lanes_used = 0u32;
    for (index, residence) in d.residences.iter().enumerate() {
        let end = u32::from(lanes.first_lane[index]) + residence.width.lanes();
        lanes_used = lanes_used.max(end);
    }
    for m in &lanes.moves {
        lanes_used = lanes_used.max(u32::from(m.to_lane) + m.width.lanes());
    }

    let stats = PlacementStats {
        terms: plan.order.len(),
        residences: d.residences.len(),
        cell_reads: d.reads.iter().map(Vec::len).sum(),
        fills: d.fills.iter().map(Vec::len).sum(),
        bf_moves: lanes.moves.iter().filter(|m| m.width == ValueWidth::Bf).count(),
        e4_moves: lanes.moves.iter().filter(|m| m.width == ValueWidth::E4).count(),
        peak_lanes,
        lanes_used,
        repaired: lanes.repaired,
    };
    let residences =
        d.residences.iter().copied().zip(lanes.first_lane.iter().copied()).collect();
    Ok(CoeffPlacement {
        regime: plan.regime,
        request: plan.request,
        instrs,
        residences,
        stats,
    })
}

// ── The cell-liveness certificate (§12.2) ────────────────────────────────────

/// What the liveness replay observed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LivenessReport {
    pub terms: usize,
    pub cell_reads: usize,
    pub fills: usize,
    pub bf_moves: usize,
    pub e4_moves: usize,
    /// Peak lanes owned by a projection the plan says is resident.
    pub peak_owned_lanes: u32,
    /// Highest lane ever written, plus one.
    pub lanes_used: u32,
}

/// Everything the liveness certificate can reject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LivenessError {
    /// The placement header disagrees with the plan it claims to place.
    HeaderMismatch,
    /// The instruction stream ran out of terms, or has trailing instructions.
    InstructionCountMismatch { expected_terms: usize, found_terms: usize },
    TermMismatch { position: usize, expected: TermId, found: TermId },
    CoefficientMismatch { term: TermId, expected: CoefficientRecipeId, found: CoefficientRecipeId },
    UseCountMismatch { term: TermId, expected: usize, found: usize },
    /// The plan step stream and the emitted term stream disagree.
    StepMismatch { step: usize, term: TermId, slot: u8 },
    /// A lane index, or a lane span, falls outside `4 * cell_budget`.
    LaneOutOfBounds { step: usize, lane: u16, lanes: u32 },
    /// An E4 lane is not four-lane-aligned (§12.1).
    ExtLaneMisaligned { step: usize, lane: u16 },
    /// A `Cell` use reads a lane whose current definition is not the intended
    /// projection — a stale read.
    StaleCellRead { step: usize, projection: ProjectionId, lane: u16, found: Option<ProjectionId> },
    /// A fill writes a lane a projection the plan still says is resident owns.
    FillClobbersLiveValue { step: usize, projection: ProjectionId, lane: u16, victim: ProjectionId },
    /// A fill writes a lane another input of the SAME term reads at a later slot
    /// (§12.2: "no term-side fill clobbers another input needed by that term").
    FillClobbersTermInput { step: usize, projection: ProjectionId, lane: u16, victim: ProjectionId },
    /// The emitted use is not a legal — or not the canonical — form for this slot
    /// and this set of declared outcomes.
    IllegalUseForm { step: usize, term: TermId, slot: u8 },
    /// A move relocates a value the current term reads.
    MoveOfCurrentTermInput { index: usize, projection: ProjectionId },
    /// A move reads a range its projection does not currently own.
    MoveSourceNotLive { index: usize, projection: ProjectionId, from_lane: u16 },
    /// A move writes a range that is neither dead nor free, or one the current term
    /// reads.
    MoveDestinationNotDead { index: usize, projection: ProjectionId, to_lane: u16 },
    /// A move's declared width is not the projection's width.
    MoveWidthMismatch { index: usize, projection: ProjectionId, declared: ValueWidth },
    /// A projection the plan declares resident owns no lanes, or the wrong number.
    ResidentWithoutLanes { step: usize, projection: ProjectionId },
    /// The lanes owned by the plan's resident set do not total
    /// `resident_lanes_after`.
    ResidentLanesMismatch { step: usize, declared: u32, owned: u32 },
    /// `PlanAction::Invalid` appeared in an emitted plan.
    InvalidPlanAction { step: usize, term: TermId, slot: u8 },
    /// The plan's structure is itself rejected by the shared structural expansion.
    Structure(ScheduleError),
}

impl From<ScheduleError> for LivenessError {
    fn from(e: ScheduleError) -> Self {
        LivenessError::Structure(e)
    }
}

/// Replay the emitted instruction stream and prove §12.2.
///
/// # Independence
///
/// This function shares NO placement code. It never calls [`derive`],
/// [`two_pass`], [`event_scan_repair`], [`value_use`] or [`emit`], and it does not
/// recompute a single residence. What it shares is three things that are not
/// placement decisions:
///
///   * [`term_slots`] — the STRUCTURAL operand-slot expansion of the layer, a
///     function of [`CoeffLayer`] alone (the paging certificate shares the same
///     expansion for the same reason);
///   * the caller's price table, which is an INPUT to both; and
///   * the [`PagingPlan`], which is the thing placement is being checked AGAINST,
///     not a shared derivation.
///
/// Everything else it maintains itself: its own lane→projection ownership map,
/// built strictly from the emitted `Fill`/`Move` writes, and its own residency,
/// which it re-synchronises to `resident_after` after every step. It proves:
///
///   * every `Cell` read resolves to the intended live [`ProjectionId`], and the
///     latest fill or move is its valid definition;
///   * a paired plan accounts for both possible writes;
///   * BF and E4 live ranges never overlap (a fill onto a live owner is rejected);
///   * no term-side fill clobbers another input needed by that term;
///   * moves read live sources, write only dead/free ranges, and never relocate or
///     overwrite an input of the term they precede;
///   * E4 lanes are four-lane-aligned and in bounds; and
///   * after every step the lanes owned by the plan's resident set are exactly
///     that set, at exactly `resident_lanes_after` lanes — which is how "placement
///     preserves the pager's admission and eviction decisions" is discharged.
pub fn certify_cell_liveness(
    layer: &CoeffLayer,
    prices: &[SourcePrice],
    plan: &PagingPlan,
    placement: &CoeffPlacement,
) -> Result<LivenessReport, LivenessError> {
    validate_prices(layer, prices)?;
    if placement.regime != plan.regime || placement.request != plan.request {
        return Err(LivenessError::HeaderMismatch);
    }
    let lanes = plan.request.budget.lanes();
    let capacity = lanes as usize;

    let mut owner: Vec<Option<ProjectionId>> = vec![None; capacity];
    let mut held: BTreeMap<ProjectionId, u16> = BTreeMap::new();
    let mut report = LivenessReport::default();

    let term_count =
        placement.instrs.iter().filter(|i| matches!(i, ScheduledInstr::Term { .. })).count();
    if term_count != plan.order.len() {
        return Err(LivenessError::InstructionCountMismatch {
            expected_terms: plan.order.len(),
            found_terms: term_count,
        });
    }

    let mut cursor = 0usize;
    let mut step = 0usize;
    for (position, &id) in plan.order.iter().enumerate() {
        let term = layer.terms.get(id.0 as usize).ok_or(ScheduleError::UnknownTerm { term: id })?;
        let slots = term_slots(layer, term)?;

        // Peek the term instruction so the move guard knows what this term reads.
        let mut at = cursor;
        while at < placement.instrs.len()
            && !matches!(placement.instrs[at], ScheduledInstr::Term { .. })
        {
            at += 1;
        }
        let ScheduledInstr::Term { term: emitted, coefficient, uses } =
            placement.instrs.get(at).ok_or(LivenessError::InstructionCountMismatch {
                expected_terms: plan.order.len(),
                found_terms: term_count,
            })?
        else {
            unreachable!("the scan above stops on a Term");
        };
        if *emitted != id {
            return Err(LivenessError::TermMismatch { position, expected: id, found: *emitted });
        }
        if *coefficient != term.coefficient() {
            return Err(LivenessError::CoefficientMismatch {
                term: id,
                expected: term.coefficient(),
                found: *coefficient,
            });
        }
        if uses.len() != slots.len() {
            return Err(LivenessError::UseCountMismatch {
                term: id,
                expected: slots.len(),
                found: uses.len(),
            });
        }

        // Lanes and projections this term reads from cells, over ALL its slots.
        let mut term_read_lanes: BTreeSet<u16> = BTreeSet::new();
        let mut term_read_projections: BTreeSet<ProjectionId> = BTreeSet::new();
        // Per slot, the lanes that slot reads — needed to reject a fill that
        // clobbers a LATER slot's input.
        let mut slot_read_lanes: Vec<BTreeSet<u16>> = Vec::with_capacity(uses.len());
        for u in uses {
            let mut here: BTreeSet<u16> = BTreeSet::new();
            let mut note = |p: ProjectionId, lane: u16| {
                let w = width_of(prices, p).lanes() as u16;
                for l in lane..lane.saturating_add(w) {
                    here.insert(l);
                    term_read_lanes.insert(l);
                }
                term_read_projections.insert(p);
            };
            match u {
                ValueUse::Cell(CellRead::Single { projection, lane }) => note(*projection, *lane),
                ValueUse::Cell(CellRead::Pair { source, endpoint0_lane, delta_lane }) => {
                    note(ProjectionId::endpoint0(*source), *endpoint0_lane);
                    note(ProjectionId::delta(*source), *delta_lane);
                }
                ValueUse::PlannedDelta { source, endpoint0, delta } => {
                    if let PlanAction::UseResident { lane } = endpoint0 {
                        note(ProjectionId::endpoint0(*source), *lane);
                    }
                    if let PlanAction::UseResident { lane } = delta {
                        note(ProjectionId::delta(*source), *lane);
                    }
                }
                ValueUse::Direct { .. } | ValueUse::Fill { .. } => {}
            }
            slot_read_lanes.push(here);
        }

        // What the plan says is still resident when this term finishes. A move
        // executes BEFORE the term, so it may overwrite a range whose occupant the
        // plan has already given up on — that occupant is physically still in its
        // lane, but nothing reads it again. It may NOT overwrite anything the plan
        // still holds, nor any lane this term reads.
        // Projections a legal pre-term move reclaimed the lanes of. Proven at move
        // time to be absent from `survivors` and unread by this term, so their
        // residency over the term's remaining slots is plan bookkeeping with no
        // physical copy behind it. Cleared when the term ends, at which point the
        // full "every resident owns its lanes" check applies again.
        let mut retired: BTreeSet<ProjectionId> = BTreeSet::new();
        let last_step = step + slots.len().saturating_sub(1);
        let survivors: BTreeSet<ProjectionId> = plan
            .actions
            .get(last_step)
            .map(|a| a.resident_after.iter().copied().collect())
            .unwrap_or_default();

        // Moves preceding this term.
        for index in cursor..at {
            let (projection, width, from_lane, to_lane) = match &placement.instrs[index] {
                ScheduledInstr::MoveBF { projection, from_lane, to_lane } => {
                    (*projection, ValueWidth::Bf, *from_lane, *to_lane)
                }
                ScheduledInstr::MoveE4 { projection, from_lane, to_lane } => {
                    (*projection, ValueWidth::E4, *from_lane, *to_lane)
                }
                ScheduledInstr::Term { .. } => unreachable!("scan stops on a Term"),
            };
            if width != width_of(prices, projection) {
                return Err(LivenessError::MoveWidthMismatch {
                    index,
                    projection,
                    declared: width,
                });
            }
            let w = width.lanes() as u16;
            if width == ValueWidth::E4 && (from_lane % 4 != 0 || to_lane % 4 != 0) {
                return Err(LivenessError::ExtLaneMisaligned { step, lane: to_lane });
            }
            if u32::from(from_lane) + width.lanes() > lanes
                || u32::from(to_lane) + width.lanes() > lanes
            {
                return Err(LivenessError::LaneOutOfBounds { step, lane: to_lane, lanes });
            }
            if term_read_projections.contains(&projection) {
                return Err(LivenessError::MoveOfCurrentTermInput { index, projection });
            }
            if (from_lane..from_lane + w).any(|l| owner[l as usize] != Some(projection)) {
                return Err(LivenessError::MoveSourceNotLive { index, projection, from_lane });
            }
            // The rule, exactly: a move may not destroy a definition that is still
            // needed. Two conditions cover it, and a THIRD one that looks necessary
            // is not.
            //
            //   * not a lane this term READS — the move executes first, so it would
            //     clobber the read; and
            //   * the occupant must not survive the term.
            //
            // What is deliberately NOT checked here is "a lane some slot of this
            // term FILLS". Rejecting all of them is over-strict, and provably so:
            // a fill at a LATER slot may legitimately reclaim the moved value's
            // lane once the plan has dropped it, and the placer cannot even know a
            // later slot's destination when it picks the move (that lane is chosen
            // afterwards). The one form that IS a hazard — a fill at an EARLIER
            // slot overwriting the relocated value — needs no separate rule: the
            // move only relocates a value live at its own step, residency within a
            // residence is contiguous, so that value is in `resident_after` of
            // every earlier step of the same term, and the fill is rejected by
            // `FillClobbersLiveValue` naming the real violated invariant.
            if (to_lane..to_lane + w).any(|l| {
                term_read_lanes.contains(&l)
                    || owner[l as usize].is_some_and(|victim| survivors.contains(&victim))
            }) {
                return Err(LivenessError::MoveDestinationNotDead { index, projection, to_lane });
            }
            // A range the move abandons stops being anyone's definition — wholly,
            // not just on the lanes the move happens to cover.
            let displaced: BTreeSet<ProjectionId> =
                (to_lane..to_lane + w).filter_map(|l| owner[l as usize]).collect();
            for victim in displaced {
                forget(&mut owner, &mut held, prices, victim);
                retired.insert(victim);
            }
            for l in from_lane..from_lane + w {
                owner[l as usize] = None;
            }
            for l in to_lane..to_lane + w {
                owner[l as usize] = Some(projection);
            }
            held.insert(projection, to_lane);
            match width {
                ValueWidth::Bf => report.bf_moves += 1,
                ValueWidth::E4 => report.e4_moves += 1,
            }
            report.lanes_used = report.lanes_used.max(u32::from(to_lane) + width.lanes());
        }
        cursor = at + 1;

        for (slot, (kind, use_)) in slots.iter().copied().zip(uses).enumerate() {
            let action = plan.actions.get(step).ok_or(LivenessError::StepMismatch {
                step,
                term: id,
                slot: slot as u8,
            })?;
            if action.term != id || action.slot != slot as u8 || action.position as usize != position
            {
                return Err(LivenessError::StepMismatch { step, term: id, slot: slot as u8 });
            }
            // Lanes a LATER slot of this term reads: a fill here may not touch them.
            let later: BTreeSet<u16> =
                slot_read_lanes[slot + 1..].iter().flatten().copied().collect();
            apply_use(
                layer, prices, plan, step, id, slot as u8, kind, use_, &later, &mut owner,
                &mut held, &mut report,
            )?;

            // Fidelity: after this step, the plan's resident set is exactly what
            // owns lanes. Re-synchronise so a later read of an evicted projection
            // is a stale read.
            let after: BTreeSet<ProjectionId> = action.resident_after.iter().copied().collect();
            let mut owned_lanes = 0u32;
            for p in &after {
                let width = width_of(prices, *p);
                if retired.contains(p) {
                    owned_lanes += width.lanes();
                    continue;
                }
                let Some(&base) = held.get(p) else {
                    return Err(LivenessError::ResidentWithoutLanes { step, projection: *p });
                };
                let w = width.lanes() as u16;
                if (base..base + w).any(|l| owner[l as usize] != Some(*p)) {
                    return Err(LivenessError::ResidentWithoutLanes { step, projection: *p });
                }
                owned_lanes += width.lanes();
            }
            if owned_lanes != action.resident_lanes_after {
                return Err(LivenessError::ResidentLanesMismatch {
                    step,
                    declared: action.resident_lanes_after,
                    owned: owned_lanes,
                });
            }
            report.peak_owned_lanes = report.peak_owned_lanes.max(owned_lanes);
            let evicted: Vec<ProjectionId> =
                held.keys().copied().filter(|p| !after.contains(p)).collect();
            for p in evicted {
                forget(&mut owner, &mut held, prices, p);
            }
            step += 1;
        }
        report.terms += 1;
    }
    if cursor != placement.instrs.len() || step != plan.actions.len() {
        return Err(LivenessError::InstructionCountMismatch {
            expected_terms: plan.order.len(),
            found_terms: term_count,
        });
    }
    Ok(report)
}

/// Drop `victim`'s definition entirely.
///
/// Partial clearing is a trap: an E4 victim spans four lanes, so a one-lane
/// overwrite that only cleared the lane it touched would leave three phantom
/// lanes still claiming the victim and turn every later bounds test on them into
/// a false rejection. Ownership is per VALUE, so it is dropped per value.
fn forget(
    owner: &mut [Option<ProjectionId>],
    held: &mut BTreeMap<ProjectionId, u16>,
    prices: &[SourcePrice],
    victim: ProjectionId,
) {
    let Some(base) = held.remove(&victim) else { return };
    let w = width_of(prices, victim).lanes() as u16;
    for l in base..base + w {
        if owner[l as usize] == Some(victim) {
            owner[l as usize] = None;
        }
    }
}

/// Check and apply one emitted value use against the plan's declared outcomes.
#[allow(clippy::too_many_arguments)]
fn apply_use(
    _layer: &CoeffLayer,
    prices: &[SourcePrice],
    plan: &PagingPlan,
    step: usize,
    term: TermId,
    slot: u8,
    kind: SlotKind,
    use_: &ValueUse,
    later_reads: &BTreeSet<u16>,
    owner: &mut [Option<ProjectionId>],
    held: &mut BTreeMap<ProjectionId, u16>,
    report: &mut LivenessReport,
) -> Result<(), LivenessError> {
    let action = &plan.actions[step];
    let lanes = plan.request.budget.lanes();
    let source = kind.source();
    let e0 = ProjectionId::endpoint0(source);
    let ds = ProjectionId::delta(source);
    let declared = |p: ProjectionId| {
        action.projections.iter().find(|a| a.projection == p).map(|a| a.outcome)
    };
    let bad = LivenessError::IllegalUseForm { step, term, slot };

    // §8's delta resolution is "obtain s0 ... obtain s1 ... ds = s1 - s0 ...
    // optionally retain Endpoint0 ... optionally retain Delta": every READ of one
    // resolution precedes every RETAIN of it. So the match below only CLASSIFIES,
    // and the reads are executed before the writes — otherwise a legal plan that
    // retains `Endpoint0` in the lane a dying resident `Delta` was just read from
    // would be rejected as a stale read.
    let mut pending_reads: Vec<(ProjectionId, u16)> = Vec::new();
    let mut pending_writes: Vec<(ProjectionId, u16)> = Vec::new();

    // A `Cell` read: the intended projection must currently own exactly this range.
    let read = |owner: &[Option<ProjectionId>],
                    report: &mut LivenessReport,
                    p: ProjectionId,
                    lane: u16|
     -> Result<(), LivenessError> {
        let width = width_of(prices, p);
        if u32::from(lane) + width.lanes() > lanes {
            return Err(LivenessError::LaneOutOfBounds { step, lane, lanes });
        }
        if width == ValueWidth::E4 && lane % 4 != 0 {
            return Err(LivenessError::ExtLaneMisaligned { step, lane });
        }
        for l in lane..lane + width.lanes() as u16 {
            if owner[l as usize] != Some(p) {
                return Err(LivenessError::StaleCellRead {
                    step,
                    projection: p,
                    lane: l,
                    found: owner[l as usize],
                });
            }
        }
        report.cell_reads += 1;
        Ok(())
    };

    let write = |owner: &mut [Option<ProjectionId>],
                     held: &mut BTreeMap<ProjectionId, u16>,
                     report: &mut LivenessReport,
                     p: ProjectionId,
                     lane: u16|
     -> Result<(), LivenessError> {
        if declared(p) != Some(ProjectionOutcome::Fill) {
            return Err(LivenessError::IllegalUseForm { step, term, slot });
        }
        let width = width_of(prices, p);
        if u32::from(lane) + width.lanes() > lanes {
            return Err(LivenessError::LaneOutOfBounds { step, lane, lanes });
        }
        if width == ValueWidth::E4 && lane % 4 != 0 {
            return Err(LivenessError::ExtLaneMisaligned { step, lane });
        }
        let after: BTreeSet<ProjectionId> = action.resident_after.iter().copied().collect();
        let mut displaced: BTreeSet<ProjectionId> = BTreeSet::new();
        for l in lane..lane + width.lanes() as u16 {
            if let Some(victim) = owner[l as usize] {
                if victim != p && after.contains(&victim) {
                    return Err(LivenessError::FillClobbersLiveValue {
                        step,
                        projection: p,
                        lane: l,
                        victim,
                    });
                }
                if victim != p && later_reads.contains(&l) {
                    return Err(LivenessError::FillClobbersTermInput {
                        step,
                        projection: p,
                        lane: l,
                        victim,
                    });
                }
                displaced.insert(victim);
            }
            if later_reads.contains(&l) && owner[l as usize] != Some(p) {
                return Err(LivenessError::FillClobbersTermInput {
                    step,
                    projection: p,
                    lane: l,
                    victim: p,
                });
            }
        }
        for victim in displaced {
            forget(owner, held, prices, victim);
        }
        for l in lane..lane + width.lanes() as u16 {
            owner[l as usize] = Some(p);
        }
        held.insert(p, lane);
        report.fills += 1;
        report.lanes_used = report.lanes_used.max(u32::from(lane) + width.lanes());
        Ok(())
    };

    match (kind, use_) {
        // ── Endpoint0-only (§8: never `PlannedSource`) ───────────────────────
        (SlotKind::Endpoint0Only(p), ValueUse::Cell(CellRead::Single { projection, lane })) => {
            if *projection != p || declared(p) != Some(ProjectionOutcome::Hit) {
                return Err(bad);
            }
            pending_reads.push((p, *lane));
        }
        (SlotKind::Endpoint0Only(p), ValueUse::Fill { projection, dst_lane }) => {
            if *projection != p {
                return Err(bad);
            }
            pending_writes.push((p, *dst_lane));
        }
        (SlotKind::Endpoint0Only(p), ValueUse::Direct { source: s }) => {
            if *s != source || declared(p) != Some(ProjectionOutcome::Bypass) {
                return Err(bad);
            }
        }

        // ── Delta-only ───────────────────────────────────────────────────────
        (SlotKind::DeltaOnly(p), ValueUse::Cell(CellRead::Single { projection, lane })) => {
            if *projection != p || declared(p) != Some(ProjectionOutcome::Hit) {
                return Err(bad);
            }
            pending_reads.push((p, *lane));
        }
        (SlotKind::DeltaOnly(p), ValueUse::Fill { projection, dst_lane }) => {
            // Canonical `FillSource`: only when the endpoint is resolved directly,
            // i.e. no resident Endpoint0 to consume.
            if *projection != p || held.contains_key(&e0) {
                return Err(bad);
            }
            pending_writes.push((p, *dst_lane));
        }
        (SlotKind::DeltaOnly(p), ValueUse::Direct { source: s }) => {
            if *s != source
                || held.contains_key(&e0)
                || declared(p) != Some(ProjectionOutcome::Bypass)
            {
                return Err(bad);
            }
        }
        (SlotKind::DeltaOnly(p), ValueUse::PlannedDelta { source: s, endpoint0, delta }) => {
            if *s != source || p != ds {
                return Err(bad);
            }
            if *endpoint0 == PlanAction::Invalid || *delta == PlanAction::Invalid {
                return Err(LivenessError::InvalidPlanAction { step, term, slot });
            }
            // A plan must not be the canonical short form.
            if *endpoint0 == PlanAction::Direct && *delta == PlanAction::Direct {
                return Err(bad);
            }
            if *endpoint0 == PlanAction::Direct && matches!(delta, PlanAction::Fill { .. }) {
                return Err(bad);
            }
            match endpoint0 {
                PlanAction::UseResident { lane } => pending_reads.push((e0, *lane)),
                PlanAction::Fill { lane } => pending_writes.push((e0, *lane)),
                PlanAction::Direct => {
                    if held.contains_key(&e0) {
                        return Err(bad);
                    }
                }
                PlanAction::Invalid => unreachable!("rejected above"),
            }
            match delta {
                PlanAction::UseResident { .. } => return Err(bad),
                PlanAction::Fill { lane } => pending_writes.push((ds, *lane)),
                PlanAction::Direct => {
                    if declared(ds) != Some(ProjectionOutcome::Bypass) {
                        return Err(bad);
                    }
                }
                PlanAction::Invalid => unreachable!("rejected above"),
            }
        }

        // ── Native dual factor (§9.5) ────────────────────────────────────────
        (
            SlotKind::DualFactor(s),
            ValueUse::Cell(CellRead::Pair { source: cs, endpoint0_lane, delta_lane }),
        ) => {
            if *cs != s
                || declared(e0) != Some(ProjectionOutcome::Hit)
                || declared(ds) != Some(ProjectionOutcome::Hit)
            {
                return Err(bad);
            }
            pending_reads.push((e0, *endpoint0_lane));
            pending_reads.push((ds, *delta_lane));
        }
        (SlotKind::DualFactor(_), ValueUse::Direct { source: s }) => {
            if *s != source
                || declared(e0) != Some(ProjectionOutcome::Bypass)
                || declared(ds) != Some(ProjectionOutcome::Bypass)
            {
                return Err(bad);
            }
        }
        (SlotKind::DualFactor(_), ValueUse::PlannedDelta { source: s, endpoint0, delta }) => {
            if *s != source {
                return Err(bad);
            }
            if *endpoint0 == PlanAction::Invalid || *delta == PlanAction::Invalid {
                return Err(LivenessError::InvalidPlanAction { step, term, slot });
            }
            // Both resident is the packed `Cell` form; both direct is `DirectSource`.
            if matches!(endpoint0, PlanAction::UseResident { .. })
                && matches!(delta, PlanAction::UseResident { .. })
            {
                return Err(bad);
            }
            if *endpoint0 == PlanAction::Direct && *delta == PlanAction::Direct {
                return Err(bad);
            }
            for (p, act) in [(e0, endpoint0), (ds, delta)] {
                match act {
                    PlanAction::UseResident { lane } => {
                        if declared(p) != Some(ProjectionOutcome::Hit) {
                            return Err(bad);
                        }
                        pending_reads.push((p, *lane));
                    }
                    PlanAction::Fill { lane } => pending_writes.push((p, *lane)),
                    PlanAction::Direct => {
                        if declared(p) != Some(ProjectionOutcome::Bypass) {
                            return Err(bad);
                        }
                    }
                    PlanAction::Invalid => unreachable!("rejected above"),
                }
            }
        }

        _ => return Err(bad),
    }

    // Reads first, then retains — §8's resolution order.
    for (p, lane) in pending_reads {
        read(owner, report, p, lane)?;
    }
    for (p, lane) in pending_writes {
        write(owner, held, report, p, lane)?;
    }
    Ok(())
}
