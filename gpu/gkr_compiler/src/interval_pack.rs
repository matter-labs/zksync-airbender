//! Offline interval packing over a four-lane-aligned cell file, generic over a
//! stable value id.
//!
//! This is the algorithm the forward Stage-3 allocator has always used
//! ([`crate::forward::compile`]'s `place`), lifted out of that module verbatim so the
//! backward coefficient-term scheduler can reuse it. The forward path keeps its
//! own `PlacementInput` adapter, its own live-range derivation, and its own error
//! type; only the width-aware packing core moved here. Nothing in this module knows
//! about instructions, residency plans, `ExprId`, or `ProjectionId`.
//!
//! # The model
//!
//! A cell file of `lanes` BF-lane-equivalents. Every value is either
//! [`PackWidth::Single`] (one lane, unaligned) or [`PackWidth::Quad`] (four
//! consecutive lanes, four-lane-aligned). Every value's `[def, last_use]`
//! interval is known up front, so this is a pure offline packing problem — no
//! eviction, no relocation, no cyclical recompute dependency.
//!
//!   1. **Quad phase.** Quads are the constrained resource. Assign each quad
//!      value, in `(def, id)` order, the lowest four-lane-aligned group holding no
//!      time-overlapping quad value — optimal interval partitioning at quad
//!      granularity. Each value's group is then fixed for its whole lifetime.
//!   2. **Single phase.** The quad groups are now immovable reservations. A single
//!      value is width-1 with no alignment constraint, so it drops into the lowest
//!      lane that is free across its interval — i.e. not inside an overlapping
//!      quad value's group and not sharing a lane with a time-overlapping single.
//!      Any residual lane-time hole works.
//!
//! Because a single is never assigned a lane a quad value will occupy, **a quad
//! value never has to evict a single**: the assignment is relocation-free by
//! construction.
//!
//! Feasibility: if some value finds no legal lane the instance does not fit at
//! this `lanes` budget and [`assign_lanes`] returns a [`PackFailure`] carrying the
//! floor the caller should report.

use std::collections::HashMap;
use std::hash::Hash;

/// Lanes one four-lane-aligned group holds.
pub const QUAD_LANES: usize = 4;

/// Backtracking-search node cap. The greedy fast path handles every layer in the
/// committed corpus, so the search runs only when greedy strands a single-lane
/// value at a budget the instance actually fits (peak demand <= lanes — checked up
/// front). The cap bounds worst-case blowup on a pathological feasible instance,
/// falling back to [`PackFailure::NoFeasibleColoring`] (never worse than greedy
/// alone). Small enough to stay sub-second, large enough that no realistic layer —
/// and no fuzzed small instance — reaches it.
pub const QUAD_SEARCH_NODE_CAP: u64 = 200_000;

/// Inclusive `[def, last_use]` live interval over a flat step index space.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Interval {
    pub def: usize,
    pub last_use: usize,
}

impl Interval {
    /// Inclusive-interval overlap. Two values conflict for a lane iff their
    /// intervals overlap.
    pub fn overlaps(&self, other: &Interval) -> bool {
        self.def <= other.last_use && other.def <= self.last_use
    }
}

/// The two widths the cell file supports: one lane, or one four-lane-aligned
/// group.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PackWidth {
    Single,
    Quad,
}

impl PackWidth {
    pub fn lanes(self) -> usize {
        match self {
            PackWidth::Single => 1,
            PackWidth::Quad => QUAD_LANES,
        }
    }
}

/// Why an instance did not pack. Each variant carries enough to reconstruct the
/// floor the caller reports; [`PackFailure::floor`] does that reconstruction so
/// two callers cannot spell the same floor differently.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackFailure {
    /// The width-weighted live demand exceeds `lanes` at some instant, so no
    /// placement of any kind can fit.
    PeakExceedsBudget { peak: usize },
    /// The concurrent quad-value count alone exceeds the quad budget.
    QuadDemandExceedsBudget { quads_needed: usize },
    /// Every quad coloring the search reached strands a single-lane value, or the
    /// node cap was hit.
    NoFeasibleColoring,
}

impl PackFailure {
    /// The lane floor to report for this failure at this budget.
    pub fn floor(self, lanes: usize) -> usize {
        match self {
            PackFailure::PeakExceedsBudget { peak } => peak,
            PackFailure::QuadDemandExceedsBudget { quads_needed } => quads_needed * QUAD_LANES,
            PackFailure::NoFeasibleColoring => lanes + 1,
        }
    }
}

/// Peak width-weighted live demand over the interval set: the largest total lane
/// count any single instant needs. A necessary feasibility condition — an
/// instance with `peak > lanes` cannot be placed by any algorithm, with or
/// without moves.
pub fn peak_weighted_demand<V, W>(ranges: &HashMap<V, Interval>, width_of: W) -> usize
where
    V: Copy + Eq + Hash,
    W: Fn(V) -> PackWidth,
{
    let Some(max_last) = ranges.values().map(|r| r.last_use).max() else {
        return 0;
    };
    let mut delta = vec![0i64; max_last + 2];
    for (&v, r) in ranges {
        let w = width_of(v).lanes() as i64;
        delta[r.def] += w;
        delta[r.last_use + 1] -= w;
    }
    let (mut cur, mut peak) = (0i64, 0i64);
    for d in delta {
        cur += d;
        peak = peak.max(cur);
    }
    peak as usize
}

/// Greedy quad coloring: assign each quad value (in the given order) the lowest
/// group holding no time-overlapping quad value. This is optimal interval
/// partitioning — it uses exactly the peak concurrent quad-value count of groups —
/// so it succeeds iff the quad demand fits at all. Returns the per-value base lane
/// plus the per-group assigned intervals, or `None` when the quad demand alone
/// exceeds the budget (genuinely infeasible; no coloring can help).
fn greedy_color_quads<V>(
    quad_values: &[V],
    ranges: &HashMap<V, Interval>,
    n_quads: usize,
) -> Option<(HashMap<V, u16>, Vec<Vec<Interval>>)>
where
    V: Copy + Eq + Hash,
{
    let mut lanes: HashMap<V, u16> = HashMap::new();
    let mut quads: Vec<Vec<Interval>> = vec![Vec::new(); n_quads];
    for &e in quad_values {
        let r = ranges[&e];
        let q = (0..n_quads).find(|&q| quads[q].iter().all(|o| !r.overlaps(o)))?;
        quads[q].push(r);
        lanes.insert(e, (q * QUAD_LANES) as u16);
    }
    Some((lanes, quads))
}

/// Pack single-lane values into the residual lane-time left by a fixed quad
/// coloring: each single (in the given order) takes the lowest lane that is (a)
/// not inside a group whose assigned quad value overlaps its interval, and (b) not
/// shared with a time-overlapping single. Lanes past the last full group
/// (`lanes % 4`) are quad-free. Returns the per-single lane map, or `None` if any
/// single finds no legal lane under this coloring. Never mutates shared state, so
/// a caller can try it against several colorings.
fn pack_singles<V>(
    singles: &[V],
    ranges: &HashMap<V, Interval>,
    quads: &[Vec<Interval>],
    n_quads: usize,
    lanes: usize,
) -> Option<HashMap<V, u16>>
where
    V: Copy + Eq + Hash,
{
    let mut single_lanes: HashMap<V, u16> = HashMap::new();
    let mut lane_singles: Vec<Vec<Interval>> = vec![Vec::new(); lanes];
    for &b in singles {
        let r = ranges[&b];
        let c = (0..lanes).find(|&c| {
            let q = c / QUAD_LANES;
            let quad_ok = q >= n_quads || quads[q].iter().all(|o| !r.overlaps(o));
            quad_ok && lane_singles[c].iter().all(|o| !r.overlaps(o))
        })?;
        lane_singles[c].push(r);
        single_lanes.insert(b, c as u16);
    }
    Some(single_lanes)
}

/// Backtracking quad coloring: assign `quad_values[i..]` to groups (best-fit
/// exploration order — concentrate quad values onto already-busy groups so others
/// stay quad-free for longer), and at the leaf pack the singles. Returns the first
/// coloring under which every single seats. Because greedy quad coloring is
/// single-blind, a single-feasible coloring can differ from the lowest-fit one;
/// the search explores alternatives that greedy would never try. Fills `out` with
/// the winning assignment. `nodes` bounds the search.
#[allow(clippy::too_many_arguments)]
fn search_quad_coloring<V>(
    i: usize,
    quad_values: &[V],
    singles: &[V],
    ranges: &HashMap<V, Interval>,
    n_quads: usize,
    lanes: usize,
    quads: &mut Vec<Vec<Interval>>,
    out: &mut HashMap<V, u16>,
    nodes: &mut u64,
) -> bool
where
    V: Copy + Eq + Hash,
{
    if *nodes == 0 {
        return false;
    }
    *nodes -= 1;
    if i == quad_values.len() {
        return match pack_singles(singles, ranges, quads, n_quads, lanes) {
            Some(single_lanes) => {
                out.extend(single_lanes);
                true
            }
            None => false,
        };
    }
    let e = quad_values[i];
    let r = ranges[&e];
    // Eligible groups (no time-overlapping quad value), explored best-fit: groups
    // already busy latest first (concentrate quad values, free other groups for
    // singles), lowest index to break ties and for a deterministic order.
    // Exploration order is a performance heuristic — completeness comes from trying
    // every eligible group on backtrack.
    let mut cand: Vec<usize> = (0..n_quads)
        .filter(|&q| quads[q].iter().all(|o| !r.overlaps(o)))
        .collect();
    cand.sort_by_key(|&q| {
        (
            std::cmp::Reverse(quads[q].iter().map(|o| o.last_use).max()),
            q,
        )
    });
    for q in cand {
        quads[q].push(r);
        out.insert(e, (q * QUAD_LANES) as u16);
        if search_quad_coloring(
            i + 1,
            quad_values,
            singles,
            ranges,
            n_quads,
            lanes,
            quads,
            out,
            nodes,
        ) {
            return true;
        }
        quads[q].pop();
        out.remove(&e);
    }
    false
}

/// Assign a fixed lane to every value: a four-lane-aligned group per
/// [`PackWidth::Quad`] value, a single lane per [`PackWidth::Single`] value, such
/// that no two time-overlapping values share any lane and no single ever lands in
/// a live quad value's group (=> relocation-free).
///
/// Fast path is greedy lowest-fit; if greedy strands a single — a single-blind
/// quad coloring can — fall back to a backtracking search over quad colorings.
/// Fails only when the peak width-weighted demand overflows, when the quad demand
/// alone overflows, or when no coloring seats the singles within the node cap.
pub fn assign_lanes<V, W>(
    ranges: &HashMap<V, Interval>,
    width_of: W,
    lanes: usize,
) -> Result<HashMap<V, u16>, PackFailure>
where
    V: Copy + Eq + Hash + Ord,
    W: Fn(V) -> PackWidth,
{
    let n_quads = lanes / QUAD_LANES;

    // Necessary feasibility condition, checked FIRST. Failing this means no
    // placement can fit, so return immediately — critically, this keeps a genuinely
    // oversubscribed input from ever reaching the backtracking search and grinding
    // to the node cap.
    let peak = peak_weighted_demand(ranges, &width_of);
    if peak > lanes {
        return Err(PackFailure::PeakExceedsBudget { peak });
    }

    // Partition by width; pack each class in deterministic `(def, id)` order so the
    // assignment is a pure function of the input.
    let mut quad_values: Vec<V> = Vec::new();
    let mut singles: Vec<V> = Vec::new();
    for &v in ranges.keys() {
        match width_of(v) {
            PackWidth::Quad => quad_values.push(v),
            PackWidth::Single => singles.push(v),
        }
    }
    let sort_key = |v: &V| (ranges[v].def, *v);
    quad_values.sort_by_key(sort_key);
    singles.sort_by_key(sort_key);

    // Greedy quad coloring. Failure here means the peak concurrent quad-value count
    // exceeds the group budget — genuinely infeasible, no coloring recovers it.
    let (mut out, quads) = greedy_color_quads(&quad_values, ranges, n_quads).ok_or(
        PackFailure::QuadDemandExceedsBudget {
            quads_needed: n_quads + 1,
        },
    )?;

    // Fast path: greedy lowest-fit single packing on the greedy coloring.
    if let Some(single_lanes) = pack_singles(&singles, ranges, &quads, n_quads, lanes) {
        out.extend(single_lanes);
        return Ok(out);
    }

    // A single stranded under the greedy coloring. Because the quad coloring is
    // single-blind, a different (still <= n_quads) coloring may seat every single —
    // search for one.
    let mut search_out: HashMap<V, u16> = HashMap::new();
    let mut search_quads: Vec<Vec<Interval>> = vec![Vec::new(); n_quads];
    let mut nodes = QUAD_SEARCH_NODE_CAP;
    if search_quad_coloring(
        0,
        &quad_values,
        &singles,
        ranges,
        n_quads,
        lanes,
        &mut search_quads,
        &mut search_out,
        &mut nodes,
    ) {
        return Ok(search_out);
    }
    Err(PackFailure::NoFeasibleColoring)
}
