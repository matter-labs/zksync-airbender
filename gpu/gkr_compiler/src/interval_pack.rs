//! Offline packing of one-lane and four-lane-aligned values over known live
//! intervals. Quad values are colored first; single-lane values fill the
//! remaining lane-time holes, so quad values never evict singles. [`assign_lanes`]
//! reports a floor when packing is infeasible.

use std::collections::HashMap;
use std::hash::Hash;

pub(crate) const QUAD_LANES: usize = 4;

/// Bounds fallback search when greedy quad coloring strands a single-lane value.
pub(crate) const QUAD_SEARCH_NODE_CAP: u64 = 200_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Interval {
    pub def: usize,
    pub last_use: usize,
}

impl Interval {
    pub(crate) fn overlaps(&self, other: &Interval) -> bool {
        self.def <= other.last_use && other.def <= self.last_use
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum PackWidth {
    Single,
    Quad,
}

impl PackWidth {
    pub(crate) fn lanes(self) -> usize {
        match self {
            PackWidth::Single => 1,
            PackWidth::Quad => QUAD_LANES,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PackFailure {
    PeakExceedsBudget { peak: usize },
    QuadDemandExceedsBudget { quads_needed: usize },
    NoFeasibleColoring,
}

impl PackFailure {
    pub(crate) fn floor(self, lanes: usize) -> usize {
        match self {
            PackFailure::PeakExceedsBudget { peak } => peak,
            PackFailure::QuadDemandExceedsBudget { quads_needed } => quads_needed * QUAD_LANES,
            PackFailure::NoFeasibleColoring => lanes + 1,
        }
    }
}

/// Maximum simultaneous lane demand.
pub(crate) fn peak_weighted_demand<V, W>(ranges: &HashMap<V, Interval>, width_of: W) -> usize
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

type QuadColoring<V> = (HashMap<V, u16>, Vec<Vec<Interval>>);

/// Lowest-fit interval coloring for four-lane values.
fn greedy_color_quads<V>(
    quad_values: &[V],
    ranges: &HashMap<V, Interval>,
    n_quads: usize,
) -> Option<QuadColoring<V>>
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

/// Lowest-fit packing into the lane-time holes left by a quad coloring.
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

/// Backtracks quad colorings when the greedy coloring strands a single.
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

/// Assigns fixed, non-overlapping lanes, falling back to bounded search when the
/// greedy quad coloring leaves no lane for a single.
pub(crate) fn assign_lanes<V, W>(
    ranges: &HashMap<V, Interval>,
    width_of: W,
    lanes: usize,
) -> Result<HashMap<V, u16>, PackFailure>
where
    V: Copy + Eq + Hash + Ord,
    W: Fn(V) -> PackWidth,
{
    let n_quads = lanes / QUAD_LANES;

    // Reject oversubscription before entering the bounded search.
    let peak = peak_weighted_demand(ranges, &width_of);
    if peak > lanes {
        return Err(PackFailure::PeakExceedsBudget { peak });
    }

    // Deterministic `(def, id)` order makes the assignment reproducible.
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

    let (mut out, quads) = greedy_color_quads(&quad_values, ranges, n_quads).ok_or(
        PackFailure::QuadDemandExceedsBudget {
            quads_needed: n_quads + 1,
        },
    )?;

    if let Some(single_lanes) = pack_singles(&singles, ranges, &quads, n_quads, lanes) {
        out.extend(single_lanes);
        return Ok(out);
    }

    // The quad coloring is single-blind, so try alternatives before failing.
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
